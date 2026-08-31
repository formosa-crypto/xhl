(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp           Require finmap.
From xhl.pwhile         Require Import notations inhabited pwhile psemantic range.
From xhl.ehl            Require Import ehl_stmt.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope sem_scope.

Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

(* -------------------------------------------------------------------- *)

Section ehl.
Context {X Y : eqType} {mem : memType X}.

Notation cond := (@cond _ mem).
Notation cond2 := (@cond2 _ mem).

Notation phi := (@Phi.type X Y mem).
Notation psi := (@psi _ Y mem).

Implicit Types  (f g h : cond).

Section Logic.

Context (ps: psi).

Inductive derivable : phi -> cond -> cmd -> cond -> Prop :=
  | H_Abort : forall f g cl,
      (forall m, (0 <= f m)%E) ->
      derivable cl f abort g
  | H_Skip : forall f cl,
      derivable cl f skip f
  | H_Asgn : forall {T : IhbType.type} x (e : expr_ X mem T) f cl,
      derivable cl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f
  | H_GAsgn : forall {T : IhbType.type} x (e : expr_ X mem T) f cl,
      derivable cl (fun m => f (m.{x <- `[{e}] m})) (G x <<- e) f
  | H_Random : forall {T : IhbType.type} x (d:expr_ X mem (Distr T)) f cl,
    let g m :=
      espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f
    in
    derivable cl g (x <$- d) f
  | H_Block : forall f g bs c rs cl,
      (forall m, (0 <= g m)%E) ->
      (forall m, derivable cl (bound (fun _ => f m) (minit m bs)) c
                              (fun m'' => g (mret m m'' rs))) ->
      derivable cl f (block bs c rs) g
  | H_If : forall f g (e:expr_ X mem bool) (c1 c2:cmd) cl,
      derivable cl (lift (esem e) f) c1 g ->
      derivable cl (lift (fun m => negb (esem e m)) f) c2 g ->
      derivable cl f (If e then c1 else c2)%S g
  | H_While : forall f (e:expr_ X mem bool) (c:cmd) cl,
      (forall m, 0 <= f m)%E ->
      derivable cl (lift (esem e) f) c f ->
      derivable cl f (While e Do c) (lift (fun m => negb (esem e m)) f)
  | H_Seq : forall f c d g h cl,
      (forall m, (0 <= g m)%E) ->
      derivable cl h d g -> derivable cl f c h -> derivable cl f (c;;d) g
  | H_Consequence : forall f' g' f g (c : cmd) cl,
      derivable cl f' c g' ->
      (forall m mu,  espe mu g' <= f' m -> espe mu g <= f m)%E ->
      derivable cl f c g
  | H_khl : forall P Q c cl,
     derivable2 cl P c (fun _ _ => Q) -> derivable cl P c Q
  with derivable2 : phi -> cond -> cmd -> cond2 -> Prop :=
  | H_hl: forall P Q c cl,
      (forall m mu m', (0 <= Q m mu m')%E) ->
      cond2_mono Q ->
       (forall s0, derivable cl (bound P s0) c (fun s => Q s0 ((ssem_ ps c s0 s)%:E) s)) ->
       derivable2 cl P c Q
   | H_call : forall cl (f:Y),
       derivable2 cl (get_pre (cl f)) (call f) (get_post (cl f))
   | H_rec : forall P Q c cl cl',
       (forall p', derivable2 cl (get_pre (cl p')) (ps p') (get_post (cl p'))) ->
       derivable2 cl P c Q ->
       derivable2 cl' P c Q
   | H_adapt : forall (P1 P2 : cond) (Q1 Q2 : cond2) c cl,
       derivable2 cl P2 c Q2 ->
       (forall m mu,  espe mu (fun m' => Q2 m ((mu m')%:E) m') <= P2 m ->
                 espe mu (fun m' => Q1 m ((mu m')%:E) m') <= P1 m)%E ->
       derivable2 cl P1 c Q1.

Scheme derivable_min := Minimality for derivable Sort Prop
    with derivable2_min := Minimality for derivable2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

End Logic.

Section Sound.

Context (ps: psi).

Section Rules.
Definition aehl (l : (Y * mem) -> {distr mem / R})
    (f : cond) (c : cmd) (g : cond) :=
  forall m : mem, (espe (ssem_aux l c m) g <= f m)%E.

Definition akehl (l : Y * mem -> {distr mem/R})
  (f : cond) (c : cmd) (g : cond2) :=
  forall m : mem, (espe (ssem_aux l c m) (fun m' => g m ((ssem_aux l c m m')%:E) m') <= f m)%E.

Lemma aehl_skip l f g :
  (forall m, (g m <= f m)%E) -> aehl l f skip g.
Proof. by move => h m /=; rewrite eexp_dunit. Qed.

Lemma aehl_abort l f g :
  (forall m, (0 <= f m)%E) -> aehl l f abort g.
Proof.
move => h m /=.
rewrite /espe (eq_esum _ _ (fun _ => 0%E)).
- by move => x; rewrite dnullE mule0.
- by rewrite esum0.
Qed.

Lemma aehl_assgn l {T : IhbType.type} f x (e : expr_ X mem T) :
  aehl l (fun m => f m.[x <- `[{e}] m]) (x <<- e) f.
Proof. by move => m /=; rewrite eexp_dunit. Qed.

Lemma aehl_gassign l {T : IhbType.type} f x (e : expr_ X mem T) :
  aehl l (fun m => f (m.{x <- `[{e}] m})) (G x <<- e) f.
Proof. by move => m /=; rewrite eexp_dunit. Qed.

Lemma aehl_block l f g bs c rs :
  (forall m, (0 <= g m)%E) ->
  (forall m, aehl l (bound (fun _ => f m) (minit m bs)) c
                    (fun m'' => g (mret m m'' rs))) ->
  aehl l f (block bs c rs) g.
Proof.
move=> Hg H m /=; rewrite espe_dlet_ret //.
by have := H m (minit m bs); rewrite /bound eqxx.
Qed.

Lemma aehl_rnd l {T : IhbType.type} f x (d : expr_ X mem (Distr T)) :
  let g m := espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f in
  aehl l g (x <$- d) f.
Proof. by move => g m /=. Qed.

Lemma aehl_seq l f g h c1 c2:
  (forall m, (0 <= g m)%E) ->
  aehl l f c1 h -> aehl l h c2 g -> aehl l f (c1 ;; c2) g.
Proof.
move => Hg h1 h2 m /=.
rewrite eexp_dlet //.
apply: (@le_trans _ _ (espe (ssem_aux l c1 m) h)); last exact: h1.
rewrite /espe; apply: le_esum  => x ?; apply: lee_wpmul2r.
+ by apply: lee_tofin; apply: ge0_mu.
+ exact: h2.
Qed.

Lemma aehl_if l f (e : expr_ X mem bool) c1 c2 g :
  aehl l (lift (esem e) f) c1 g ->
  aehl l (lift (fun m => negb (esem e m)) f) c2 g ->
  aehl l f (If e then c1 else c2) g.
Proof.
move => Hc1 Hc2 m /=.
case h: (`[{e}] m).
- by move : (Hc1 m); rewrite /lift h /=.
- by move : (Hc2 m); rewrite /lift h /=.
Qed.

Lemma aehl_conseq l c f g f' g':
  aehl l f' c g' ->
  (forall m d,  espe d g' <= f' m -> espe d g <= f m)%E ->
  aehl l f c g.
Proof. by move => h' hc m; apply hc. Qed.

Lemma ssem_aux_whileE l (e : expr_ X mem bool) c m :
  ssem_aux l (While e Do c) m = \dlim_(n) ssem_aux l (@whilen X Y mem e c n) m.
Proof.
rewrite /=; apply: eq_dlim => n0; move: m; elim: n0 => [|n0 IHn0] s //=.
case: (`[{e}] s) => //=.
by apply: eq_in_dlet => [s' _|//]; rewrite IHn0.
Qed.

Lemma aehl_while l (e : expr_ X mem bool) c f :
  (forall m, 0 <= f m)%E ->
  aehl l (lift (esem e) f) c f ->
  aehl l f (While e Do c) (lift (fun m => negb (esem e m)) f).
Proof.
move => Hf.
have Hpos : forall m : mem, (0%R <= (if ~~ `[{e}] m then f m else +oo))%E.
+ move => m; case (`[{e}] m) => //=. exact: le0y.
rewrite /lift => Hi m.
rewrite ssem_aux_whileE /espe.
apply: (esum_dlim_r (dhomo_dnd (hmono_whilen l e c m)) Hpos) => n.
move : m.
elim : n.
+ by apply aehl_abort.
+ move => n Hi'.
  apply aehl_if => //=.
  + by apply: (aehl_seq _ _ _ f).
  + by apply aehl_skip.
Qed.

Lemma akehl_aehl l P c Q :
  akehl l P c Q <-> (forall s0, aehl l (bound P s0) c (fun s => Q s0 ((ssem_aux l c s0 s)%:E) s)).
Proof.
rewrite /bound; split.
+ move=> h m0 m.
  case: ifP.
  - by move => /eqP <-.
  - move => _. exact : leey.
+ move => h m.
  have // := (h m m).
  by rewrite eq_refl.
Qed.

Lemma aehl_akehl l P c Q : akehl l P c (fun _ _ => Q) <-> aehl l P c Q.
Proof. by split; move => h m; apply h. Qed.


Definition valid_cl_n n cl :=
  forall  (f:Y), akehl (ubnf ps n) (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma cl_calls (cl: phi):
  (forall (f : Y) (n : nat), valid_cl_n n cl ->
        akehl (ubnf ps n) (get_pre (cl f)) (ps f) (get_post (cl f))) ->
  (forall (f : Y) (n : nat),
      akehl (ubnf ps n) (get_pre (cl f)) (call f) (get_post (cl f))).
Proof.
move => IH_body f n.
elim: n f => [|k IHk] f m.
+ rewrite /espe //=.
  under eq_esum do rewrite dnullE  mule0.
  rewrite esum0.
  exact: pre_pos.
apply: (IH_body f k _ m).
by move=> g; apply: IHk => //.
Qed.

End Rules.

Lemma soundness_n :
  (forall (cl: phi) P c Q, derivable ps cl P c Q ->
     forall n, valid_cl_n n cl -> aehl (ubnf ps n) P c Q) /\
    (forall (cl: phi) P c Q, derivable2 ps cl P c Q ->
     forall n, valid_cl_n n cl -> akehl (ubnf ps n) P c Q).
Proof.
apply: derivable_mut.
- (* H_Abort *) by move=> *; exact: aehl_abort.
- (* H_Skip *) by move=> *; exact: aehl_skip.
- (* H_Asgn *) by move=> *; exact: aehl_assgn.
- (* H_GAsgn *) by move=> *; exact: aehl_gassign.
- (* H_Random *) by move=> *; exact: aehl_rnd.
- (* H_Block *)
  move=> f g bs c rs cl Hg _ IH n Hv.
  by apply: aehl_block; [exact: Hg | move=> m; exact: IH].
- (* H_If *)
  move => f g e c1 c2 cl ? IH1 ? IH2 n Hv.
  by apply: aehl_if;[exact: IH1 | exact: IH2].
- (* H_While *)
  move => f e c cl m ? IH n Hv; apply: aehl_while => //;  exact: IH.
- (* H_Seq *)
  move=> f c d g h cl Hg ? IHd ? IHc n Hv.
  by apply: (aehl_seq _ _ _ _ _ _ Hg (IHc n Hv) (IHd n Hv)).
- (* H_Consequence *)
  move => f' g' f g c cl ? HI H n Hv.
  apply: aehl_conseq. apply: HI => //. apply H.
- (* H_khl *)
  move => P Q c cl ? IH n Hv; rewrite -aehl_akehl; exact: IH.
- (* H_hl *)
  move=> P Q c cl Hpos Hmono ? IH n Hv. rewrite akehl_aehl=> s0.
  move => m.
  move :(IH s0 n Hv m).
  apply: le_trans.
  rewrite /espe.
  apply le_esum => x ?.
  apply: lee_pmul => //=.
  + by rewrite lee_tofin.
  + unfold cond2_mono in Hmono.
    apply: Hmono.
    rewrite ssem_dlim_ubnf.
    apply: dlim_ub => ????.
    apply mono_ssem_aux.
    by apply homo_ubnf.
- (* H_call *) by move=> cl f n Hv; exact: Hv.
- (* H_rec *)
  move=> P Q c cl cl' _ IH_body _ IH_c n Hv; apply: (IH_c n).
  by move=> f; apply: cl_calls.
- (* H_adapt *)
  move=> P1 P2 Q1 Q2 c cl ? HI H n Hv m.
  exact :(H m (ssem_aux (ubnf ps n) c m) (HI n Hv m)).
Qed.

Definition valid_cl cl :=
  forall (f: Y), kehl_ ps (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma valid_cl_to_n (cl: phi) :
  valid_cl cl -> forall n, valid_cl_n n cl.
Proof.
move=> Hv n f m; move: (Hv f m).
rewrite ssem_callE; apply: le_trans; rewrite /espe; apply: le_esum.
move => x ?; rewrite lee_pmul //= ?lee_tofin //.
+ exact: post_pos.
+ apply: (post_mono f).
  apply: dlim_ub => ????.  exact: homo_ubnf.
+ apply: dlim_ub => ????.  exact: homo_ubnf.
Qed.

Theorem hoare_sound (cl:phi) P c Q :
  (forall m, (0 <= P m)%E) ->
  (forall m, (0 <= Q m)%E) ->
  valid_cl cl -> derivable ps cl P c Q -> ehl_ ps P c Q.
Proof.
move => HP HQ Hv Hd m.
rewrite /espe ssem_dlim_ubnf.
apply: esum_dlim_r => //.
+ move => ????.
  apply mono_ssem_aux.
  by apply homo_ubnf.
move => n.
have Hvn : valid_cl_n n cl := @valid_cl_to_n cl Hv n.
have Hahl := (proj1 soundness_n  _ _ _ _ Hd n Hvn).
exact: (Hahl m).
Qed.

Corollary hoare_sound0 P c Q :
  (forall m, (0 <= P m)%E) ->
  (forall m, (0 <= Q m)%E) ->
  derivable ps cl_empty P c Q -> ehl_ ps P c Q.
Proof.
move => HP HQ HD; apply: (hoare_sound cl_empty) => //.
rewrite /valid_cl /kehl_ => //= *.
rewrite /empty_precondition.
exact: leey.
Qed.

Theorem khoare_sound (cl:phi) P c (Q: mem -> mem -> \bar R) :
  (forall m, (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  valid_cl cl -> derivable2 ps cl P c (fun s0 _ s =>Q s0 s) -> kehl_ ps P c (fun s0 _ s =>Q s0 s).
Proof.
move => HP HQ Hv Hd m.
rewrite /espe ssem_dlim_ubnf.
apply: esum_dlim_r => //.
+ move => ????.
   apply mono_ssem_aux.
   by apply homo_ubnf.
move => n.
have Hvn : valid_cl_n n cl := @valid_cl_to_n cl Hv n.
have Hahl := (proj2 soundness_n  _ _ _ _ Hd n Hvn).
move : (Hahl m).
apply: le_trans.
rewrite /espe.
by apply le_esum.
Qed.

Corollary khoare_sound0 P c (Q: mem -> mem -> \bar R) :
  (forall m,  (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  derivable2 ps cl_empty P c (fun s0 _ s =>Q s0 s) -> kehl_ ps P c (fun s0 _ s =>Q s0 s).
Proof.
move => HP HQ HD.
apply: (khoare_sound cl_empty) => //.
rewrite /valid_cl /kehl_ => //=.
move => *.
rewrite /empty_precondition.
exact: leey.
Qed.

End Sound.

Section Complete.
Context (ps: psi).

(* Most-general procedure contract *)
Definition cl_mgt : Y -> clause :=
  fun (f:Y) => ((fun _ => 0)%E,
                  (fun s0 r s =>
                     if (r <= ((ssem_ ps (ps f) s0) s)%:E)%E then 0%E else +oo%E)
                ).

Lemma post_mono_cl_mgt : cl_post_mono cl_mgt.
Proof.
move => f r r' H x x'.
rewrite /cl_mgt //=.
case_eq  ( r <= (ssem_ ps (ps f) x x')%:E)%E.
+ case  (r' <= (ssem_ ps (ps f) x x')%:E)%E => //=.
  move => _. exact: le0y.
+ case_eq (r' <= (ssem_ ps (ps f) x x')%:E)%E => //=.
move =>  H1  H2.
have : (r <= (ssem_ ps (ps f) x x')%:E)%E = true.
+ by apply: (le_trans H ).
by rewrite H2.
Qed.

Lemma pre_pos_cl_mgt : cl_pre_pos cl_mgt.
Proof. by []. Qed.

Lemma post_pos_cl_mgt : cl_post_pos cl_mgt.
Proof.
  move => f x r x' //=.
  case: (r <= EFin (ssem_ ps (ps f) x x'))%E => //=.
  exact : le0y.
Qed.

HB.instance Definition _ :=
  isPhi.Build X Y mem cl_mgt  post_mono_cl_mgt  pre_pos_cl_mgt post_pos_cl_mgt.

Lemma cl_mgt_pos (mu: {distr mem/R}) m0 (f: Y):
  forall s,(0 <= (if (EFin (mu s) <= EFin ((ssem_ ps (ps f) m0) s))%E
            then 0%E else +oo%E) * (mu s)%:E)%E.
Proof.
move => s;apply: mule_ge0.
+ by case: ifP => _; [exact: lexx | exact: leey].
exact: (lee_tofin (ge0_mu _ s)).
Qed.

Lemma rel_complete_d (c : cmd) (f g : cond) :
  (forall m,  (0 <= f m)%E) ->
  (forall m , (0 <= g m)%E) ->
  ehl_ ps f c g -> derivable ps cl_mgt f c g.
Proof.
elim: c f g => [ | | T x e | T gx ge | T x d | bs cb ihb rs
               | e c1 ih1 c2 ih2 | e c0 ih0 | c1 ih1 c2 ih2 | f ] P Q Hf Hg Hhl.
- (* abort *) exact: H_Abort.
- (* skip *)
  apply: (H_Consequence _ Q Q) => //.
  + exact: H_Skip.
  + move=> m mu H1; apply:  (le_trans H1).
    by move : (Hhl m); rewrite ssem_skipE eexp_dunit.
- (* assign *)
  apply: (H_Consequence _ (fun m => Q m.[x <- `[{e}] m]) Q).
    + exact: H_Asgn.
    + move=> m mu H1; apply:  (le_trans H1).
      by move : (Hhl m); rewrite ssem_assnE eexp_dunit.
- (* gassign *)
  apply: (H_Consequence _ (fun m => Q (m.{gx <- `[{ge}] m})) Q).
  + exact: H_GAsgn.
  + move=> m mu H1; apply: (le_trans H1).
    by move : (Hhl m); rewrite ssem_gassnE eexp_dunit.
- (* random *)
  apply: (H_Consequence _
            (fun m => espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) Q) Q).
  + exact: H_Random.
  + move=> m mu H1; apply: (le_trans H1).
    by move : (Hhl m); rewrite ssem_rndE.
- (* block *)
  apply: H_Block => // m; apply: ihb => //.
  + by move=> m'; rewrite /bound; case: ifP => _ //; exact: le0y.
  + move=> m'; rewrite /bound; case: ifP => [/eqP -> | _]; last exact: leey.
    by move: (Hhl m); rewrite ssem_blockE espe_dlet_ret.
- (* if *)
  apply: H_If.
  + rewrite /lift.
    apply: ih1 => m //.
    + case (`[{e}] m) => //=. exact : le0y.
    + move: (Hhl m); rewrite ssem_ifE; case (`[{e}] m) => // _.
      exact : leey.
  + rewrite /lift.
    apply: ih2 => m //.
    + case (~~ `[{e}] m) => //=. exact: le0y.
    + move: (Hhl m); rewrite ssem_ifE; case (`[{e}] m) => //= _.
      exact : leey.
- (* while *)
  pose I : cond := fun m => espe (ssem_ ps (While e Do c0) m) Q .
  have Ipos :  forall m : mem, (0%R <= I m)%E.
  + move => m; subst I=> /=.
    rewrite /espe esum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply (H_Consequence _ I (lift (`[{~~e}]) I)).
  + apply: H_While => //.
    apply ih0 => //.
    +  move => m; rewrite /lift; case (`[{e}] m) => //=. exact: le0y.
    rewrite /lift.
    move => m; case_eq (`[{e}] m) => He; last first. exact : leey.
    subst I => /=.
    by rewrite -eexp_dlet // ssem_whileS // ssem_seqE.
  + move => m mu H1;  move : (Hhl m).
    apply: le_trans.
    move : H1; subst I => //=.
    apply: le_trans; apply le_esum.
    move => x; rewrite /lift.
    case_eq ( ~~ `[{e}] x) => ? //=.
    rewrite lee_pmul //=.
    + by rewrite lee_fin.
    + by rewrite ssem_while0 // eexp_dunit.
    + rewrite lee_pmul //= ?lee_fin //.
      exact : leey.
- (* seq *)
  pose R : cond := fun x : mem => espe (ssem_ ps c2 x) Q.
  have Rpos :   forall m : mem, (0%R <= R m)%E.
  + move => m; subst R => //=; rewrite /espe.
    rewrite /espe esum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply: (H_Seq _ _ _ _ _ R) => //=.
  + apply ih2 => //=.
  + apply ih1 => //=.
    by move => m; move : (Hhl m);  rewrite ssem_seqE eexp_dlet.
- (* call *)
  apply: H_khl.
  apply: (H_adapt _ _ (get_pre (cl_mgt f)) _ (get_post (cl_mgt f))).
  + by apply: H_call; right.
  + move=> m0 mu h.
    have Hesum :
        (\esum_(i in (@classical_sets.setT mem))
           ((if (EFin (mu i) <= EFin ((ssem_ ps (ps f) m0) i))%E then 0%E else +oo%E)
              * (mu i)%:E) = 0)%E.
    { apply/eqP; rewrite eq_le; apply/andP; split; first  exact: h.
      apply: esum_ge0 => ??; exact: cl_mgt_pos. }
    have Hdom : forall s, (EFin (mu s) <= EFin ((ssem_ ps (ps f) m0) s))%E.
    { move=> s; rewrite leNgt; apply/negP => Hgt.
      have Hmu : (0 < (mu s)%:E)%E.
      by rewrite lte_fin; exact: (le_lt_trans (ge0_mu _ s) Hgt).
      have := @esum_eq0P _ _ _ _ (fun x _ => (cl_mgt_pos mu m0 f x)) Hesum s I.
      by rewrite (lt_geF Hgt) gt0_mulye. }
    simpl in h.
    move: (Hhl m0); rewrite ssem_call_eq; apply: le_trans.
    rewrite /espe; apply: le_esum => s ?; apply: (lee_wpmul2l (Hg s)).
    exact: (lee_tofin (Hdom s)).
Qed.

Lemma rel_complete (c : cmd) (P : cond) (Q : cond2) :
  (forall m,  (0 <= P m)%E) ->
  (forall m mu m', (0 <= Q m mu m')%E) ->
  cond2_mono Q ->
  kehl_ ps P c Q -> derivable2 ps cl_mgt P c Q.
Proof.
move=> h1 h2 h3 /kehl_ehl h; apply: H_hl => //= s0. apply rel_complete_d => //.
move => m; rewrite /bound; case: ifP => _ //=.
exact: le0y.
Qed.

Theorem khoare_complete: forall P c (Q: mem -> mem -> \bar R) cl,
  (forall m,  (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  kehl_ ps P c (fun s0 _ s =>Q s0 s) -> derivable2 ps cl P c (fun s0 _ s =>Q s0 s).
Proof.
move=> P c Q cl h1 h2 Hvalid.
apply: (H_rec _ _ _ _ cl_mgt); last first.
- by apply rel_complete.
- move=> p'; apply: rel_complete => //.
  + move=> m mu m'; rewrite /get_post /cl_mgt /=.
    by case: ifP => _; [exact: lexx | exact: leey].
  + exact: (post_mono p').
  + move=> m.
    rewrite /get_pre /cl_mgt /= /espe.
    under eq_esum do rewrite lexx mul0e.
    by rewrite esum0.
Qed.

Theorem hoare_complete: forall f c g cl,
  (forall m,  (0 <= f m)%E) ->
  (forall m , (0 <= g m)%E) ->
  ehl_ ps f c g -> derivable ps cl f c g.
Proof.
move=> f c g cl H1 H2 Hvalid.
apply: H_khl.
by apply khoare_complete.
Qed.

End Complete.

Section prhl.

From xhl.prhl Require Import prhl.

Notation cmd := (@cmd ident ident cmem).

Lemma espe_coupling (ν : Distr (cmem * cmem)) (g g':(@ehl_stmt.cond _ cmem)) :
  (forall m, 0 <= g m)%E ->
  (forall m, 0 <= g' m)%E ->
  (forall p, p \in dinsupp ν -> (g p.2 <= g' p.1)%E) ->
  (espe (dsnd ν) g <= espe (dfst ν) g')%E.
Proof.
move => Hg Hg' Hpw.
rewrite eexp_dlet //.
rewrite {1}/espe.
rewrite (eq_esum _ _ (fun p => g p.2 * EFin (ν p))%E).
+ by move => ??; rewrite eexp_dunit.
rewrite [espe (dfst ν) g'] eexp_dlet //.
rewrite {1}/espe.
rewrite (eq_esum _
           (fun x => espe (dunit (T:=cmem) x.1) g' * EFin (ν x))%E
           (fun p => g' p.1 * EFin (ν p))%E).
+ by move => ??; rewrite eexp_dunit.
rewrite /espe; apply: le_esum => p _.
case/boolP: (p \in dinsupp ν) => [hp | /dinsuppPn hp].
+ apply: lee_wpmul2r; first by apply: lee_tofin; apply: ge0_mu.
  exact: Hpw _ hp.
+ by rewrite hp !mule0.
Qed.

Lemma ehl_prhl (c d:cmd) (f g f' g':(@ehl_stmt.cond _ cmem))  P Q (ps: ident -> cmd):
  (forall m : cmem, 0 <= g m)%E ->
  (forall m : cmem, 0 <= g' m)%E ->
  ehl_ ps f' d g' ->
  @prhl_ ps P d c Q ->
  (forall m, exists m', f' m' <= f m /\ P (m',m))%E ->
  (forall m' m, Q (m',m) -> g m <= g' m')%E ->
  ehl_ ps f c g.
Proof.
move => Hg Hg' He Hr H1 H2 m.
have [m' Hm'] := H1 m.
have [Hle HP] := Hm'.
have [ν [Hfst Hsnd] Hrange] := prhlw Hr HP.
rewrite -Hsnd.
have Hpw : forall p, p \in dinsupp ν -> (g p.2 <= g' p.1)%E.
{ by move => [m1 m2] /Hrange /H2. }
apply: (@le_trans _ _ (espe (dfst ν) g')).
- exact: (espe_coupling ν g g' Hg Hg' Hpw).
  rewrite Hfst.
  apply: (@le_trans _ _ (f' m')); first exact: (He m').
  exact: Hle.
Qed.

End prhl.

End ehl.
