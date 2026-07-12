(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis Require Import esum ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr edistr.
From mathcomp    Require  finmap.
From xhl.pwhile Require Import notations inhabited pwhile psemantic range.
From xhl.ehl    Require Import ehl_stmt.

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

Inductive derivable : psi -> phi -> cond -> cmd -> cond -> Prop :=
| H_Skip : forall f cl ps,
    derivable ps cl f skip f
| H_Abort : forall f g cl ps,
    (forall m, (0 <= f m)%E) ->
    derivable ps cl f abort g
| H_Asgn : forall {T : IhbType.type} x (e : expr_ X mem T) f cl ps,
    derivable ps cl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f
| H_Random : forall {T : IhbType.type} x (d:expr_ X mem (Distr T))  f cl ps,
    let g m :=
      espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f
    in
    derivable ps cl g (x <$- d) f
| H_Seq : forall f c d g h cl ps,
    (forall m, (0 <= g m)%E) ->
    derivable ps cl h d g -> derivable ps cl f c h -> derivable ps cl f (c;;d) g
| H_If : forall f g (e:expr_ X mem bool) c1 c2 cl ps,
    derivable ps cl (lift (esem e) f) c1 g ->
    derivable ps cl (lift (fun m => negb (esem e m)) f) c2 g ->
    derivable ps cl f (If e then c1 else c2) g
| H_While : forall f (e:expr_ X mem bool) c cl ps ,
    (forall m, 0 <= f m)%E ->
    derivable ps cl (lift (esem e) f) c f ->
    derivable ps cl f (While e Do c) (lift (fun m => negb (esem e m)) f)
| H_Consequence : forall f' g' f g (c : cmd) cl ps,
    derivable ps cl f' c g' ->
    (forall m mu,  espe mu g' <= f' m -> espe mu g <= f m)%E ->
    derivable ps cl f c g
| H_khl : forall P Q c cl ps,
    derivable2 ps cl P c (fun _ _ => Q) -> derivable ps cl P c Q
with derivable2 : psi -> phi -> cond -> cmd -> cond2 -> Prop :=
| H_hl: forall P Q c cl ps,
    (forall m mu m', (0 <= Q m mu m')%E) ->
    (forall s0, derivable ps cl (bound P s0) c (fun s => Q s0 ((ssem_ ps c s0 s)%:E) s)) ->
    derivable2 ps cl P c Q
| H_call : forall cl (f:Y) ps,
    derivable2 ps cl (get_pre (cl f)) (call f) (get_post (cl f))
| H_rec : forall P Q c (cl cl':phi) ps',
    (forall p' ps, derivable2 ps cl (get_pre (cl p')) (ps' p') (get_post (cl p'))) ->
    (forall ps, derivable2 ps cl P c Q) ->
    derivable2 ps' cl' P c Q
| H_adapt : forall (P1 P2 : cond) (Q1 Q2 : cond2) c cl ps,
    derivable2 ps cl P2 c Q2 ->
    (forall m mu,  espe mu (fun m' => Q2 m ((mu m')%:E) m') <= P2 m ->
              espe mu (fun m' => Q1 m ((mu m')%:E) m') <= P1 m)%E ->
    derivable2 ps cl P1 c Q1.

Scheme derivable_min := Minimality for derivable Sort Prop
    with derivable2_min := Minimality for derivable2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

End Logic.

Section Sound.

Section Rules.
Context (ps: psi).

Notation ehl   := (ehl_ ps).
Notation kehl   := (kehl_ ps).

(* -------------------------------------------------------------------- *)

Lemma ehl_skip f g :
  (forall m, (g m <= f m)%E) ->
  ehl f skip g.
Proof. by move => h m; rewrite ssemE exp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_abort f g :
  (forall m, (0 <= f m)%E) ->
  ehl f abort g.
Proof.
move => h m.
rewrite ssem_abortE /espe.
rewrite (@esum.eq_sum _ _ _ (fun _ => 0)).
- by rewrite esum.sum0.
- by move => x; rewrite dnullE mule0.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_seq_m (m:mem) f g h c1 c2:
  (forall m : mem, 0 <= g m)%E ->
  (espe (ssem_ ps c1 m) h <= f m)%E ->
  (forall m : mem, espe (ssem_ ps c2 m) g <= h m)%E ->
  (espe(\dlet_(m' <- ssem_ ps c1 m) ssem_ ps c2 m') g <= f m)%E.
Proof.
move => Hg h1 h2.
rewrite exp_dlet //.
apply: (@le_trans _ _ (espe (ssem_ ps c1 m) h)); last exact: h1.
rewrite /espe; apply: esum.le_sum.
- move => x; apply: mule_ge0; last by apply: lee_tofin; apply: ge0_mu.
  apply: sum_ge0 => x'; apply: mule_ge0; first exact: Hg.
  by apply: lee_tofin; apply: ge0_mu.
- move => x; apply: lee_wpmul2r.
  + by apply: lee_tofin; apply: ge0_mu.
  + exact: h2.
Qed.

Lemma ehl_seq f g h c1 c2:
  (forall m, (0 <= g m)%E) ->
  ehl f c1 h -> ehl h c2 g -> ehl f (c1 ;; c2) g.
Proof.
move => Hg h1 h2 m.
rewrite ssemE.
by apply: (ehl_seq_m m _ _ h).
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_assign {T : IhbType.type} f x (e : expr_ X mem T) :
  ehl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f.
Proof. by  move => m; rewrite ssemE exp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_random {T : IhbType.type} f x (d:expr_ X mem (Distr T)) :
  let g m :=
    espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f
  in
  ehl g (x <$- d) f.
Proof. by move => g m; rewrite ssemE. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_if f (e:expr_ X mem bool) c1 c2 g :
  ehl (lift (esem e) f) c1 g ->
  ehl (lift (fun m => negb (esem e m)) f) c2 g ->
  ehl f (If e then c1 else c2) g.
Proof.
move => Hc1 Hc2 m.
rewrite ssemE.
case h: (`[{e}] m).
- move : (Hc1 m).
  by rewrite /lift h /=.
  move : (Hc2 m).
  by  rewrite /lift h /=.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_while (e:expr_ X mem bool) c f :
  (forall m, 0 <= f m)%E ->
  ehl (lift (esem e) f) c f ->
  ehl f (While e Do c) (lift (fun m => negb (esem e m)) f).
Proof.
move => Hf.
have Hpos : forall m : mem, (0%R <= (if ~~ `[{e}] m then f m else +oo))%E.
+ by move => m;  case (`[{e}] m) => //=.
rewrite /lift => Hi m.
rewrite  ssemE /espe esum_sum';last first.
- move => x; rewrite mule_ge0 //.
  by rewrite lee_tofin.
apply: (esum_dlim_r (homo_whilen e c m)) => //.
move => n; rewrite -esum_sum';last first.
- move => x; rewrite mule_ge0 //.
  by rewrite lee_tofin.
move : m.
elim : n => /=.
+ by apply ehl_abort.
+  move => n Hi'.
   apply ehl_if => //=.
   + by apply: (ehl_seq _ _ f).
   + by apply ehl_skip.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_conseq c f g f' g':
  ehl f' c g' ->
  (forall m d,  espe d g' <= f' m -> espe d g <= f m)%E ->
  ehl f c g.
Proof. move => h' hc m. by apply hc. Qed.

(* -------------------------------------------------------------------- *)

Lemma kehl_conseq c f f' (g g' : cond2):
  kehl f' c g' ->
  (forall m d,  espe d (fun m' => g' m ((d m')%:E) m') <= f' m ->
           espe d (fun m' => g m ((d m')%:E) m') <= f m)%E ->
  kehl f c g.
Proof. by move => h' hc m; apply hc. Qed.

(* -------------------------------------------------------------------- *)

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx (cl : phi) (ps: psi) (P: cond) (Q: cond2) (c: cmd) :=
  (forall p, kehl_ ps (get_pre (cl p)) (call p) (get_post (cl p))) ->
  kehl_ ps P c Q.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx (cl : phi) (ps_init: psi):=
  forall p ps, hoare_triple_ctx cl ps
            (get_pre (cl p))
            (get_post (cl p))
            (ps_init p).

Lemma recursive_proc (ps': psi) (cl' : phi) :
  hoare_triple_proc_ctx cl' ps' ->
  (forall p, kehl_ ps' (get_pre (cl' p)) (call p)  (get_post (cl' p))).
Proof.
  Admitted.
(*   move => h p s. *)
(*   rewrite /espe  esum_sum';last first. *)
(*   - move => x; rewrite mule_ge0 // ?lee_tofin //. *)
(*     exact: post_pos. *)
(*    rewrite {2}test8. *)
(*    apply esum_dlim_r. *)
(*     + move => ????. *)
(*      apply mono_ssem_aux. *)
(*      by apply homo_ubnf. *)
(*     + move => m. exact: post_pos. *)
(*   move => n. *)
(*   (*This should be a lemma*) *)
(*   rewrite ssem_ubnf_dnull ubnf_ssem (test9 _ _ _ _ ps') test5. *)
(*   move : s p. *)
(*   elim : n => [| n Hn]. *)
(*   + move => ??. rewrite ssem_false_ps. *)
(*     under eq_esum do  rewrite dnullE mule0. *)
(*     rewrite esum1 //. *)
(*     exact: pre_pos. *)
(*   move => s p. *)
(*   rewrite (inline2_split n 1) //=. *)
(*   rewrite -esum_sum';last first. *)
(*   + move => x; rewrite mule_ge0 // ?lee_tofin //. *)
(*     exact: post_pos. *)
(*   rewrite /hoare_triple_proc_ctx in h. *)
(*   rewrite /hoare_triple_ctx in h. *)
(*   apply: h => // p0 s0. *)
(*   rewrite /espe esum_sum';last first. *)
(*   + move => x; rewrite mule_ge0 // ?lee_tofin //. *)
(*     exact: post_pos. *)
(*  under eq_esum do rewrite (@post_inv _ _ mem cl' p0 _ _ 0%E). *)
(*  by apply: Hn. *)
(* Qed. *)

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple :
  forall P Q c (cl: phi) (ps: psi),
    hoare_triple_proc_ctx cl ps  ->
    hoare_triple_ctx cl ps P Q c ->
    kehl_ ps P c Q .
Proof.
  move => ????? H H0.
  apply H0.
  by apply: recursive_proc.
Qed.

(* -------------------------------------------------------------------- *)
End Rules.

Definition valid_cl (cl:phi) (ps:psi) :=
  forall (f:Y), kehl_ ps (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma soundness :
  (forall (ps:psi) (cl:phi) P (c:cmd) Q, derivable ps cl P c Q ->
      valid_cl cl ps -> ehl_ ps P c Q) /\
  (forall ps cl P c Q, derivable2 ps cl P c Q ->
     valid_cl cl ps -> kehl_ ps P c Q).
Proof.
apply: derivable_mut.
- (* H_Skip *)  by move=> *; exact: ehl_skip.
- (* H_Abort *) by move=> *; exact: ehl_abort.
- (* H_Asgn *) by move=> *; exact: ehl_assign.
- (* H_Random *) by move=> *; exact: ehl_random.
- (* H_Seq *)
  move=> P c Q d R cl ps Hpos ? IHd ? IHc Hv.
  by apply: ehl_seq; [exact: Hpos | exact: (IHc Hv) | exact: (IHd Hv)].
- (* H_If *)
  move=> Pr Po e c1 c2 cl ? ? IH1 ? IH2 Hv.
  by apply: ehl_if; [exact: IH1 | exact: IH2].
- (* H_While *)
  by move=> I e c cl ? Hpos ? IH Hv; apply: ehl_while; [exact: Hpos | exact: IH].
- (* H_Consequence *)
  move=> P2 Q2 P1 Q1 c cl ps ? HP HQ IH Hv.
  by apply: ehl_conseq; [ exact: HP | exact: HQ].
- (* H_khl *) by move=> P Q c cl ? ? IH Hv; apply/ehl_kehl; exact: IH.
- (* H_hl *) by move=> P Q c cl ? Hpos ? IH Hv; apply/kehl_ehl=> s0; exact: IH.
- (* H_call *) by move=> cl f ? Hv; exact: Hv.
- (* H_rec *)
-  move=> P Q c cl cl' ps' ? IH_body IH_c HI Hv.
   admit.
   (* apply: (recursion_hoare_triple  _ _ _ cl). *)
   (* + rewrite /hoare_triple_proc_ctx. *)
   (*   by rewrite /hoare_triple_ctx. *)
   (* + rewrite /hoare_triple_ctx. *)
   (*   by move => h; apply: HI. *)
- (* H_adapt *)
  move=> P1 P2 Q1 Q2 c cl ps ? IH H Hv m.
   exact: (H m (ssem_ ps c m) (IH Hv m)).
Admitted.
   (* Qed. *)

Corollary hoare_sound0 P c Q ps : derivable ps cl_empty P c Q -> ehl_ ps P c Q.
Proof.
  move => Hd.
  apply: (proj1 soundness _ cl_empty) => //.
  rewrite /valid_cl /kehl_ => //= => *.
  rewrite /empty_precondition.
  exact: leey.
Qed.

Corollary khoare_sound0 P c Q ps : derivable2 ps cl_empty P c Q -> kehl_ ps P c Q.
Proof.
  move => Hd.
  apply: (proj2 soundness _ cl_empty) => //.
  rewrite /valid_cl /kehl_ => //= => *.
  rewrite /empty_precondition.
  exact: leey.
Qed.

End Sound.

Section Complete.

Definition cl_mgt ps : Y -> clause:=
fun (f:Y) => ((fun _ => 0)%E,
                (fun (s0: mem) r s =>
                   if (r <= ((ssem_ ps (ps f) s0) s)%:E)%E then 0%E else +oo%E)
          ).

Lemma post_mono_cl_mgt ps : cl_post_mono (cl_mgt ps).
Proof.
move => f r r' H x x'.
rewrite /cl_mgt //=.
case_eq  ( r <= (ssem_ ps (ps f) x x')%:E)%E.
case  (r' <= (ssem_ ps (ps f) x x')%:E)%E => //=.
case_eq (r' <= (ssem_ ps (ps f) x x')%:E)%E => //=.
move =>  H1  H2.
have : (r <= (ssem_ ps (ps f) x x')%:E)%E = true.
+ by apply: (le_trans H ).
by rewrite H2.
Qed.

Lemma pre_pos_cl_mgt ps : cl_pre_pos (cl_mgt ps).
Proof. by []. Qed.

Lemma post_pos_cl_mgt ps : cl_post_pos (cl_mgt ps).
Proof.
  move => f x r x'  //=.
  by case: (r <= EFin (ssem_ ps (ps f) x x'))%E.
Qed.

HB.instance Definition _ ps :=
  isPhi.Build X Y mem
    (cl_mgt ps)
    (post_mono_cl_mgt ps)
    (pre_pos_cl_mgt ps)
    (post_pos_cl_mgt ps).

Lemma cl_mgt_pos (mu: {distr mem/R}) m0 (f: Y) ps':
  forall s,(0 <= (if (EFin (mu s) <= EFin ((ssem_ ps' (ps' f) m0) s))%E
            then 0%E else +oo%E) * (mu s)%:E)%E.
Proof.
move => s;apply: mule_ge0.
+ by case: ifP => _; [exact: lexx | exact: leey].
exact: (lee_tofin (ge0_mu _ s)).
Qed.

Lemma rel_complete_d c (P Q : cond) ps' :
  (forall m,  (0 <= P m)%E) ->
  (forall m , (0 <= Q m)%E) ->
  ehl_ ps' P c Q -> (forall ps, derivable ps (cl_mgt ps') P c Q).
Proof.
  elim: c P Q =>
        [ | | T x e | T x d | e c1 ih1 c2 ih2 | e c0 ih0 | c1 ih1 c2 ih2 | f ]
        P Q HP HQ Hhl ps.
- (* abort *) exact: H_Abort.
- (* skip *)
  apply: (H_Consequence Q Q) => //.
  + exact: H_Skip.
  + move=> m mu H1; apply:  (le_trans H1).
    by move : (Hhl m); rewrite ssem_skipE exp_dunit.
- (* assign *)
  apply: (H_Consequence (fun m => Q m.[x <- `[{e}] m]) Q).
    + exact: H_Asgn.
    + move=> m mu H1; apply:  (le_trans H1).
      by move : (Hhl m); rewrite ssem_assnE exp_dunit.
- (* random *)
  apply: (H_Consequence
            (fun m => espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) Q) Q).
  + exact: H_Random.
  + move=> m mu H1; apply: (le_trans H1).
    by move : (Hhl m); rewrite ssem_rndE.
- (* if *)
  apply: H_If.
  + rewrite /lift.
    apply: ih1 => m //.
    + by case (`[{e}] m).
    + move: (Hhl m); rewrite ssem_ifE; case (`[{e}] m) => // _.
      exact : leey.
  + rewrite /lift.
    apply: ih2 => m //.
    + by case (~~ `[{e}] m).
    + move: (Hhl m); rewrite ssem_ifE; case (`[{e}] m) => //= _.
      exact : leey.
- (* while *)
  pose I : cond := fun m => espe (ssem_ ps' (While e Do c0) m) Q .
  have Ipos :  forall m : mem, (0%R <= I m)%E.
  + move => m; subst I=> /=.
    rewrite /espe sum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply (H_Consequence I (lift (`[{~~e}]) I)).
  + apply: H_While => //.
    apply ih0 => //.
    + by move => m; rewrite /lift; case (`[{e}] m).
    rewrite /lift.
    move => m; case_eq (`[{e}] m) => He; last first. exact : leey.
    subst I => /=.
    by rewrite -exp_dlet // ssem_whileS // ssem_seqE.
  + move => m mu H1;  move : (Hhl m).
    apply: le_trans.
    move : H1; subst I => //=.
    apply: le_trans; apply esum.le_sum.
    + by move => x; rewrite mule_ge0 //= lee_tofin.
    move => x; rewrite /lift.
    case_eq ( ~~ `[{e}] x) => ? //=.
    rewrite lee_pmul //=.
    + by rewrite lee_fin.
    + by rewrite ssem_while0 // exp_dunit.
    + rewrite lee_pmul //= ?lee_fin //.
      exact : leey.
- (* seq *)
  pose R : cond := fun x : mem => espe (ssem_ ps' c2 x) Q.
  have Rpos :   forall m : mem, (0%R <= R m)%E.
  + move => m; subst R => //=; rewrite /espe.
    rewrite /espe sum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply: (H_Seq _ _ _ _ R) => //=.
  + apply ih2 => //=.
  + apply ih1 => //=.
    by move => m; move : (Hhl m);  rewrite ssem_seqE exp_dlet.
- (* call *)
  apply: H_khl.
  apply: (H_adapt _ (get_pre (cl_mgt ps' f)) _ (get_post (cl_mgt ps' f))).
  + by apply: H_call; right.
  + move=> m0 mu h.
    simpl in h.
    have Hesum :
        (\esum_(i in (@classical_sets.setT mem))
           ((if (EFin (mu i) <= EFin ((ssem_ ps' (ps' f) m0) i))%E then 0%E else +oo%E)
              * (mu i)%:E) = 0)%E.
    { rewrite -esum_sum'; last first. exact: (cl_mgt_pos).
      apply/eqP; rewrite eq_le; apply/andP; split; first  exact: h.
      apply: sum_ge0; exact: cl_mgt_pos. }
    have Hdom : forall s, (EFin (mu s) <= EFin ((ssem_ ps' (ps' f) m0) s))%E.
    { move=> s; rewrite leNgt; apply/negP => Hgt.
      have Hmu : (0 < (mu s)%:E)%E.
      by rewrite lte_fin; exact: (le_lt_trans (ge0_mu _ s) Hgt).
      have := @esum_eq0P _ _ _ _ (fun x _ => (cl_mgt_pos mu m0 f ps' x)) Hesum s I.
      by rewrite (lt_geF Hgt) gt0_mulye. }
    move: (Hhl m0); rewrite ssem_call_eq; apply: le_trans.
    rewrite /espe; apply: esum.le_sum.
    - move=> s; apply: mule_ge0; first exact: HQ.
      exact: (lee_tofin (ge0_mu _ s)).
    - move=> s; apply: (lee_wpmul2l (HQ s)).
      exact: (lee_tofin (Hdom s)).
Qed.

Lemma rel_complete (c : cmd) (P : cond) (Q: cond2) ps:
  (forall m,  (0 <= P m)%E) ->
  (forall m mu m', (0 <= Q m mu m')%E) ->
  cond2_mono Q ->
  kehl_ ps P c Q ->
  (forall ps', derivable2 ps' (cl_mgt ps) P c Q).
Proof.
  move=> h1 h2 h3 /kehl_ehl h ps'; apply: H_hl => // s0. apply rel_complete_d => //.
  + by rewrite /bound => m; case_eq (m == s0) => //=.
 Admitted.

Theorem khoare_complete: forall P c (Q: mem -> mem -> \bar R) ps cl,
  (forall m,  (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  kehl_ ps P c (fun s0 _ s =>Q s0 s) -> derivable2 ps cl P c (fun s0 _ s =>Q s0 s).
Proof.
move=> P c Q ps cl h1 h2 Hvalid.
apply: (H_rec _ _ _ (cl_mgt ps)); last first.
- by apply rel_complete.
- move=> p'; apply: rel_complete => //.
  + move=> m mu m'; rewrite /get_post /cl_mgt /=.
    by case: ifP => _; [exact: lexx | exact: leey].
  + exact: (post_mono p').
  + move=> m.
    rewrite /get_pre /cl_mgt /= /espe.
    under esum.eq_sum do rewrite lexx mul0e.
    by rewrite esum.sum0.
Qed.

Theorem hoare_complete: forall f c g cl ps,
  (forall m,  (0 <= f m)%E) ->
  (forall m , (0 <= g m)%E) ->
  ehl_ ps f c g -> derivable ps cl f c g.
Proof.
move=> f c g cl ps H1 H2 Hvalid.
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
rewrite exp_dlet //.
rewrite (_ : (fun p => espe (dunit p.2) g) = (fun p => g p.2));
  last by apply/funext => p; rewrite exp_dunit.
rewrite [espe (dfst ν) g']exp_dlet //.
rewrite (_ : (fun p => espe (dunit p.1) g') = (fun p => g' p.1));
  last by apply/funext => p; rewrite exp_dunit.
rewrite /espe; apply: esum.le_sum.
- move => p; apply: mule_ge0; first exact: Hg.
  by apply: lee_tofin; apply: ge0_mu.
- move => p.
  case/boolP: (p \in dinsupp ν) => [hp | /dinsuppPn hp].
  + apply: lee_wpmul2r; first by apply: lee_tofin; apply: ge0_mu.
    exact: Hpw _ hp.
  + by rewrite hp !mule0.
Qed.

Lemma ehl_prhl (c d:cmd) (f g f' g':(@ehl_stmt.cond _ cmem))  P Q (ps: ident -> cmd):
  (forall m : cmem, 0 <= g m)%E ->
  (forall m : cmem, 0 <= g' m)%E ->
  ehl_ ps f' d g' ->
  @prhl ps P d c Q ->
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
