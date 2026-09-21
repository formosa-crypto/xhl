(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp           Require finmap.
From xhl.pwhile         Require Import notations inhabited mem pwhile psemantic range.
From xhl.prhl           Require Import prhl.
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
Context {R : realType} {A B : codeType} {X Xg Y : eqType}
        {M : memType A B X Xg}.

Local Notation Distr T := {distr T%type / R}.

Local Notation cond := (@cond R A B X Xg M).
Local Notation cond2 := (@cond2 R A B X Xg M).

Local Notation phi := (@Phi.type R A B X Xg Y M).
Local Notation psi := (@psi R A B X Xg Y M).
Local Notation expr := (@expr_ A B X Xg M).

Implicit Types  (f g h : cond).

Section Logic.

Inductive derivable : psi -> phi -> cond -> cmd -> cond -> Prop :=
| H_Abort : forall f g cl ps,
    (forall m, (0 <= f m)%E) ->
    derivable ps cl f abort g
| H_Skip : forall f cl ps,
    derivable ps cl f skip f
| H_Asgn : forall {T : A} x (e : expr T) f cl ps,
    derivable ps cl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f
| H_GAsgn : forall {T : B} x (e : expr T) f cl ps,
    derivable ps cl (fun m => f (m.{x <- `[{e}] m})) (G x <<- e) f
| H_Random : forall {T : A} x (d:expr (Distr T))  f cl ps,
    let g m :=
      espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f
    in
    derivable ps cl g (x <$- d) f
| H_Block : forall f g bs c rs cl ps,
    (forall m, (0 <= g m)%E) ->
    (forall m, derivable ps cl (bound (fun _ => f m) (minit m bs)) c
                               (fun m'' => g (mret m m'' rs))) ->
    derivable ps cl f (block bs c rs) g
| H_If : forall f g (e:expr bool) c1 c2 cl ps,
    derivable ps cl (lift (esem e) f) c1 g ->
    derivable ps cl (lift (fun m => negb (esem e m)) f) c2 g ->
    derivable ps cl f (If e then c1 else c2) g
| H_While : forall f (e:expr bool) c cl ps ,
    (forall m, 0 <= f m)%E ->
    derivable ps cl (lift (esem e) f) c f ->
    derivable ps cl f (While e Do c) (lift (fun m => negb (esem e m)) f)
| H_Seq : forall f c d g h cl ps,
    (forall m, (0 <= g m)%E) ->
    derivable ps cl h d g -> derivable ps cl f c h -> derivable ps cl f (c;;d) g
| H_Consequence : forall f' g' f g (c : cmd) cl ps,
    derivable ps cl f' c g' ->
    (forall m mu,  espe mu g' <= f' m -> espe mu g <= f m)%E ->
    derivable ps cl f c g
| H_Proc : forall f g (p:Y) cl ps,
    derivable ps cl f (ps p) g ->
    derivable ps cl f (call p) g
| H_khl : forall P Q c cl ps,
    derivable2 ps cl P c (fun _ => Q) -> derivable ps cl P c Q
with derivable2 : psi -> phi -> cond -> cmd -> cond2 -> Prop :=
| H_hl: forall P Q c cl ps,
    (forall s0, derivable ps cl (bound P s0) c (fun s => Q s0 s)) ->
    derivable2 ps cl P c Q
| H_call : forall cl (f:Y) ps,
    derivable2 ps cl (get_pre (cl f)) (call f) (get_post (cl f))
| H_rec : forall P Q c (cl cl':phi) ps',
    (forall p' ps, derivable2 ps cl (get_pre (cl p')) (ps' p') (get_post (cl p'))) ->
    (forall ps, derivable2 ps cl P c Q) ->
    derivable2 ps' cl' P c Q
| H_adapt : forall (P1 P2 : cond) (Q1 Q2 : cond2) c cl ps,
    (forall m mu,  espe mu (fun m' => Q2 m  m') <= P2 m ->
              espe mu (fun m' => Q1 m  m') <= P1 m)%E ->
    derivable2 ps cl P2 c Q2 ->
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
Proof. by move => h m; rewrite ssemE eexp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_abort f g :
  (forall m, (0 <= f m)%E) ->
  ehl f abort g.
Proof.
move => h m.
rewrite ssem_abortE /espe.
rewrite (eq_esum _ _ (fun _ => 0)).
- by move => x; rewrite dnullE mule0.
- by rewrite esum0.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_seq_m (m:M) f g h c1 c2:
  (forall m : M, 0 <= g m)%E ->
  (espe (ssem_ ps c1 m) h <= f m)%E ->
  (forall m : M, espe (ssem_ ps c2 m) g <= h m)%E ->
  (espe(\dlet_(m' <- ssem_ ps c1 m) ssem_ ps c2 m') g <= f m)%E.
Proof.
move => Hg h1 h2.
rewrite eexp_dlet //.
apply: (@le_trans _ _ (espe (ssem_ ps c1 m) h)); last exact: h1.
rewrite /espe; apply: le_esum => x ?; apply: lee_wpmul2r.
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

Lemma ehl_assign {T : A} f x (e : expr T) :
  ehl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f.
Proof. by  move => m; rewrite ssemE eexp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_gassign {T : B} f x (e : expr T) :
  ehl (fun m => f (m.{x <- `[{e}] m})) (G x <<- e) f.
Proof. by move => m; rewrite ssem_gassnE eexp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_block f g bs c rs :
  (forall m, (0 <= g m)%E) ->
  (forall m, ehl (bound (fun _ => f m) (minit m bs)) c
                 (fun m'' => g (mret m m'' rs))) ->
  ehl f (block bs c rs) g.
Proof.
move=> Hg H m; rewrite ssem_blockE espe_dlet_ret //.
by have := H m (minit m bs); rewrite /bound eqxx.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_random {T : A} f x (d:expr (Distr T)) :
  let g m :=
    espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f
  in
  ehl g (x <$- d) f.
Proof. by move => g m; rewrite ssemE. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_if f (e:expr bool) c1 c2 g :
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

Lemma ehl_while (e:expr bool) c f :
  (forall m, 0 <= f m)%E ->
  ehl (lift (esem e) f) c f ->
  ehl f (While e Do c) (lift (fun m => negb (esem e m)) f).
Proof.
move => Hf.
have Hpos : forall m : M, (0%R <= (if ~~ `[{e}] m then f m else +oo))%E.
+ move => m;  case (`[{e}] m) => //=. exact: le0y.
rewrite /lift => Hi m.
rewrite ssemE /espe.
apply: (esum_dlim_r (dhomo_dnd (homo_whilen e c m)) Hpos) => n.
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
  (forall m d,  espe d (fun m' => g' m m') <= f' m ->
           espe d (fun m' => g m m') <= f m)%E ->
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
  move => h p s.
  rewrite /espe ssem_dlim_ubnf.
  apply esum_dlim_r.
  + move => ????.
    apply mono_ssem_aux.
    by apply homo_ubnf.
  + move => m. exact: post_pos.
  move => n; rewrite ssem_aux_ssem_.
  move : s p.
  elim : n => [| n Hn].
  + move => ??. rewrite ssem_false_ps.
    under eq_esum do  rewrite dnullE mule0.
    rewrite esum1 //.
    exact: pre_pos.
  move => s p.
  rewrite (inline2_split n 1) //=.
  rewrite /hoare_triple_proc_ctx in h.
  rewrite /hoare_triple_ctx in h.
  apply: h => // p0 s0.
  rewrite /espe.
  by apply: Hn.
Qed.

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
- (* H_Abort *) by move=> *; exact: ehl_abort.
- (* H_Skip *)  by move=> *; exact: ehl_skip.
- (* H_Asgn *) by move=> *; exact: ehl_assign.
- (* H_GAsgn *) by move=> *; exact: ehl_gassign.
- (* H_Random *) by move=> *; exact: ehl_random.
- (* H_Block *)
  move=> f g bs c rs cl ps Hg _ IH Hv.
  by apply: ehl_block; [exact: Hg | move=> m; exact: IH].
- (* H_If *)
  move=> Pr Po e c1 c2 cl ? ? IH1 ? IH2 Hv.
  by apply: ehl_if; [exact: IH1 | exact: IH2].
- (* H_While *)
  by move=> I e c cl ? Hpos ? IH Hv; apply: ehl_while; [exact: Hpos | exact: IH].
- (* H_Seq *)
  move=> P c Q d Rm cl ps Hpos ? IHd ? IHc Hv.
  by apply: ehl_seq; [exact: Hpos | exact: (IHc Hv) | exact: (IHd Hv)].
- (* H_Consequence *)
  move=> P2 Q2 P1 Q1 c cl ps ? HP HQ IH Hv.
  by apply: ehl_conseq; [ exact: HP | exact: HQ].
- (* H_Proc *)
  by move=> f g p cl ps _ IH Hv m; rewrite ssem_call_eq; exact: (IH Hv m).
- (* H_khl *) by move=> P Q c cl ? ? IH Hv; apply/ehl_kehl; exact: IH.
- (* H_hl *)
  move=> P Q c cl ps ? IH Hv.
  rewrite kehl_ehl => s0.
  exact: (IH s0 Hv).
- (* H_call *) by move=> cl f ? Hv; exact: Hv.
- (* H_rec *)
  move=> P Q c cl cl' ps' _ IH_body _ IH_c Hv.
  apply: (recursion_hoare_triple _ _ _ cl) => //.
  rewrite /hoare_triple_ctx.
   by move => h; apply: IH_c.
- (* H_adapt *)
  move=> P1 P2 Q1 Q2 c cl ps IH ? HI Hv m.
  apply IH.
  exact : (HI Hv m).
Qed.

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

  (* The logic is complete then there are not recurisve procedure call.
     For a complete logic with recurisve procedure and no proc rule see ehl2.v.
   *)

Lemma nocall_ki_block {n} {ps' : psi} {bs} {c : cmd} {rs} :
  nocall (k_inliner2 n (block bs c rs) ps') -> nocall (k_inliner2 n c ps').
Proof. by case: n. Qed.

Lemma nocall_ki_if {n} {ps' : psi} {b} {c1 c2 : cmd} :
  nocall (k_inliner2 n (If b then c1 else c2) ps') ->
  nocall (k_inliner2 n c1 ps') /\ nocall (k_inliner2 n c2 ps').
Proof. by case: n. Qed.

Lemma nocall_ki_while {n} {ps' : psi} {b} {c : cmd} :
  nocall (k_inliner2 n (While b Do c) ps') -> nocall (k_inliner2 n c ps').
Proof. by case: n. Qed.

Lemma nocall_ki_seq {n} {ps' : psi} {c1 c2 : cmd} :
  nocall (k_inliner2 n (c1 ;; c2) ps') ->
  nocall (k_inliner2 n c1 ps') /\ nocall (k_inliner2 n c2 ps').
Proof. by case: n. Qed.

Lemma nocall_ki_call {n} {ps' : psi} {p : Y} :
  nocall (k_inliner2 n (call p) ps') ->
  exists2 n', (n' < n)%N & nocall (k_inliner2 n' (ps' p) ps').
Proof. by case: n => [|n] //= h; exists n. Qed.

Lemma rel_complete_d_n (ps' : psi) n :
  forall (c : cmd) (P Q : cond),
    nocall (k_inliner2 n c ps') ->
    (forall m,  (0 <= P m)%E) ->
    (forall m , (0 <= Q m)%E) ->
    ehl_ ps' P c Q -> derivable ps' cl_empty P c Q.
Proof.
elim/ltn_ind: n => n ihn c.
elim: c => [ | | T x e | T gx ge | T x d | bs cb ihb rs
           | e c1 ih1 c2 ih2 | e c0 ih0 | c1 ih1 c2 ih2 | p ] P Q Hnc Hf Hg Hhl.
- (* abort *) exact: H_Abort.
- (* skip *)
  apply: (H_Consequence Q Q) => //.
  + exact: H_Skip.
  + move=> m mu H1; apply:  (le_trans H1).
    by move : (Hhl m); rewrite ssem_skipE eexp_dunit.
- (* assign *)
  apply: (H_Consequence (fun m => Q m.[x <- `[{e}] m]) Q).
    + exact: H_Asgn.
    + move=> m mu H1; apply:  (le_trans H1).
      by move : (Hhl m); rewrite ssem_assnE eexp_dunit.
- (* gassign *)
  apply: (H_Consequence (fun m => Q (m.{gx <- `[{ge}] m})) Q).
  + exact: H_GAsgn.
  + move=> m mu H1; apply: (le_trans H1).
    by move : (Hhl m); rewrite ssem_gassnE eexp_dunit.
- (* random *)
  apply: (H_Consequence
            (fun m => espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) Q) Q).
  + exact: H_Random.
  + move=> m mu H1; apply: (le_trans H1).
    by move : (Hhl m); rewrite ssem_rndE.
- (* block *)
  have Hb := nocall_ki_block Hnc.
  apply: H_Block => // m; apply: (ihb _ _ Hb) => //.
  + by move=> m'; rewrite /bound; case: ifP => _ //; exact: le0y.
  + move=> m'; rewrite /bound; case: ifP => [/eqP -> | _]; last exact: leey.
    by move: (Hhl m); rewrite ssem_blockE espe_dlet_ret.
- (* if *)
  have [H1 H2] := nocall_ki_if Hnc.
  apply: H_If.
  + rewrite /lift.
    apply: (ih1 _ _ H1) => //.
    + move => m; case (`[{e}] m) => //=; exact : le0y.
    + move => m; move: (Hhl m); rewrite ssem_ifE; case (`[{e}] m) => // _.
      exact : leey.
  + rewrite /lift.
    apply: (ih2 _ _ H2) => //.
    + move => m; case (~~ `[{e}] m) => //=. exact: le0y.
    + move => m; move: (Hhl m); rewrite ssem_ifE; case (`[{e}] m) => //= _.
      exact : leey.
- (* while *)
  have Hb := nocall_ki_while Hnc.
  pose I : cond := fun m => espe (ssem_ ps' (While e Do c0) m) Q .
  have Ipos :  forall m : M, (0%R <= I m)%E.
  + move => m; subst I=> /=.
    rewrite /espe esum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply (H_Consequence I (lift (`[{~~e}]) I)).
  + apply: H_While => //.
    apply: (ih0 _ _ Hb) => //.
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
  have [H1 H2] := nocall_ki_seq Hnc.
  pose Rm : cond := fun x : M => espe (ssem_ ps' c2 x) Q.
  have Rpos :   forall m : M, (0%R <= Rm m)%E.
  + move => m; subst Rm => //=; rewrite /espe.
    rewrite /espe esum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply: (H_Seq _ _ _ _ Rm) => //=.
  + apply: (ih2 _ _ H2) => //=.
  + apply: (ih1 _ _ H1) => //=.
    by move => m; move : (Hhl m);  rewrite ssem_seqE eexp_dlet.
- (* call *)
  have [n' ltn' Hb] := nocall_ki_call Hnc.
  apply: H_Proc.
  apply: (ihn n' ltn' _ _ _ Hb) => //.
  by move=> m; move: (Hhl m); rewrite ssem_call_eq.
Qed.

Lemma rel_complete_d (c : cmd) (P Q : cond) ps' :
  (exists n, nocall (k_inliner2 n c ps')) ->
  (forall m,  (0 <= P m)%E) ->
  (forall m , (0 <= Q m)%E) ->
  ehl_ ps' P c Q -> derivable ps' cl_empty P c Q.
Proof.
by move=> [n Hn] Hf Hg Hhl; exact: (rel_complete_d_n ps' n c P Q Hn Hf Hg Hhl).
Qed.

Lemma rel_complete (c : cmd) (P : cond) (Q : cond2) ps' :
  (exists n, nocall (k_inliner2 n c ps')) ->
  (forall m,  (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  kehl_ ps' P c Q -> derivable2 ps' cl_empty P c Q.
Proof.
  move=> Hnc Hp Hq /kehl_ehl h; apply: H_hl => s0.
  apply: rel_complete_d => //=.
  move => m; rewrite /bound; case: ifP => _ //=.
  exact: le0y.
Qed.

End Complete.
End ehl.

Section prhl.
Context {R : realType} {A B : codeType} {X Xg Y : eqType}
        {M : memType A B X Xg}.

Local Notation Distr T := {distr T%type / R}.

Local Notation cond := (@cond R A B X Xg M).
Local Notation cond2 := (@cond2 R A B X Xg M).

Local Notation phi := (@Phi.type R A B X Xg Y M).
Local Notation psi := (@psi R A B X Xg Y M).
Local Notation expr := (@expr_ A B X Xg M).

Implicit Types  (f g h : cond).

Lemma espe_coupling (ν : Distr (M * M)) (g g':cond (* (@ehl_stmt.cond R A B X Xg M) *)) :
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
           (fun x => espe (dunit (T:=M) x.1) g' * EFin (ν x))%E
           (fun p => g' p.1 * EFin (ν p))%E).
+ by move => ??; rewrite eexp_dunit.
rewrite /espe; apply: le_esum => p _.
case/boolP: (p \in dinsupp ν) => [hp | /dinsuppPn hp].
+ apply: lee_wpmul2r; first by apply: lee_tofin; apply: ge0_mu.
  exact: Hpw _ hp.
+ by rewrite hp !mule0.
Qed.

Lemma ehl_prhl (c d: cmd) (f g f' g':cond)  P Q (ps: Y -> cmd):
  (forall m : M, 0 <= g m)%E ->
  (forall m : M, 0 <= g' m)%E ->
  ehl_ ps f' d g' ->
  @prhl_ R A B X Xg Y M ps P d c Q ->
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
