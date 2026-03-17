(* -------------------------------------------------------------------- *)

From Stdlib             Require Import Setoid Morphisms.
From mathcomp           Require Import all_ssreflect all_algebra.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope sem_scope.
Local Open Scope mem_scope.

(* -------------------------------------------------------------------- *)
Section PreCouplings.
Context {A B : choiceType} (v1 : Distr A) (v2 : Distr B)
  (f1: A -> Distr A) (f2: B -> Distr B).

Definition isprecoupling (ν : Distr (A * B)) :=
  \dlet_(m' <- dfst ν) (f1 m') = v1
  /\ \dlet_(m' <- dsnd ν) (f2 m') = v2.

End PreCouplings.

Section PreCouplingsTheory.

Section Variables.

Fixpoint fv {T : Type} (e : expr T) : set ident :=
  match e with
  | var_ T x => set1 (vname x)
  | cst_ _ _ => set0
  | prp_ _ => set0
  | app_ _ _ l r => fv l `|` fv r
  end.

Fixpoint read (c : cmd) : set ident :=
  match c with
  | abort => set0
  | skip => set0
  | assign _ _ e => fv e
  | random _ _ d => fv d
  | cond b _ _ => fv b
  | while b _ => fv b
  | seqc c1 c2 => read c1 `|` read c2
  end.

Fixpoint write (c : cmd) : set ident :=
  match c with
  | abort => set0
  | skip => set0
  | assign _ x _ => set1 (vname x)
  | random _ x _ => set1 (vname x)
  | cond _ c1 c2 => write c1 `|` write c2
  | while _ c => write c
  | seqc c1 c2 => write c1 `|` write c2
  end.

Definition disjoint_vars (A B : set ident) :=
  [disjoint A & B]
  /\ (forall (T : IhbType.type) (x : vars T), vname x \in A
      -> forall (P : pred cmem) m v, P m = P m.[x <- v]).

Lemma disjoint_exp {T : IhbType.type} (e : expr T) (x : vars T):
  disjoint_vars [set vname x] (fv e)
  -> forall m u, `[{e}] m = `[{e}] m.[x <- u].
Proof.
elim e.
+ move=> T1 y /= dv m u.
  rewrite mget_neq; last by [].
  right.
  move: dv=> [/(elimT disj_set2P) + _].
  rewrite disjoints_subset.
  move=> /(_ (vname x)) /=.
  move=> /(_ (Logic.eq_refl _)).
  admit.
+ by [].
+ move=> p [_ /(_ T x) /=].
  rewrite in_setE /=.
  by move=> /(_ (Logic.eq_refl _) p).
move=> T1 T2 e1 H1 e2 H2 /=.
move=> [/(elimT disj_set2P) /disjoints_subset Hsubs Hpred] m u.
rewrite -H2.
+ split; last exact Hpred.
  apply /(introT disj_set2P).
  rewrite disjoints_subset.
  move=> w /Hsubs.
  rewrite setCU.
  by case.
+ rewrite -H1.
  split; last exact Hpred.
  apply /(introT disj_set2P).
  rewrite disjoints_subset.
  move=> w /Hsubs.
  rewrite setCU.
  by case.
by [].
Admitted.

Lemma disjoint_cmd {T : IhbType.type} (c : cmd) (e : expr T):
  disjoint_vars (write c) (fv e)
  -> forall (m m': cmem), m' \in dinsupp (ssem c m)
  -> `[{e}] m = `[{e}] m'.
Proof.
elim c.
+ move=> _ m m'.
  rewrite ssem_abortE.
  move=> /dinsuppP.
  by rewrite dnullE.
+ move=> _ m m'.
  rewrite ssem_skipE.
  by move=> /in_dunit ->.
+ move=> t.
  have <-: T = t.
  + admit.
  move=> y e1 /=.
  move=> H m m'.
  rewrite ssem_assnE.
  move=> /in_dunit ->.
  exact /disjoint_exp/H.
+ move=> t. 
  have <-: T = t.
  + admit.
  move=> y e1.
  move=> H m m'.
  rewrite ssem_rndE.
  move=> /dinsupp_dlet [u] _.
  rewrite dunit1E.
  move=> H2.
  have ->: m' = m.[y <- u].
  + admit.
  exact /disjoint_exp/H.
+ move=> e1 c0 Hl c1 Hr.
  move=> [/(elimT disj_set2P) /disjoints_subset /= + Hpred] m m'.
  rewrite subUset.
  move=> [Hsubl Hsubr].
  rewrite ssem_ifE.
  case (`[{e1}] m).
  + apply Hl.
    split.
    + apply /(introT disj_set2P).
      rewrite disjoints_subset.
      by move=> w /Hsubl.
    move=> T0 x A.
    apply Hpred.
    by rewrite in_setU A.
  + apply Hr.
    split.
    + apply /(introT disj_set2P).
      rewrite disjoints_subset.
      by move=> w /Hsubr.
    move=> T0 x A.
    apply Hpred.
    rewrite in_setU.
    by rewrite A orbT.
+ move=> e1 c0 IH.
  move=> [/= Hdisj Hpred] m m'.
  rewrite ssem_whileE.
  move=> /dinsupp_dlim [k].
  case k.
  + move=> /=.
    rewrite ssem_abortE.
    move=> /dinsuppP.
    by rewrite dnullE.
  move=> n.
  rewrite whilen_iterc.
  rewrite ssem_seqE.
  move=> /dinsupp_dlet [m1].
  rewrite ssem_ifE ssem_abortE ssem_skipE -in_dinsupp.
  case (`[{e1}] m1).
  + move=> _ /dinsuppP.
    by rewrite dnullE.
  move=> + /in_dunit ->.
  move: m1.
  elim n.
  + move=> m1.
    rewrite iterc0 ssem_skipE.
    by move=> /in_dunit ->.
  move=> n0 IH2 m1.
  rewrite itercSr ssem_seqE.
  move=> /dinsupp_dlet [m2] /IH2 H2.
  rewrite ssem_ifE -in_dinsupp ssem_skipE.
  case (`[{e1}] m2); last first.
  + by move=> /in_dunit ->.
  rewrite {}H2.
  apply IH.
  by split; last exact Hpred.
move=> c0 Hl c1 Hr.
move=> [/(elimT disj_set2P) /disjoints_subset /= + Hpred] m m'.
rewrite subUset.
move=> [Hsubl Hsubr].
rewrite ssem_seqE.
move=> /dinsupp_dlet [m1] /Hl m1v.
rewrite -in_dinsupp=> H.
have Hdisjl: disjoint_vars (write c0) (fv e).
+ split.
  + apply /(introT disj_set2P).
    rewrite disjoints_subset.
    by move=> w /Hsubl.
  move=> T0 x A.
  apply Hpred.
  by rewrite in_setU A.
have Hdisjr: disjoint_vars (write c1) (fv e).
+ split.
  + apply /(introT disj_set2P).
    rewrite disjoints_subset.
    by move=> w /Hsubr.
  move=> T0 x A.
  apply Hpred.
  by rewrite in_setU A orbT.
move: (Hr Hdisjr m1 m' H)=> <-.
exact (m1v Hdisjl).
Admitted.

End Variables.

Context {A B C D : choiceType}.

Lemma isprecoupling_dlet
  (u1 u2 : Distr _) (f1 f2 : _ -> Distr _) (u: Distr (A * B))
  (v1 v2 : _ -> Distr _) (g1 g2 : _ -> Distr _) (v: _ -> Distr (C * D)) :
  isprecoupling u1 u2 f1 f2 u
  -> (forall x, x \in dinsupp u ->
    isprecoupling (\dlet_(y <- f1 x.1) (v1 y)) (\dlet_(y <- f2 x.2) (v2 y)) g1 g2 (v x))
    -> isprecoupling
      (\dlet_(x <- u1) (v1 x))
      (\dlet_(x <- u2) (v2 x))
      g1 g2
      (\dlet_(x <- u) (v x)).
Proof.
move=> [eq1 eq2] hC.
subst u1 u2.
split.
+ rewrite dlet_dmargin !dlet_dlet.
  apply: eq_in_dlet => // y /hC [+ _].
  by rewrite dlet_dmargin dlet_unit.
rewrite dlet_dmargin !dlet_dlet.
apply: eq_in_dlet => // y /hC [_ +].
by rewrite dlet_dmargin dlet_unit.
Qed.

End PreCouplingsTheory.

(* -------------------------------------------------------------------- *)
Implicit Types P Q R I : rassn.
Implicit Types c r s t : cmd.

(* -------------------------------------------------------------------- *)
Definition dprhl P r1 r2 c1 c2 s1 s2 Q :=
  forall m : rmem, P m ->
                   exists2 ν,
  isprecoupling
    (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2)
    (ssem s1) (ssem s2)
    ν
  & range Q ν.

Lemma dprhlw P r1 r2 c1 c2 s1 s2 Q m :
  dprhl P r1 r2 c1 c2 s1 s2 Q -> P m ->
    { ν | isprecoupling (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2) (ssem s1) (ssem s2) ν & range Q ν }.
Proof.
move=> h Pm.
have: exists ν, 
  isprecoupling (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2) (ssem s1) (ssem s2) ν
  /\ range Q ν.
+ by case: (h _ Pm) => ν h1 h2; exists ν; split.
by case/cid=> ν [h1 h2]; exists ν.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_sem P r1 r2 r'1 r'2 c1 c2 c'1 c'2 s1 s2 s'1 s'2 Q :
  r1 =C r'1
  -> r2 =C r'2
  -> c1 =C c'1
  -> c2 =C c'2
  -> s1 =C s'1
  -> s2 =C s'2
  -> dprhl P r'1 r'2 c'1 c'2 s'1 s'2 Q
  -> dprhl P r1 r2 c1 c2 s1 s2 Q.
Proof.
move=> eq1 eq2 eq3 eq4 eq5 eq6 h m Pm.
case: (h _ Pm).
move=> x.
rewrite !ssemE /isprecoupling !dlet_dmargin eq1 eq2.
move=> [hCl hCr hR].
exists x => //.
rewrite !dlet_dmargin.
under [\dlet_(m' <- ssem r'1 _) _]eq_in_dlet => [? _ |] do [rewrite eq3|].
under [\dlet_(m' <- ssem r'2 _) _]eq_in_dlet => [? _ |] do [rewrite eq4|].
under eq_in_dlet => [? _ |] do [rewrite eq5|].
under [X in _ /\ X = _]eq_in_dlet => [? _ |] do [rewrite eq6|].
by [].
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_skip P r1 r2 Q:
  (forall m : rmem, P m -> Q m)
  -> dprhl P r1 r2 skip skip r1 r2 Q.
Proof.
move=> H1 m H2.
exists (dunit m).
+ by split; rewrite dmargin_dunit dlet_unit seq_skip_r.
by apply/range_dunit/H1/H2.
Qed.

Lemma dprhl_seq P r1 r2 c1 c2 R t1 t2 c1' c2' s1 s2 Q:
  dprhl P r1 r2 c1 c2 t1 t2 R
  -> dprhl R t1 t2 c1' c2' s1 s2 Q
  -> dprhl P r1 r2 (c1 ;; c1') (c2 ;; c2') s1 s2 Q.
Proof.
move=> h1 h2 m Pm.
case: (h1 _ Pm) => ν hC hR.
pose f m :=
  if @idP (m \in dinsupp ν) is ReflectT Rm then
    tag (dprhlw h2 (hR _ Rm))
  else dnull.
exists (\dlet_(m <- ν) f m); last first.
+ apply: (range_dlet hR) => m' Rm'; rewrite /f.
  case: {-}_ / idP; first by move=> p; case: dprhlw.
  by move=> _ x /dinsuppP; rewrite dnullE.
rewrite 2!seqA ssem_seqE [ssem (r2 ;; c2 ;; c2') _]ssem_seqE. 
apply: isprecoupling_dlet; first exact hC.
move=> m' hm'; rewrite /f; case: {-}_ / idP => //.
move=> p; case: dprhlw.
by rewrite !ssemE.
Qed.

Lemma dprhl_assignL {T : IhbType.type} Q r1 r'1 r2 (x : vars T) (e : expr T) :
  (forall m, ssem r'1 m = ssem r1 m.[x <- `[{ e }] m])
  -> disjoint_vars (write r1) ([set vname x] `|` fv e)
  -> dprhl [pred m : rmem | Q m.[~1 x <- `[{ e }] m.1]] r'1 r2 (x <<- e) skip r1 r2 Q.
Proof.
move=> Heq Hwrite.
move=> m /= Qmxe; exists (dunit (m.[~1 x <- `[{ e }] m.1])); last first.
+ by apply/range_dunit.
split.
+ rewrite dlet_dmargin dlet_unit.
  rewrite ssem_seqE Heq.
  rewrite -/(mselect '1 _) mselect_mset /=.
  under eq_in_dlet => [? _|] do [rewrite ssem_assnE|].
Admitted.

Lemma dprhl_if P e1 e2 c1 c'1 c2 c'2 Q r1 r2 s1 s2:
  write r1 `&` fv e1 == set0
  -> write r2 `&` fv e2 == set0
  -> dprhl (P /\ `[{    e1#'1 &&    e2#'2 }])%A r1 r2 c1  c2  s1 s2 Q
  -> dprhl (P /\ `[{ ~~ e1#'1 && ~~ e2#'2 }])%A r1 r2 c'1 c'2 s1 s2 Q
  -> dprhl (P /\ `[{ e1#'1 =b e2#'2 }])%A r1 r2
       (If e1 then c1 else c'1)
       (If e2 then c2 else c'2)
       s1 s2 Q.
Proof.
Admitted.

Lemma dprhl_seqL1 P r1 r2 c1 c2 R t1 t2 c1' s1 s2 Q:
  dprhl P r1 r2 c1 skip t1 t2 R
  -> dprhl R t1 t2 c1' c2 s1 s2 Q
  -> dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q.
Proof.
move=> Htop Hbot.
apply: dprhl_sem; last first.
apply: dprhl_seq.
+ exact Htop.
+ exact Hbot.
+ by [].
+ by [].
+ by rewrite seq_skip_l.
+ by [].
+ by [].
by [].
Qed.

Lemma dprhl_seqL2 P r1 r2 c1 c2 R t1 t2 c1' s1 s2 Q:
  dprhl P r1 r2 c1 c2 t1 t2 R
  -> dprhl R t1 t2 c1' skip s1 s2 Q
  -> dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q.
Proof.
move=> Htop Hbot.
apply: dprhl_sem; last first.
apply: dprhl_seq.
+ exact Htop.
+ exact Hbot.
+ by [].
+ by [].
+ by rewrite seq_skip_r.
+ by [].
+ by [].
by [].
Qed.

(* -------------------------------------------------------------------- *)
(* Structural Rules *)

Lemma dprhl_pushL Q r1 r2 c1 c2:
  dprhl Q r1 r2 c1 c2 (r1 ;; c1) (r2 ;; c2) Q.
Proof.
move=> m Qm.
exists (dunit m).
+ by split; rewrite dmargin_dunit dlet_unit.
by apply: range_dunit.
Qed.

Lemma dprhl_popL P r1 r2 c1 c1' c2 s1 s2 Q:
  dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q
  <->
  dprhl P (r1 ;; c1) r2 c1' c2 s1 s2 Q.
Proof.
by split; move=> H m {}/H; rewrite seqA.
Qed.

Lemma dprhl_case P A r1 r2 c1 c2 s1 s2 Q :
     dprhl (P /\   A)%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl (P /\ ~ A)%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl P r1 r2 c1 c2 s1 s2 Q.
Proof.
move=> hA hNA m Pm; case/boolP: (A m) => [Am | NAm].
+ by apply/hA; rewrite -(rwP andP).
+ by apply/hNA; rewrite -(rwP andP).
Qed.
