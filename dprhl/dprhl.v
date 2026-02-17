(* -------------------------------------------------------------------- *)
From Stdlib             Require Import Setoid Morphisms.
From mathcomp           Require Import all_ssreflect all_algebra.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import boolp.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

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
  apply /eq_in_dlet => // y /hC [].
  by rewrite dlet_dmargin dlet_unit.
rewrite dlet_dmargin !dlet_dlet.
apply /eq_in_dlet => // y /hC [].
by rewrite !dlet_dmargin dlet_unit.
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
+ apply/(range_dlet hR) => m' Rm'; rewrite /f.
  case: {-} _ /idP; first by move=> p; case: dprhlw.
  by move=> _ x /dinsuppP; rewrite dnullE.
rewrite 2!seqA ssem_seqE [ssem (r2 ;; c2 ;; c2') _]ssem_seqE. 
apply: isprecoupling_dlet.
+ exact hC.
move=> m' hm'; rewrite /f; case: {-}_ / idP => //.
move=> p; case: dprhlw.
by rewrite !ssemE.
Qed.
