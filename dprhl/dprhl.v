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
