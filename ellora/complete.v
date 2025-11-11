(* -------------------------------------------------------------------- *)
(* ------- *)            Require Import Setoid Morphisms.
From mathcomp            Require Import all_ssreflect all_algebra.
From mathcomp.classical  Require Import boolp.
From mathcomp.reals      Require Import reals.
From mathcomp.experimental_reals Require Import  realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.
(* --------- *) Require Import range ellora sound.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope sem_scope.
Local Open Scope mem_scope.

(* -------------------------------------------------------------------- *)
Local Notation dmem  := (Distr cmem).
Local Notation dassn := (pred  dmem).

Implicit Types P Q S : dassn.
Implicit Types c : cmd.
Implicit Types mu : dmem.

(* -------------------------------------------------------------------- *)
Local Notation eqmu mu :=
  (fun x => `[< x = mu >]).

Local Notation iscomplete c :=
  (forall mu, sellora (eqmu mu) (eqmu (dssem c mu)) c)
  (only parsing).

Local Notation PRE  := (X in sellora X _)%pattern.
Local Notation POST := (X in sellora _ X)%pattern.

(* -------------------------------------------------------------------- *)
Lemma cpl_abort : iscomplete abort.
Proof.
move=> mu; apply/(@EConseq (eqmu mu) (□ pred0))=> //.
+ move=> nu /asboolP h; apply/asboolP; rewrite dssem_abortE.
  apply/distr_eqP=> m; rewrite dnullE.
  by case: (nu m =P 0)=> // /dinsuppP /h.
by apply/EAbort.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cpl_skip : iscomplete skip.
move=> mu; apply/(@EConseq (eqmu mu) (eqmu mu))=> //.
+ by move=> nu /asboolP=> ->; apply/asboolP; rewrite dssem_skipE.
by apply/ESkip.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cpl_assign {t : IhbType.type} (x : vars t) e : iscomplete (x <<- e).
Proof.
move=> mu; set Q := POST; apply/(EConseq _ _ (EAssign Q x e)) => //.
by move=> nu /asboolP ->; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cpl_sample {t : IhbType.type} (x : vars t) d : iscomplete (x <$- d).
Proof.
move=> mu; set Q := POST; apply/(EConseq _ _ (ESample Q x d)) => //.
by move=> nu /asboolP ->; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cpl_seq c1 c2 : iscomplete c1 -> iscomplete c2 -> iscomplete (c1 ;; c2).
Proof.
move=> ih1 ih2 mu; pose S x := `[<x = dssem c1 mu>].
by apply/(@ESeq S); [apply/ih1 | rewrite dssem_seqE; apply/ih2].
Qed.

(* -------------------------------------------------------------------- *)
Lemma cpl_if e c1 c2 :
  iscomplete c1 -> iscomplete c2 -> iscomplete (If e then c1 else c2).
Proof.
move=> ih1 ih2 mu; set P := PRE; set Q := POST.
pose mu1 := (drestr `[{    e }] mu).
pose mu2 := (drestr `[{ ~~ e }] mu).
pose R1 x := `[< x = dssem c1 mu1 >].
pose R2 x := `[< x = dssem c2 mu2 >].
apply/(@EConseq P (R1 ⊕ R2)) => //; first move=> nu /asboolP.
* case=> -[nu1 nu2 /= eqD] [/asboolP eq1 /asboolP eq2].
  apply/asboolP; apply/distr_eqP=> m; rewrite eqD.
  rewrite !(eq1, eq2) /dssem bsemE.
  rewrite [RHS](dlet_additive (mu1 := mu1) (mu2 := mu2)).
  - by apply/drestrD.
  congr (_ + _); apply/distr.eq_in_dlet => //.
  - by move=> m'; rewrite dinsupp_restr => /andP[_ ->].
  - move=> m'; rewrite dinsupp_restr => /andP[_ /=].
    by move/negbTE=> ->.
pose P1 x := `[< x = mu1 >]; pose P2 x := `[< x = mu2 >].
apply/(@EConseq (P1 ⊕ P2) (R1 ⊕ R2)) => //.
* move=> nu /asboolP ->; apply/asboolP; exists (mu1, mu2) => /=.
  - by apply/drestrD. - by split; apply/asboolP.
apply/(EConseq _ _ (@ECond P1 R1 P2 R2 _ _ _ _ _)) => //.
* move=> nu /asboolP[] [nu1 nu2 /= eqD] [eq1 eq2].
  apply/asboolP; exists (nu1, nu2) => //=.
  split; apply/andP; split=> //; apply/asboolP => /= m.
  - by move/asboolP: eq1=> ->; rewrite dinsupp_restr=> /andP[].
  - by move/asboolP: eq2=> ->; rewrite dinsupp_restr=> /andP[].
* apply: (EConseq _ _ (ih1 mu1)) => nu /= => [/andP[]|].
  - by move/asboolP=> -> h; apply/asboolP/distr_eqP=> m.
  by move/asboolP=> ->; apply/asboolP.
* apply: (EConseq _ _ (ih2 mu2)) => nu /= => [/andP[]|].
  - by move/asboolP=> -> h; apply/asboolP/distr_eqP=> m.
  by move/asboolP=> ->; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cpl_while e c : iscomplete c -> iscomplete (While e Do c).
Proof.
move=> cc mu; pose I n := iter n (seqc^~ (IfT e then c)) skip.
pose A n := eqmu (dssem (I n) mu).
pose B n := eqmu (dssem (I n ;; IfT e then abort) mu).
set Q := POST; apply/(EConseq _ _ (@EWhileTClosed A B Q _ _ _ _ _)).
+ move=> nu /asboolP ->; apply/asboolP=> /=.
  by rewrite /dssem !bsemE dlet_dunit_id.
+ by move=> nu /andP[].
+ move=> n; rewrite /A {2}/I; set D := dssem (iter _ _ _) _.
  suff ->: D = dssem (IfT e then c) (dssem (I n) mu).
  - by apply/cpl_if/cpl_skip=> nu; apply/cc.
  - by rewrite /D iterS dssem_seqE.
+ move=> n; rewrite /A /B; set D := dssem (_ ;; _) _.
  suff ->: D = dssem (IfT e then abort) (dssem (I n) mu).
  - by apply/cpl_if/cpl_skip=> nnu; apply/cpl_abort.
  - by rewrite /D dssem_seqE.
+ move=> nu Bnu cvg; apply/asboolP.
  pose C n := dssem (I n ;; IfT e then abort) mu.
  transitivity (\dlim_(n) C n); first apply/eq_dlim.
  * by move=> n; move/asboolP: (Bnu n) => ->.
  rewrite {}/C /dssem bsemE -dlim_let; first by apply/homo_whilen.
  apply/distr_eqP=> m; rewrite -[in RHS]dlim_bump.
  apply/distr_eqP: m; apply/eq_dlim=> n; apply/eq_in_dlet=> //.
  move=> m _; rewrite whilen_iterc; rewrite !ssemE.
  by apply/eq_in_dlet=> //; rewrite ssem_iterop_iterrev.
Qed.

(* -------------------------------------------------------------------- *)
Hint Resolve cpl_abort  : complete.
Hint Resolve cpl_skip   : complete.
Hint Resolve cpl_assign : complete.
Hint Resolve cpl_sample : complete.
Hint Resolve cpl_if     : complete.
Hint Resolve cpl_while  : complete.
Hint Resolve cpl_seq    : complete.

(* -------------------------------------------------------------------- *)
Lemma complete c mu :
  sellora (eqmu mu) (eqmu (dssem c mu)) c.
Proof. by elim: c mu; auto with complete. Qed.
