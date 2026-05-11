(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
(* ----------------- *) Require Import notations inhabited pwhile psemantic passn.

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
Definition range {A : choiceType} (P : pred A) (mu : Distr A) :=
  forall m, m \in dinsupp mu -> P m.

Section Range.
Context {A B : choiceType}.

Lemma range_dnull (P : pred A) : range P dnull.
Proof. by move=> x /dinsuppP; rewrite dnullE. Qed.

Lemma range_dunit (P: pred A) m : P m -> range P (dunit m).
Proof. by move=> Pm m' /in_dunit ->. Qed.

Lemma range_dlet (PA : pred A) (PB : pred B) mu f :
    range PA mu -> (forall m, PA m -> range PB (f m))
  -> range PB (\dlet_(m <- mu) f m).
Proof. by move=> hA hB y /dinsupp_dlet[x] /hA /hB /(_ y). Qed.

Lemma dinsupp_dlim (mu : nat -> Distr A) x:
  x \in dinsupp (\dlim_(n) mu n) ->
    exists k, x \in dinsupp (mu k).
Proof.
move/dinsuppP; rewrite dlimE; apply: contra_notP.
move/asboolPn/forallp_asboolPn => eq; rewrite (@eq_nlim _ (fun _ => 0)).
  by move=> n; apply/dinsuppPn/negP/eq.
  by rewrite nlimC.
Qed.

Lemma range_dlim P (mu : nat -> Distr A):
  (forall n, range P (mu n)) -> range P (dlim mu).
Proof. by move=> h m /dinsupp_dlim[k] /h. Qed.
 
Lemma range_weaken (P1 P2 : pred A) mu:
  (forall x, P1 x -> P2 x) ->
  range P1 mu -> range P2 mu.
Proof. by move=> imp_P h m /h /imp_P. Qed.

Lemma range_pswap (P : pred (A * B)) (mu : Distr (A * B)) :
  range P mu -> range (pswap P) (dswap mu).
Proof.
move=> h [m1 m2] m_in_mu; have := h (m2, m1); apply.
by apply/dinsuppP; rewrite -dswapK; apply/dinsuppP/dinsupp_swap.
Qed.

Lemma pr_range (mu : Distr A) (E : pred A) :
  \P_[mu] (~ E)%A = 0 <-> range E mu.
Proof. 
  split.
  + by move=> /pr_eq0 h x; apply/contraLR => /h /dinsuppPn. 
  rewrite /range -(pr_pred0 mu)=> Hin;apply eq_in_pr=> x /Hin.
  by rewrite /mem /= /in_mem /= => ->.   (* TODO: simplify this *)
Qed.
End Range.
