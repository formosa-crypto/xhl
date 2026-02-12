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
Section Couplings.
  Context {A B : choiceType} (μ1 : Distr A) (μ2 : Distr B)
    (f1: A -> Distr A) (f2: B -> Distr B).

  Definition iscoupling (ν : Distr (A * B)) :=
    \dlet_(m' <- dfst ν) (f1 m') = μ1 /\
      \dlet_(m' <- dsnd ν) (f2 m')= μ2.
End Couplings.

(* -------------------------------------------------------------------- *)
(* Section CouplingsTheory. *)
(* Context {A B C D : choiceType}. *)

(* Lemma iscoupling_eq (μ1 μ2 μ1' μ2' : Distr _) (ν : Distr (A * B)) : *)
(*   μ1 =1 μ1' -> μ2 =1 μ2' -> iscoupling μ1 μ2 ν -> iscoupling μ1' μ2' ν. *)
(* Proof. by do 2! move=> /distr_eqP->. Qed. *)

(* Lemma iscoupling_prod (μ : Distr (A * B)) : *)
(*   iscoupling (dfst μ) (dsnd μ) μ. *)
(* Proof. by []. Qed. *)

(* Lemma iscoupling_dnull : @iscoupling A B dnull dnull dnull. *)
(* Proof. by split; rewrite dmarginE dlet_null. Qed. *)

(* Lemma iscoupling_dunit a b : *)
(*   @iscoupling A B (dunit a) (dunit b) (dunit (a, b)). *)
(* Proof. by split; rewrite dmarginE dlet_unit. Qed. *)

(* Lemma iscoupling_swap (μ1 μ2 : Distr A) (ν : Distr (A * A)) : *)
(*   iscoupling μ1 μ2 ν -> iscoupling μ2 μ1 (dswap ν). *)
(* Proof. *)
(* case=> <- <-; split; apply/distr_eqP => m; *)
(*   by rewrite (dfst_dswap, dsnd_dswap). *)
(* Qed. *)

(* Lemma iscoupling_dlet *)
(*   (μ1 μ2 : Distr _) (ν : Distr (A * B)) *)
(*   (θ1 θ2 : _ -> Distr _) (ν' : _ -> Distr (C * D)) : *)

(*      iscoupling μ1 μ2 ν *)
(*   -> (forall x, x \in dinsupp ν -> *)
(*         iscoupling (θ1 x.1) (θ2 x.2) (ν' x)) *)
(*   -> iscoupling *)
(*        (\dlet_(x <- μ1) (θ1 x)) *)
(*        (\dlet_(x <- μ2) (θ2 x)) *)
(*        (\dlet_(x <- ν ) (ν' x)). *)
(* Proof. *)
(* move=> [eq1 eq2] hC; split; rewrite !dmargin_dlet; subst μ1 μ2. *)
(* + by rewrite dlet_dmargin; apply/eq_in_dlet => // x /hC [<- _]. *)
(* + by rewrite dlet_dmargin; apply/eq_in_dlet => // x /hC [_ <-]. *)
(* Qed. *)

(* Lemma iscoupling_dlim *)
(*   (μ1 μ2 : nat -> Distr _) (ν : nat -> Distr (A * B)) : *)

(*      (forall n, iscoupling (μ1 n) (μ2 n) (ν n)) *)
(*   -> (forall n m, (n <= m)%N -> ν n <=1 ν m) *)
(*   -> iscoupling (dlim μ1) (dlim μ2) (dlim ν). *)
(* Proof. *)
(* move=> hC mono; rewrite /iscoupling !dmarginE !dlet_lim //. *)
(* by split; apply/eq_dlim => n; case: (hC n). *)
(* Qed. *)
(* End CouplingsTheory. *)

(* -------------------------------------------------------------------- *)
Implicit Types P Q S I : rassn.
Implicit Types c r s      : cmd.

(* -------------------------------------------------------------------- *)
Definition prhl P c1 c2 r1 r2 s1 s2 Q :=
  forall m : rmem, P m ->
                   exists2 ν,
  iscoupling
    (ssem_aux (seqc r1 c1) m.1)
    (ssem_aux (seqc r2 c2) m.2)
    (ssem_aux s1)
    (ssem_aux s2) ν
  & range Q ν.
