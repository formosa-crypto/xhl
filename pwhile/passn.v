(* -------------------------------------------------------------------- *)
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis  Require Import reals realsum distr.
(* ------- *)           Require Import notations.

(* -------------------------------------------------------------------- *)
CoInductive or_spec (a b : bool) : bool -> bool -> Type :=
| OrT of a    : or_spec a b true  true
| OrF of ~~ a : or_spec a b false b.

Lemma orlP a b : or_spec a b a (a || b).
Proof. by case: (boolP a) => h; constructor. Qed.

Lemma orrP a b : or_spec b a b (a || b).
Proof. rewrite orbC;apply orlP. Qed.

(* -------------------------------------------------------------------- *)
Declare Scope assn.
Delimit Scope assn with A.

Definition predImpl {T} (P Q:pred T) := 
   [pred x | P x ==> Q x].

Notation "P /\ Q"   := (predI P%A Q%A) : assn.
Notation "P \/ Q"   := (predU P%A Q%A) : assn.
Notation "P ==> Q"  := (predImpl P%A Q%A) : assn.
Notation "~ P"      := (predC P%A) : assn.

Definition predP {T : Type} (P : T -> Prop) := [pred x | `[<P x>]].

Notation "`[< P >]" := (predP P) : assn.

Definition pswap {A B : Type} (P : pred (A * B)) :=
  [pred m | P (m.2, m.1)].


