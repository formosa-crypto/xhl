(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import all_boot all_order.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope nat_scope.

(* -------------------------------------------------------------------- *)
HB.mixin Record IsInhabited T of Choice T := {
  witness : T
}.

HB.structure Definition IhbType := { T of IsInhabited T & Choice T}.

Arguments witness : clear implicits.

HB.instance Definition _ :=
(@comparableMixin IhbType.type (fun x y => pselect (x = y))).

(* -------------------------------------------------------------------- *)
HB.instance Definition unit_ihbType :=
  IsInhabited.Build unit tt.

(* -------------------------------------------------------------------- *)
HB.instance Definition nat_ihbType :=
  IsInhabited.Build nat 0%N.

(* -------------------------------------------------------------------- *)
HB.instance Definition prod_ihbType (T U : IhbType.type) :=
  IsInhabited.Build (T * U)%type (witness T, witness U).

(* -------------------------------------------------------------------- *)
HB.instance Definition int_ihbType :=
  IsInhabited.Build int 0.

(* -------------------------------------------------------------------- *)
HB.instance Definition seq_ihbType (T : IhbType.type) :=
   IsInhabited.Build (seq.seq T) [::].
