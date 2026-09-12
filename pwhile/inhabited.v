From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ==================================================================== *)
(* inhabited choiceTypes                                                *)
(* ==================================================================== *)

HB.mixin Record isInhab T of Choice T := {
  witness : T;
}.

#[short(type="inhabType")]
HB.structure Definition Inhab := { C of Choice C & isInhab C }.

HB.instance Definition bool_inhab := isInhab.Build bool false.

HB.instance Definition nat_inhab := isInhab.Build nat 0.

(* ==================================================================== *)
(* pwhile types                                                         *)
(* ==================================================================== *)

HB.mixin Record isTypeCode T of Equality T := {
  interp : T -> inhabType;            (* interpretation of a code      *)
}.

#[short(type="codeType")]
HB.structure Definition TypeCode := { T of Equality T & isTypeCode T }.

(* A code may be written wherever its interpretation is expected: [c] in type
 * position, [Distr c], [v : c].  The path is [TypeCode.sort >-> Inhab.type],
 * and [Inhab.type] carries the carrier's *own* Choice structure -- e.g.
 * [dunit 3%N : Distr (interp Cnat)] elaborates at [nat]'s own choiceType,
 * which is exactly what the [IhbType] structure could not do.
 * The coercion is keyed on [TypeCode.sort], so for a *concrete* alphabet it
 * fires only through the structure: [fun c : excode :> codeType => Distr c]. *)
Coercion interp : TypeCode.sort >-> Inhab.type.

(* -------------------------------------------------------------------- *)
Section TypeTheory.
Variable (T : codeType).

Definition type_eq_dec (c1 c2 : T) : {c1 = c2} + {c1 <> c2} :=
  match @eqP T c1 c2 with
  | ReflectT e => left e
  | ReflectF h => right h
  end.

Lemma type_eq_irrelevance (c1 c2 : T) (e1 e2 : c1 = c2) : e1 = e2.
Proof. exact: eq_irrelevance. Qed.

Lemma ecast_id (c : T) (F : T -> Type) (e : c = c) (v : F c) :
  ecast c' (F c') e v = v.
Proof. by rewrite (type_eq_irrelevance e (erefl c)). Qed.

End TypeTheory.

Arguments type_eq_dec : clear implicits.
Arguments ecast_id : clear implicits.

(* -------------------------------------------------------------------- *)
(* An example code grammar over the two level-1 instances above.  A
   client wanting products or sequences of program types adds code
   constructors ([Cprod of C & C], [Cseq of C]) and interprets them with
   mathcomp's [prod]/[seq] -- the former [prod_ihbType]/[seq_ihbType]
   instances become data rather than structure. *)
Inductive excode := Cbool | Cnat.

Definition excode_eqb (c1 c2 : excode) : bool :=
  match c1, c2 with
  | Cbool, Cbool | Cnat, Cnat => true
  | _, _ => false
  end.

Lemma excode_eqP : Equality.axiom excode_eqb.
Proof. by move=> [] [] /=; constructor. Qed.

HB.instance Definition excode_eqType := hasDecEq.Build excode excode_eqP.

Definition ex_interp (c : excode) : inhabType :=
  match c with
  | Cbool => (bool : inhabType)
  | Cnat  => (nat  : inhabType)
  end.

HB.instance Definition excode_typeCode := isTypeCode.Build excode ex_interp.

(* the interpretation, and the default it induces at each code *)
Example ex_interp_Cbool : interp Cbool = bool :> Type. Proof. by []. Qed.
Example ex_interp_Cnat  : interp Cnat  = nat  :> Type. Proof. by []. Qed.
Example ex_wit_Cbool : @witness (interp Cbool) = false. Proof. by []. Qed.
Example ex_wit_Cnat  : @witness (interp Cnat)  = 0%N.   Proof. by []. Qed.
