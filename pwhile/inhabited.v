(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.reals     Require Import reals.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* inhabited choiceTypes                                                *)
(* -------------------------------------------------------------------- *)

HB.mixin Record isInhab T of Choice T := {
  witness : T;
}.

#[short(type="inhabType")]
HB.structure Definition Inhab := { C of Choice C & isInhab C }.

HB.instance Definition bool_inhab := isInhab.Build bool false.

HB.instance Definition nat_inhab := isInhab.Build nat 0.

HB.instance Definition int_inhab := isInhab.Build int 0.

HB.instance Definition seq_inhab (T : Inhab.type) := isInhab.Build (seq.seq T) [::].

(* -------------------------------------------------------------------- *)
(* pwhile types                                                         *)
(* -------------------------------------------------------------------- *)

HB.mixin Record isTypeCode T of Equality T := {
  interp : T -> inhabType;
}.

#[short(type="codeType")]
HB.structure Definition TypeCode := { T of Equality T & isTypeCode T }.

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
Section example.

Inductive excode := Cbool | Cnat | Cint | Cseq (c :excode).

Fixpoint excode_eqb (c1 c2 : excode) : bool :=
  match c1, c2 with
  | Cbool, Cbool | Cnat, Cnat | Cint, Cint => true
  | Cseq t1, Cseq t2 => excode_eqb t1 t2
  | _, _ => false
  end.

Lemma excode_eqP : Equality.axiom excode_eqb.
Proof.
  elim => [||| t1 ih] [||| t2] /=; try by constructor.
  by apply : (iffP (ih t2))=>  [ -> | []].
Qed.

HB.instance Definition excode_eqType := hasDecEq.Build excode excode_eqP.

Fixpoint ex_interp (t : excode) : inhabType :=
  match t with
  | Cbool => (bool : inhabType)
  | Cnat  => (nat  : inhabType)
  | Cint => (int: inhabType)
  | Cseq t => seq.seq (ex_interp t)
  end.

HB.instance Definition excode_typeCode := isTypeCode.Build excode ex_interp.

Example ex_interp_Cbool : interp Cbool = bool :> Type. Proof. by []. Qed.
Example ex_interp_Cnat  : interp Cnat  = nat  :> Type. Proof. by []. Qed.
Example ex_interp_Cint : interp Cint = int :> Type. Proof. by []. Qed.
Example ex_interp_Cseq  : interp (Cseq Cint)  = seq.seq int  :> Type. Proof. by []. Qed.

Example ex_wit_Cbool : @witness (interp Cbool) = false. Proof. by []. Qed.
Example ex_wit_Cnat  : @witness (interp Cnat)  = 0%N.   Proof. by []. Qed.
Example ex_wit_Cint  : @witness (interp Cint)  = 0.   Proof. by []. Qed.
Example ex_wit_Cseq  : @witness (interp (Cseq Cint))  = [::]. Proof. by []. Qed.

End example.
