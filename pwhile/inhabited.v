(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
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
HB.mixin Record IsInhabited T := {
  witness : T
}.

(* [Choice] is deliberately *not* part of this class.  Storing a mathcomp
 * mixin here makes [IhbType.type] live strictly above the universe of
 * eqType carriers:
 *
 *   Equality.axioms_.u0 < PredOfSimpl.coerce.u0
 *                      <= IhbType.axioms_.u1 <= IhbType.type.u0
 *
 * and then neither [IhbType.type] nor anything quantifying over it can be
 * given an eq/choice structure.  Concretely, with [Choice T] in the class:
 *
 *   - [hasDecEq.Build IhbType.type _] silently generates nothing (HB says
 *     "no new instance is generated") and [existT_inj2], which is stated
 *     for an eqType index, no longer applies in [eq_vars];
 *   - [coremem], which quantifies over [IhbType.type], cannot be a
 *     choiceType, so [Choice.clone coremem _] in [pwhile.v] fails with a
 *     universe inconsistency, and with it [cmem] and [Distr cmem].
 *
 * The carriers get their eq/choice structures classically, just below. *)
HB.structure Definition IhbType := { T of IsInhabited T }.

Arguments witness : clear implicits.

(* -------------------------------------------------------------------- *)
Lemma comparable_ihbtype : comparable IhbType.type.
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition ihbtype_eqType :=
  hasDecEq.Build IhbType.type (compareP comparable_ihbtype).

HB.instance Definition ihbtype_choiceType :=
  gen_choiceMixin IhbType.type.

(* -------------------------------------------------------------------- *)
(* Every inhabited type is classically an eqType and a choiceType.  These
 * instances are non-forgetful: for a concrete carrier they are *not* that
 * type's own structure.  Below, [N := (nat : IhbType.type)], i.e. [nat]
 * seen as a program type.
 *
 * (1) Two different [==] on the same carrier.
 *
 *       Goal forall x y : N, (x == y) = (x == y :> nat).
 *       Proof. Fail by []. Abort.            (* No applicable tactic *)
 *
 *     They are provably equal but not convertible -- they are literally
 *     different structures:
 *
 *       fun x y : N   => @eq_op (IhbType_sort__canonical__eqtype_Equality nat) x y
 *       fun x y : nat => @eq_op Datatypes_nat__canonical__eqtype_Equality x y
 *
 * (2) The dangerous one: a goal that *displays* as a tautology but is not.
 *
 *       Goal forall x y : N, (x.+1 == y.+1) = (x == y).
 *       Proof. move=> x y; rewrite eqSS.
 *
 *     [rewrite eqSS] succeeds: [x.+1] has type [nat] on the nose
 *     ([S : nat -> nat]), so that side elaborated with nat's own eqType,
 *     while the other side used the classical one.  The goal then prints as
 *
 *       (x == y) = (x == y)
 *
 *     yet [by []] fails, and [Set Printing All] shows why:
 *
 *       @eq bool (@eq_op Datatypes_nat__canonical__eqtype_Equality x y)
 *                (@eq_op (IhbType_sort__canonical__eqtype_Equality nat) x y)
 *
 *     This is the failure mode to watch for: invisible in the printed goal,
 *     noticed only when a [by []]/[exact] inexplicably fails.  Closing such
 *     a goal needs [apply/idP/idP] + [eqP], or [rewrite (rwP eqP)].
 *
 * (3) A program cannot sample a standard-library distribution.
 *
 *       Definition xv : vars N := Var N i.
 *       Check (dunit 3%N : {distr nat / R}).      (* fine *)
 *       Fail Check (xv <$- (dunit 3%N)%:S)%S.
 *
 *       The term "(dunit (T:=Datatypes_nat__canonical__choice_Choice) 3%N)%:S"
 *       has type "expr_ ident ?mem (Distr Datatypes_nat__canonical__choice_Choice)"
 *       while it is expected to have type "expr_ ident ?mem (Distr nat)"
 *       (cannot unify "Datatypes_nat__canonical__choice_Choice" and
 *        "reverse_coercion (IhbType_sort__canonical__choice_Choice nat) nat").
 *
 *     Workaround: build program distributions at the [IhbType] carrier,
 *
 *       Check (xv <$- (dunit (T := N) 3%N)%:S)%S.  (* accepted *)
 *
 * What is NOT affected: lemmas generic in an eqType/choiceType transfer
 * fine, since they are instantiated at whichever structure is in play --
 * [exact: mem_head] closes [v \in v :: s] for [s : seq N], and [eqxx],
 * [dunit1E], [dlet_dlet], [range_dunit] apply unchanged.  That is why all
 * of pwhile.v compiles and why nothing in hl/ or ehl/ trips today: every
 * [dunit]/[dlet] there is at memory type or generic.
 *
 * The breakage is confined to *type-specific* facts meeting a program
 * value: [eqSS], [eqn], [ltn_eqF], [mem_iota], anything about nat's or
 * int's own [==], and any concrete distribution built outside the
 * [IhbType] lens.  Rules of thumb: annotate concrete distributions with
 * [(T := (tau : IhbType.type))], and when a [by []] fails on a goal that
 * looks trivially reflexive, check it with [Set Printing All] before
 * believing the display.  If that discipline costs more than it saves,
 * switch to the FALLBACK below, which removes the issue entirely. *)
#[non_forgetful_inheritance]
HB.instance Definition ihb_carrier_eqType (T : IhbType.type) :=
  gen_eqMixin T.

#[non_forgetful_inheritance]
HB.instance Definition ihb_carrier_choiceType (T : IhbType.type) :=
  gen_choiceMixin T.

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

(* -------------------------------------------------------------------- *)

(* FALLBACK, if the non-forgetful instances above ever become painful (a
 * program at a concrete type whose own eq/choice structure must meet the
 * one seen through [IhbType]): replace the structure by a small inductive
 * of type *codes* interpreted into genuine mathcomp structures.  Codes are
 * an eqType by construction and live in [Set], so [coremem] and friends
 * stay small, while each interpretation keeps the carrier's own structure
 * -- no non-forgetful inheritance at all.  The price is that the set of
 * program types is closed to the grammar below.
 *
 * Keeping the module name [IhbType] means the spelling [IhbType.type] used
 * throughout hl/, ehl/, phl/, prhl/, ellora/ and psemantic.v stays valid,
 * so only this file and two lines of pwhile.v change ([Parameter R] moves
 * here, and the [real_ihbType] instance goes away).
 *
 *   Parameter R : realType.  (* moved from pwhile.v, for the [Real] code *)
 *
 *   Module IhbType.
 *   Inductive type :=
 *   | Unit | Bool | Nat | Int | Real
 *   | Prod of type & type
 *   | Seq  of type.
 *   End IhbType.
 *
 *   Notation ihbType := IhbType.type.
 *
 *   Fixpoint ihb_eqb (c1 c2 : ihbType) : bool :=
 *     match c1, c2 with
 *     | IhbType.Unit, IhbType.Unit | IhbType.Bool, IhbType.Bool
 *     | IhbType.Nat , IhbType.Nat  | IhbType.Int , IhbType.Int
 *     | IhbType.Real, IhbType.Real => true
 *     | IhbType.Prod a b, IhbType.Prod a2 b2 => ihb_eqb a a2 && ihb_eqb b b2
 *     | IhbType.Seq  a  , IhbType.Seq  a2    => ihb_eqb a a2
 *     | _, _ => false
 *     end.
 *
 *   Lemma ihb_eqb_refl c : ihb_eqb c c.
 *   Proof. by elim: c => [|||||a ha b hb|a ha] //=; rewrite ?ha ?hb. Qed.
 *
 *   Lemma ihb_eqb_eq c1 c2 : ihb_eqb c1 c2 -> c1 = c2.
 *   Proof.
 *   elim: c1 c2 => [|||||a iha b ihb|a iha] [|||||a2 b2|a2] //=.
 *   - by case/andP=> /iha-> /ihb->.
 *   - by move/iha->.
 *   Qed.
 *
 *   Lemma ihb_eqP : Equality.axiom ihb_eqb.
 *   Proof.
 *   by move=> x y; apply: (iffP idP) => [/ihb_eqb_eq//|->]; apply: ihb_eqb_refl.
 *   Qed.
 *
 *   HB.instance Definition _ := hasDecEq.Build ihbType ihb_eqP.
 *
 *   (* the interpretation returns *genuine* mathcomp structures *)
 *   Fixpoint ihb_choice (c : ihbType) : choiceType :=
 *     match c with
 *     | IhbType.Unit => unit
 *     | IhbType.Bool => bool
 *     | IhbType.Nat  => nat
 *     | IhbType.Int  => int
 *     | IhbType.Real => R
 *     | IhbType.Prod a b => (ihb_choice a * ihb_choice b)%type
 *     | IhbType.Seq  a   => seq.seq (ihb_choice a)
 *     end.
 *
 *   Definition ihb_sort (c : ihbType) : Type := ihb_choice c.
 *   Coercion ihb_sort : ihbType >-> Sortclass.
 *
 *   (* this is what makes [Distr T] elaborate for a *generic* code T: the
 *    * canonical structure is keyed on the constant [ihb_sort] *)
 *   HB.instance Definition _ (c : ihbType) :=
 *     Choice.copy (ihb_sort c) (ihb_choice c).
 *
 *   Fixpoint witness (c : ihbType) : c :=
 *     match c with
 *     | IhbType.Unit => tt | IhbType.Bool => false | IhbType.Nat => 0%N
 *     | IhbType.Int => 0 | IhbType.Real => 0
 *     | IhbType.Prod a b => (witness a, witness b)
 *     | IhbType.Seq  a   => [::]
 *     end.
 *
 *   Definition ihb_eq_dec (c1 c2 : ihbType) : {c1 = c2} + {c1 <> c2} :=
 *     decP (c1 =P c2).
 *
 * Checked on a prototype: [{c : ihbType & vars c} : eqType],
 * [dunit 3%N : Distr IhbType.Nat], [Distr IhbType.Nat] and [{distr nat / R}]
 * convert both ways, [IhbType.Nat = nat :> Type] by [erefl], and nat lemmas
 * rewrite through it ([rewrite eqSS] on [x y : IhbType.Nat]). *)
