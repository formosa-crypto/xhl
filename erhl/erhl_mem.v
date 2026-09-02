From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp.analysis  Require Import sequences normedtype topology.
From mathcomp           Require finmap.

From xhl.pwhile         Require Import notations inhabited mem pwhile psemantic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
HB.mixin Record isMemExt (A B : codeType) (mident midentg : eqType) M
    of Choice M & isMemType A B mident midentg M := {
  mset_eq_ : forall (T : A) (m : M) (x : mident), mset_ m T x (mget_ m T x) = m;
}.

#[short(type="erhlMemType")]
HB.structure Definition ErhlMemType (A B : codeType) (mident midentg : eqType) :=
  { M of Choice M & isMemType A B mident midentg M & isMemExt A B mident midentg M }.

Section ErhlMemTheory.
Variable (A B : codeType) (mident midentg : eqType).
Variable (M : erhlMemType A B mident midentg) (T : A).

Lemma mset_eq (m : M) (x : mident) : mset m x (mget T m x) = m.
Proof. by unlock mget mset; apply/mset_eq_. Qed.

End ErhlMemTheory.

(* -------------------------------------------------------------------- *)
Section ConcreteExt.
Variable (A B : codeType) (ident identg : eqType).

Lemma set_get_eq {T : A} (m : coremem A B ident identg) (x : ident) :
  coremem_set m x (m T x) = m.
Proof. by rewrite /coremem_set hupd_id; case: m. Qed.

HB.instance Definition coremem_memExt :=
  isMemExt.Build A B ident identg (coremem A B ident identg) (@set_get_eq).

Definition ecmem : erhlMemType A B ident identg := coremem A B ident identg.

End ConcreteExt.

(* -------------------------------------------------------------------- *)
Section RelaMemExt.
Variable (A B : codeType) (X Xg : eqType) (M : erhlMemType A B X Xg).

Lemma set_get2_eq {T : A} (m : coremem2 M) (x : rident X) :
  coremem2_set m x (coremem2_get m T x) = m.
Proof.
by case: m x => m1 m2 [x []]; rewrite /coremem2_set /coremem2_get /= mset_eq.
Qed.

HB.instance Definition coremem2_memExt :=
  isMemExt.Build A B (rident X) (ridentg Xg) (coremem2 M) (@set_get2_eq).

Definition ermem : erhlMemType A B (rident X) (ridentg Xg) := coremem2 M.

End RelaMemExt.

Arguments ermem : clear implicits.
Arguments ermem : simpl never.

(* -------------------------------------------------------------------- *)
Section Mem_misc.
Context {A B : codeType} {X Xg : eqType} {M : erhlMemType A B X Xg}.

Local Notation rmem  := (rmem A B X Xg M).
Local Notation vars  := (vars_ X).
Local Notation gvars := (vars_ Xg).

Lemma mselect_msetg {T : B} s s' (m : rmem) (x : gvars T) (v : T) :
  ((m.{x#g s <- v})#s')%M = if s == s' then ((m#s).{x <- v})%M else (m#s')%M.
Proof. by case: s s' x => [] [] []. Qed.

Lemma rmset1E {T : A} (m : rmem) (x : vars T) (v : T) :
  (m.[~1 x <- v])%M = (((m.1).[x <- v])%M, m.2).
Proof. by rewrite mset_iE. Qed.

Lemma rmset2E {T : A} (m : rmem) (x : vars T) (v : T) :
  (m.[~2 x <- v])%M = (m.1, ((m.2).[x <- v])%M).
Proof. by rewrite mset_iE. Qed.

Lemma rmset_get1 {T : A} (m : rmem) (x : vars T) :
  (m.[~1 x <- ((m.1).[x])%M])%M = m.
Proof. by rewrite rmset1E mset_eq -surjective_pairing. Qed.

Lemma rmset_get2 {T : A} (m : rmem) (x : vars T) :
  (m.[~2 x <- ((m.2).[x])%M])%M = m.
Proof. by rewrite rmset2E mset_eq -surjective_pairing. Qed.

End Mem_misc.
