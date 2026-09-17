(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From elpi.apps          Require Import derive.std.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
From mathcomp.analysis  Require Import counting_distr.
(* ----------------- *) Require Import inhabited notations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Declare Scope syn_scope.
Declare Scope xsyn_scope.
Declare Scope vsyn_scope.
Declare Scope mem_scope.

Delimit Scope syn_scope with S.
Delimit Scope xsyn_scope with X.
Delimit Scope vsyn_scope with V.
Delimit Scope mem_scope with M.

(* -------------------------------------------------------------------- *)
(* Program types are elements of an alphabet [A : codeType].

  A memory is split in two independent stores: a *local* one, read and
  written by [mget_]/[mset_], and a *main* (global) one, read and written by
  [mgetg_]/[msetg_].  [mnew_ m] replaces the local store by a fresh one, and
  [mrestore_ m0 m] puts [m0]'s local store back while keeping [m]'s main
  store.
*)
HB.mixin Record isMemType (A B: codeType) (mident midentg : eqType) M of Choice M := {
  mget_     : M -> forall T : A, mident -> interp T;
  mset_     : M -> forall T : A, mident -> interp T -> M;
  mgetg_    : M -> forall T : B, midentg -> interp T;
  msetg_    : M -> forall T : B, midentg -> interp T -> M;
  mnew_     : M -> M;
  mrestore_ : M -> M -> M;

  mget_eq_  : forall T m x v, mget_ (mset_ m T x v) T x = v;
  mget_neq_ : forall T U m x y v, (T <> U \/ x != y) ->
                mget_ (mset_ m T x v) U y = mget_ m U y;

  mgetg_eq_  : forall T m x v, mgetg_ (msetg_ m T x v) T x = v;
  mgetg_neq_ : forall T U m x y v, (T <> U \/ x != y) ->
                 mgetg_ (msetg_ m T x v) U y = mgetg_ m U y;

  mget_setg_ : forall T U m x y v, mget_  (msetg_ m T x v) U y = mget_  m U y;
  mgetg_set_ : forall T U m x y v, mgetg_ (mset_  m T x v) U y = mgetg_ m U y;

  mgetg_new_ : forall U m y, mgetg_ (mnew_ m) U y = mgetg_ m U y;

  mrestore_id_   : forall m, mrestore_ m m = m;
  mrestoreA_     : forall m0 m1 m, mrestore_ m0 (mrestore_ m1 m) = mrestore_ m0 m;
  mrestore_new_  : forall m0 m, mrestore_ m0 (mnew_ m) = mrestore_ m0 m;
  mrestore_set_  : forall T m0 m x v, mrestore_ m0 (mset_  m T x v) = mrestore_ m0 m;
  mrestore_setg_ : forall T m0 m x v,
                     mrestore_ m0 (msetg_ m T x v) = msetg_ (mrestore_ m0 m) T x v;
  mget_restore_  : forall U m0 m y, mget_  (mrestore_ m0 m) U y = mget_  m0 U y;
  mgetg_restore_ : forall U m0 m y, mgetg_ (mrestore_ m0 m) U y = mgetg_ m U y;
}.

#[short(type="memType")]
HB.structure Definition MemType (A B: codeType) (mident midentg: eqType) :=
  { M of Choice M & isMemType A B mident midentg M }.

Section MemTheory.
Variable (A B : codeType) (mident midentg: eqType).

Section GetSet.
Variable (M : memType A B mident midentg) (T : A) (Tg: B).

Definition mget (m : M) (x : mident) := mget_ m T x.

Arguments mget : simpl never.

Definition mset (m : M) (x : mident) (v : interp T) := mset_ m T x v.

Arguments mset : simpl never.

Definition mgetg (m : M) (x : midentg) := mgetg_ m Tg x.

Arguments mgetg : simpl never.

Definition msetg (m : M) (x : midentg) (v : interp Tg) := msetg_ m Tg x v.

Arguments msetg : simpl never.

End GetSet.

Definition mnew (M : memType A B mident midentg) (m : M) := mnew_ m.

Arguments mnew : simpl never.

Definition mrestore (M : memType A B mident midentg) (m0 m : M) := mrestore_ m0 m.

Arguments mrestore : simpl never.

(* one-variable block entry, kept as a derived form *)
Definition mpush (M : memType A B mident midentg) (T : A)
    (m : M) (x : mident) (v : interp T) := mset (mnew m) x v.

Arguments mpush : simpl never.

Variable (M : memType A B mident midentg) (T U : A) (Tg Ug : B).

Lemma mget_eq (m : M) (x : mident) (v : interp T) : mget T (mset m x v) x = v.
Proof. by unlock mget mset; apply/mget_eq_. Qed.

Lemma mget_neq (m : M) (x y : mident) (v : interp T) : (T <> U \/ x != y) ->
  mget U (mset m x v) y = mget U m y.
Proof. by unlock mget mset; apply/mget_neq_. Qed.

Lemma mgetg_eq (m : M) (x : midentg) (v : interp Tg) : mgetg Tg (msetg m x v) x = v.
Proof. by unlock mgetg msetg; apply/mgetg_eq_. Qed.

Lemma mgetg_neq (m : M) (x y : midentg) (v : interp Tg) : (Tg <> Ug \/ x != y) ->
  mgetg Ug (msetg m x v) y = mgetg Ug m y.
Proof. by unlock mgetg msetg; apply/mgetg_neq_. Qed.

Lemma mget_setg (m : M) (x: midentg) (y : mident) (v : interp Tg) :
  mget U (msetg m x v) y = mget U m y.
Proof. by unlock mget msetg; apply/mget_setg_. Qed.

Lemma mgetg_set (m : M) (x: mident) (y: midentg) (v : interp T) :
  mgetg Ug (mset m x v) y = mgetg Ug m y.
Proof. by unlock mgetg mset; apply/mgetg_set_. Qed.

Lemma mgetg_new (m : M) (y : midentg) : mgetg Ug (mnew m) y = mgetg Ug m y.
Proof. by unlock mgetg mnew; apply/mgetg_new_. Qed.

Lemma mrestore_id (m : M) : mrestore m m = m.
Proof. by unlock mrestore; apply/mrestore_id_. Qed.

Lemma mrestoreA (m0 m1 m : M) : mrestore m0 (mrestore m1 m) = mrestore m0 m.
Proof. by unlock mrestore; apply/mrestoreA_. Qed.

Lemma mrestore_new (m0 m : M) : mrestore m0 (mnew m) = mrestore m0 m.
Proof. by unlock mrestore mnew; apply/mrestore_new_. Qed.

Lemma mrestore_set (m0 m : M) (x : mident) (v : interp T) :
  mrestore m0 (mset m x v) = mrestore m0 m.
Proof. by unlock mrestore mset; apply/mrestore_set_. Qed.

Lemma mrestore_setg (m0 m : M) (x : midentg) (v : interp Tg) :
  mrestore m0 (msetg m x v) = msetg (mrestore m0 m) x v.
Proof. by unlock mrestore msetg; apply/mrestore_setg_. Qed.

Lemma mget_restore (m0 m : M) (y : mident) :
  mget U (mrestore m0 m) y = mget U m0 y.
Proof. by unlock mget mrestore; apply/mget_restore_. Qed.

Lemma mgetg_restore (m0 m : M) (y : midentg) :
  mgetg Ug (mrestore m0 m) y = mgetg Ug m y.
Proof. by unlock mgetg mrestore; apply/mgetg_restore_. Qed.

(* the one-variable block entry, derived *)
Lemma mget_push (m : M) (x : mident) (v : interp T) : mget T (mpush m x v) x = v.
Proof. by unlock mpush; apply/mget_eq. Qed.

Lemma mgetg_push (m : M) (x : mident) (y : midentg) (v : interp T) :
  mgetg Ug (mpush m x v) y = mgetg Ug m y.
Proof. by unlock mpush; rewrite mgetg_set mgetg_new. Qed.

Lemma mrestore_push (m0 m : M) (x : mident) (v : interp T) :
  mrestore m0 (mpush m x v) = mrestore m0 m.
Proof. by unlock mpush; rewrite mrestore_set mrestore_new. Qed.

End MemTheory.

Arguments mget     : simpl never.
Arguments mset     : simpl never.
Arguments mgetg    : simpl never.
Arguments msetg    : simpl never.
Arguments mnew     : simpl never.
Arguments mpush    : simpl never.
Arguments mrestore : simpl never.

(* -------------------------------------------------------------------- *)
(* Concrete memory                                                     *)
(* -------------------------------------------------------------------- *)
Section Concrete.
Variable (R : realType) (A : codeType) (ident : countType).

Definition hupd {F : A -> Type}
    (f : forall T : A, ident -> F T)
    (T : A) (x : ident) (v : F T) : forall U : A, ident -> F U :=
  fun U y =>
    if type_eq_dec A T U is left eq then
      (if x == y then ecast U (F U) eq v else f U y)
    else f U y.

Arguments hupd {F} f T x v : simpl never.

Lemma hupd_eq {F : A -> Type} f (T : A) (x : ident) (v : F T) :
  hupd f T x v T x = v.
Proof.
rewrite /hupd; case: (type_eq_dec _ _ _) => // eq; rewrite eqxx.
by rewrite (type_eq_irrelevance eq (erefl T)).
Qed.

Lemma hupd_nex {F : A -> Type} f (T U : A) (x y : ident) (v : F T) :
  x != y -> hupd f T x v U y = f U y.
Proof.
by move=> ne_xy; rewrite /hupd; case: type_eq_dec => //; rewrite (negbTE ne_xy).
Qed.

Lemma hupd_net {F : A -> Type} f (T U : A) (x y : ident) (v : F T) :
  T <> U -> hupd f T x v U y = f U y.
Proof. by rewrite /hupd; case: type_eq_dec. Qed.

Lemma hupd_ne {F : A -> Type} f (T U : A) (x y : ident) (v : F T) :
  (T <> U \/ x != y) -> hupd f T x v U y = f U y.
Proof. by case=> h; [exact: hupd_net | exact: hupd_nex]. Qed.

Lemma hupd_id (F : A -> Type)
    (f : forall U : A, ident -> F U) (T : A) (x : ident) :
  hupd f T x (f T x) = f.
Proof.
apply: functional_extensionality_dep => U; apply/funext => y.
case: (pselect (T = U)) => [eq|nT]; last by rewrite hupd_net.
case: (eqVneq x y) => [<-|nx]; last by rewrite hupd_nex.
by case: U / eq; rewrite hupd_eq.
Qed.

(* -------------------------------------------------------------------- *)
Record coremem := CoreMem {
  mmain : forall T : A, ident -> interp T;
  mloc  : forall T : A, ident -> interp T;
}.

Definition coremem_get (m : coremem) (T : A) (x : ident) : interp T :=
  mloc m T x.

Coercion coremem_get : coremem >-> Funclass.

Definition coremem_set (m : coremem) (T : A) (x : ident) (v : interp T) :=
  CoreMem (mmain m) (hupd (mloc m) T x v).

Definition coremem_getg (m : coremem) (T : A) (x : ident) : interp T :=
  mmain m T x.

Definition coremem_setg (m : coremem) (T : A) (x : ident) (v : interp T) :=
  CoreMem (hupd (mmain m) T x v) (mloc m).

Definition coremem_new (m : coremem) :=
  CoreMem (mmain m) (fun (U : A) (_ : ident) => witness).

Definition coremem_restore (m0 m : coremem) := CoreMem (mmain m) (mloc m0).

Arguments coremem_set     : simpl never.
Arguments coremem_setg    : simpl never.
Arguments coremem_new     : simpl never.
Arguments coremem_restore : simpl never.

(* -------------------------------------------------------------------- *)
Lemma get_set_eq {T : A} (m : coremem) (x : ident) (v : interp T) :
  (coremem_set m x v) T x = v.
Proof. exact: hupd_eq. Qed.

Lemma set_get_eq {T : A} (m : coremem) (x : ident) :
  coremem_set m x (coremem_get m T x) = m.
Proof.
 by case: m => m1 m2;
   rewrite /mset /mget /mset_ /mget_ /= /coremem_set /=  hupd_id.
Qed.

Lemma get_set_ne {T U : A} (m : coremem) (x y : ident) (v : interp T) :
  (T <> U \/ x != y) -> (coremem_set m x v) U y = m U y.
Proof. exact: hupd_ne. Qed.

Lemma getg_setg_eq {T : A} (m : coremem) (x : ident) (v : interp T) :
  coremem_getg (coremem_setg m x v) T x = v.
Proof. exact: hupd_eq. Qed.

Lemma getg_setg_ne {T U : A} (m : coremem) (x y : ident) (v : interp T) :
  (T <> U \/ x != y) ->
  coremem_getg (coremem_setg m x v) U y = coremem_getg m U y.
Proof. exact: hupd_ne. Qed.

Lemma get_setg {T U : A} (m : coremem) (x y : ident) (v : interp T) :
  (coremem_setg m x v) U y = m U y.
Proof. by []. Qed.

Lemma getg_set {T U : A} (m : coremem) (x y : ident) (v : interp T) :
  coremem_getg (coremem_set m x v) U y = coremem_getg m U y.
Proof. by []. Qed.

Lemma get_new {U : A} (m : coremem) (y : ident) :
  (coremem_new m) U y = witness.
Proof. by []. Qed.

Lemma getg_new {U : A} (m : coremem) (y : ident) :
  coremem_getg (coremem_new m) U y = coremem_getg m U y.
Proof. by []. Qed.

Lemma restore_id (m : coremem) : coremem_restore m m = m.
Proof. by case: m. Qed.

Lemma restoreA (m0 m1 m : coremem) :
  coremem_restore m0 (coremem_restore m1 m) = coremem_restore m0 m.
Proof. by []. Qed.

Lemma restore_new (m0 m : coremem) :
  coremem_restore m0 (coremem_new m) = coremem_restore m0 m.
Proof. by []. Qed.

Lemma restore_set {T : A} (m0 m : coremem) (x : ident) (v : interp T) :
  coremem_restore m0 (coremem_set m x v) = coremem_restore m0 m.
Proof. by []. Qed.

Lemma restore_setg {T : A} (m0 m : coremem) (x : ident) (v : interp T) :
  coremem_restore m0 (coremem_setg m x v) = coremem_setg (coremem_restore m0 m) x v.
Proof. by []. Qed.

Lemma get_restore {d : A} (m0 m : coremem) (y : ident) :
  (coremem_restore m0 m) d y = m0 d y.
Proof. by []. Qed.

Lemma getg_restore {d : A} (m0 m : coremem) (y : ident) :
  coremem_getg (coremem_restore m0 m) d y = coremem_getg m d y.
Proof. by []. Qed.

Lemma coremem_comparable : comparable coremem.
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition coremem_eqType :=
  hasDecEq.Build coremem (compareP coremem_comparable).

HB.instance Definition coremem_choiceType :=
  gen_choiceMixin coremem.

(* -------------------------------------------------------------------- *)
HB.instance Definition coremem_memType :=
  isMemType.Build A ident ident coremem
    (@get_set_eq) (@set_get_eq) (@get_set_ne) (@getg_setg_eq) (@getg_setg_ne)
    (@get_setg) (@getg_set) (@getg_new)
    restore_id restoreA restore_new (@restore_set) (@restore_setg)
    (@get_restore) (@getg_restore).

Definition cmem : memType A ident ident := coremem.

End Concrete.

(* -------------------------------------------------------------------- *)
#[only(eqbOK)] derive
  Inductive side := SLeft | SRight.

Definition _side_list := [:: SLeft; SRight].

HB.instance Definition _ := hasDecEq.Build side side_eqb_OK.

Notation "''1'" := SLeft.
Notation "''2'" := SRight.

Definition mselect {T : Type} (s : side) (m : T * T) :=
  match s with
  | '1 => m.1
  | '2 => m.2
  end.

Notation "m # s" := (mselect s m) (at level 2, format "m # s") : mem_scope.

(* -------------------------------------------------------------------- *)
Lemma side2 {A : Type} s (x : A * A) : ((fst, snd)#s x = x#s)%M.
Proof. by case: s. Qed.

Lemma side_app {A B : Type} (f : A -> B) s (x y : A) :
  (f (x, y)#s = (f x, f y)#s)%M.
Proof. by case: s. Qed.

(* -------------------------------------------------------------------- *)
(* Relational memory                                           *)
(* -------------------------------------------------------------------- *)
Section RelaMem.
Variable (R : realType) (A : codeType) (X Xg: eqType) (M: memType A X Xg).

Definition rident :=  (X * side)%type.
Definition ridentg := (Xg * side)%type.

Definition coremem2 := (M * M)%type.

Definition coremem2_get (m : coremem2) T xs :=
  mget T (m#(xs.2))%M xs.1.

Definition coremem2_set (m : coremem2) (T : A) xs (v : interp T) :=
  match xs.2 return coremem2 with
  | '1 => (mset m.1 xs.1 v, m.2)
  | '2 => (m.1, mset m.2 xs.1 v)
  end.

Definition coremem2_getg (m : coremem2) T xs :=
  mgetg T (m#(xs.2))%M xs.1.

Definition coremem2_setg (m : coremem2) (T : A) xs (v : interp T) :=
  match xs.2 return coremem2 with
  | '1 => (msetg m.1 xs.1 v, m.2)
  | '2 => (m.1, msetg m.2 xs.1 v)
  end.

Definition coremem2_new (m : coremem2) : coremem2 := (mnew m.1, mnew m.2).

Definition coremem2_restore (m0 m : coremem2) : coremem2 :=
  (mrestore m0.1 m.1, mrestore m0.2 m.2).

Coercion coremem2_get : coremem2 >-> Funclass.

Lemma get_set2_eq {T} m x v : (@coremem2_set m T x v) T x = v.
Proof. by case: m x => m1 m2 [x []] /=; apply mget_eq. Qed.

Lemma set_get2_eq {T} m x : (@coremem2_set m T x (@coremem2_get m T x)) = m.
Proof. by case: m x => m1 m2 [x []] /=; rewrite /coremem2_set /= mset_eq. Qed.

Lemma get_set2_ne {T U} m x y v :
  (T <> U \/ x != y) -> (@coremem2_set m T x v) U y = m U y.
Proof.
case: m x y => m1 m2 [x []] [y []] //= h; apply mget_neq => /=;
  by (elim: h => h; [left | right; apply: contra h => /eqP->]).
Qed.

Lemma getg_setg2_eq {T} m x v :
  coremem2_getg (@coremem2_setg m T x v) T x = v.
Proof. by case: m x => m1 m2 [x []] /=; apply mgetg_eq. Qed.

Lemma getg_setg2_ne {T U} m x y v :
  (T <> U \/ x != y) ->
  coremem2_getg (@coremem2_setg m T x v) U y = coremem2_getg m U y.
Proof.
case: m x y => m1 m2 [x []] [y []] //= h; apply mgetg_neq => /=;
  by (elim: h => h; [left | right; apply: contra h => /eqP->]).
Qed.

Lemma get_setg2 {T U} m x y v : (@coremem2_setg m T x v) U y = m U y.
Proof. by case: m x y => m1 m2 [x []] [y []] //=; apply mget_setg. Qed.

Lemma getg_set2 {T d} m x y v :
  coremem2_getg (@coremem2_set m T x v) d y = coremem2_getg m d y.
Proof. by case: m x y => m1 m2 [x []] [y []] //=; apply mgetg_set. Qed.

Lemma getg_new2 {U} m y :
  coremem2_getg (coremem2_new m) U y = coremem2_getg m U y.
Proof. by case: m y => m1 m2 [y []] /=; apply mgetg_new. Qed.

Lemma restore2_id m : coremem2_restore m m = m.
Proof. by case: m => m1 m2; rewrite /coremem2_restore /= !mrestore_id. Qed.

Lemma restore2A m0 m1 m :
  coremem2_restore m0 (coremem2_restore m1 m) = coremem2_restore m0 m.
Proof. by rewrite /coremem2_restore /= !mrestoreA. Qed.

Lemma restore2_new m0 m :
  coremem2_restore m0 (coremem2_new m) = coremem2_restore m0 m.
Proof.
by case: m => m1 m2; rewrite /coremem2_restore /coremem2_new /= !mrestore_new.
Qed.

Lemma restore2_set {T} m0 m x v :
  coremem2_restore m0 (@coremem2_set m T x v) = coremem2_restore m0 m.
Proof.
by case: m x => m1 m2 [x []] /=; rewrite /coremem2_restore /= mrestore_set.
Qed.

Lemma restore2_setg {T} m0 m x v :
  coremem2_restore m0 (@coremem2_setg m T x v)
    = coremem2_setg (coremem2_restore m0 m) x v.
Proof.
by case: m x => m1 m2 [x []] /=; rewrite /coremem2_restore /= mrestore_setg.
Qed.

Lemma get_restore2 {U} m0 m y : (coremem2_restore m0 m) U y = m0 U y.
Proof. by case: m0 m y => a1 a2 [b1 b2] [y []] /=; apply mget_restore. Qed.

Lemma getg_restore2 {U} m0 m y :
  coremem2_getg (coremem2_restore m0 m) U y = coremem2_getg m U y.
Proof. by case: m0 m y => a1 a2 [b1 b2] [y []] /=; apply mgetg_restore. Qed.

HB.instance Definition coremem2_choiceType :=
  Choice.copy coremem2 (M * M)%type.

(* -------------------------------------------------------------------- *)
HB.instance Definition coremem2_memType :=
  isMemType.Build A rident ridentg coremem2
    (@get_set2_eq) (@set_get2_eq) (@get_set2_ne) (@getg_setg2_eq) (@getg_setg2_ne)
    (@get_setg2) (@getg_set2) (@getg_new2)
    restore2_id restore2A restore2_new (@restore2_set) (@restore2_setg)
    (@get_restore2) (@getg_restore2).

Definition rmem : memType A rident ridentg := coremem2.

End RelaMem.

Arguments rmem : clear implicits.
Arguments rmem : simpl never.
