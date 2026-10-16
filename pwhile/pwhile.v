(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From elpi.apps          Require Import derive.std.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
From mathcomp.analysis  Require Import counting_distr.
(* ----------------- *) Require Import inhabited notations.

From Stdlib Require Import Eqdep_dec.

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
Parameter R : realType.

#[non_forgetful_inheritance]
HB.instance Definition real_ihbType :=
  IsInhabited.Build R 0.

Notation Distr T := {distr T%type / R}.

(* -------------------------------------------------------------------- *)
(* A memory is split in two independent stores: a *local* one, read and
 * written by [mget_]/[mset_], and a *main* (global) one, read and written by
 * [mgetg_]/[msetg_].  [mnew_ m] replaces the local store by a fresh one, and
 * [mrestore_ m0 m] puts [m0]'s local store back while keeping [m]'s main
 * store.  A block therefore enters with [mnew_] followed by one [mset_] per
 * declared local.  The stack of enclosing local stores is *not* held in the
 * memory: it is the recursion of the interpreter. *)
HB.mixin Record isMemType (mident : eqType) M of Choice M := {
  mget_     : M -> forall (T : IhbType.type), mident -> T;
  mset_     : M -> forall (T : IhbType.type), mident -> T -> M;
  mgetg_    : M -> forall (T : IhbType.type), mident -> T;
  msetg_    : M -> forall (T : IhbType.type), mident -> T -> M;
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
HB.structure Definition MemType (mident : eqType) :=
  { M of Choice M & isMemType mident M }.

Section MemTheory.
Variable (mident : eqType).

Section GetSet.
Variable (M : memType mident) (T : IhbType.type).

Definition mget (m : M) (x : mident) := mget_ m T x.

Arguments mget : simpl never.

Definition mset (m : M) (x : mident) (v : T) := mset_ m T x v.

Arguments mset : simpl never.

Definition mgetg (m : M) (x : mident) := mgetg_ m T x.

Arguments mgetg : simpl never.

Definition msetg (m : M) (x : mident) (v : T) := msetg_ m T x v.

Arguments msetg : simpl never.

End GetSet.

Definition mnew (M : memType mident) (m : M) := mnew_ m.

Arguments mnew : simpl never.

Definition mrestore (M : memType mident) (m0 m : M) := mrestore_ m0 m.

Arguments mrestore : simpl never.

(* one-variable block entry, kept as a derived form *)
Definition mpush (M : memType mident) (T : IhbType.type)
    (m : M) (x : mident) (v : T) := mset (mnew m) x v.

Arguments mpush : simpl never.

Variable (M : memType mident) (T U : IhbType.type).

Lemma mget_eq (m : M) (x : mident) (v : T) : mget T (mset m x v) x = v.
Proof. by unlock mget mset; apply/mget_eq_. Qed.

Lemma mget_neq (m : M) (x y : mident) (v : T) : (T <> U \/ x != y) ->
  mget U (mset m x v) y = mget U m y.
Proof. by unlock mget mset; apply/mget_neq_. Qed.

Lemma mgetg_eq (m : M) (x : mident) (v : T) : mgetg T (msetg m x v) x = v.
Proof. by unlock mgetg msetg; apply/mgetg_eq_. Qed.

Lemma mgetg_neq (m : M) (x y : mident) (v : T) : (T <> U \/ x != y) ->
  mgetg U (msetg m x v) y = mgetg U m y.
Proof. by unlock mgetg msetg; apply/mgetg_neq_. Qed.

Lemma mget_setg (m : M) (x y : mident) (v : T) :
  mget U (msetg m x v) y = mget U m y.
Proof. by unlock mget msetg; apply/mget_setg_. Qed.

Lemma mgetg_set (m : M) (x y : mident) (v : T) :
  mgetg U (mset m x v) y = mgetg U m y.
Proof. by unlock mgetg mset; apply/mgetg_set_. Qed.

Lemma mgetg_new (m : M) (y : mident) : mgetg U (mnew m) y = mgetg U m y.
Proof. by unlock mgetg mnew; apply/mgetg_new_. Qed.

Lemma mrestore_id (m : M) : mrestore m m = m.
Proof. by unlock mrestore; apply/mrestore_id_. Qed.

Lemma mrestoreA (m0 m1 m : M) : mrestore m0 (mrestore m1 m) = mrestore m0 m.
Proof. by unlock mrestore; apply/mrestoreA_. Qed.

Lemma mrestore_new (m0 m : M) : mrestore m0 (mnew m) = mrestore m0 m.
Proof. by unlock mrestore mnew; apply/mrestore_new_. Qed.

Lemma mrestore_set (m0 m : M) (x : mident) (v : T) :
  mrestore m0 (mset m x v) = mrestore m0 m.
Proof. by unlock mrestore mset; apply/mrestore_set_. Qed.

Lemma mrestore_setg (m0 m : M) (x : mident) (v : T) :
  mrestore m0 (msetg m x v) = msetg (mrestore m0 m) x v.
Proof. by unlock mrestore msetg; apply/mrestore_setg_. Qed.

Lemma mget_restore (m0 m : M) (y : mident) :
  mget U (mrestore m0 m) y = mget U m0 y.
Proof. by unlock mget mrestore; apply/mget_restore_. Qed.

Lemma mgetg_restore (m0 m : M) (y : mident) :
  mgetg U (mrestore m0 m) y = mgetg U m y.
Proof. by unlock mgetg mrestore; apply/mgetg_restore_. Qed.

(* the one-variable block entry, derived *)
Lemma mget_push (m : M) (x : mident) (v : T) : mget T (mpush m x v) x = v.
Proof. by unlock mpush; apply/mget_eq. Qed.

Lemma mgetg_push (m : M) (x y : mident) (v : T) :
  mgetg U (mpush m x v) y = mgetg U m y.
Proof. by unlock mpush; rewrite mgetg_set mgetg_new. Qed.

Lemma mrestore_push (m0 m : M) (x : mident) (v : T) :
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
(* Expressions and probabilistic expressions *)

Section Vars.
Context {ident : eqType}.

Inductive vars_r (T : IhbType.type) :=
| Var of ident.

Definition vars_of of phant ident := vars_r.
End Vars.

Notation vars_ ident := (vars_of (Phant ident)).

(* -------------------------------------------------------------------- *)
Section Syntax.
  Context
    {ident : eqType}
    {mem : memType ident}
    {fname : eqType}.

Local Notation vars := (vars_ ident).

Definition vname {T} (v : vars T) :=
  let: Var name := v in name.

Definition vtype {T} (v : vars T) := T.

Inductive expr_ : Type -> Type :=
| var_  {T}   of vars T : expr_ T
| cst_  {T}   of T : expr_ T
| prp_        of pred mem : expr_ bool
| app_  {T U} of expr_ (T -> U) & expr_ T : expr_ U
| gvar_ {T}   of vars T : expr_ T.

Notation bexpr   := (expr_ bool).
Notation dexpr T := (expr_ (Distr T)).

Definition binding := {t : IhbType.type & (vars t * expr_ t)%type}.

Definition bind_of {t : IhbType.type} (x : vars t) (e : expr_ t) : binding :=
  existT _ t (x, e).

(* -------------------------------------------------------------------- *)
Bind Scope syn_scope with expr_.

(* -------------------------------------------------------------------- *)
Section VarsEqType.
  Variables (T : IhbType.type) (I : eqType).

  Definition vars_eq (x y : vars_ I T) :=
    let: Var x := x in let: Var y := y in x == y.

  Lemma vars_eqP (x y : vars_ I T) : reflect (x = y) (vars_eq x y).
  Proof.
    by case: x y => [x] [y]; apply: (iffP idP) => /= [/eqP->|[->]].
  Qed.

  HB.instance Definition vars_eqType :=
    hasDecEq.Build (vars_ I T) vars_eqP.
End VarsEqType.

(* -------------------------------------------------------------------- *)

Lemma eq_vars {t u : IhbType.type} (x : vars t) (y : vars u) :
      (Tagged vars y = Tagged vars x)
  <-> (vtype x = vtype y /\ vname x == vname y).
Proof.
  split.
  - case: x y => [x] [y]; rewrite /vtype /=.
    unfold Tagged => H.
    have ? := (existT_inj1 H);subst.
    have := (existT_inj2 H).
    by case => ->.
  - by case: x y => [x] [y]; rewrite /vtype /= => -[-> /eqP->].
Qed.

(* -------------------------------------------------------------------- *)
(* Commands *)

Inductive cmd_ : Type :=
| abort
| skip
| assign {t}    of vars t & expr_ t
| gassign {t}   of vars t & expr_ t
| random {t}    of vars t & dexpr t
| block         of seq binding & cmd_ & seq binding
| cond          of bexpr & cmd_ & cmd_
| while         of bexpr & cmd_
| seqc          of cmd_ & cmd_
| call          of fname.

Bind Scope syn_scope with cmd_.
End Syntax.

(* -------------------------------------------------------------------- *)
Notation "x <<- e"
  := (assign x%V e%X) : syn_scope.

Notation "'G' x <<- e"
  := (gassign x%V e%X) (at level 0, x at level 0, e at level 70) : syn_scope.

Notation "x <$- d"
  := (random x%V d%X) : syn_scope.

Notation "x <<= e"
  := (bind_of x%V e%X) (at level 65, e at level 70) : syn_scope.

Notation "'Block' bs 'Do' c 'Return' rs"
  := (block bs c%S rs)
  (at level 0, bs at level 99, c at level 99, rs at level 99) : syn_scope.

Notation "'Begin' 'Local' x := e ; c ; r := e' 'End'"
  := (block [:: bind_of x%V e%X] c%S [:: bind_of r%V e'%X])
  (at level 0, x at level 0, e at level 70, c at level 99,
   r at level 0, e' at level 70) : syn_scope.

Notation "'If' e 'then' c1 'else' c2"
  := (cond e%X c1%S c2%S) : syn_scope.

Notation "'IfT' e 'then' c1"
  := (cond e%X c1%S skip) : syn_scope.

Notation "'While' e 'Do' c"
  := (while e%X c%S) : syn_scope.

Notation "c1 ;; c2"
  := (seqc c1%S c2%S) : syn_scope.

Local Open Scope syn_scope.

(* -------------------------------------------------------------------- *)
Arguments expr_ : clear implicits.
Arguments cmd_  : clear implicits.

(* -------------------------------------------------------------------- *)
Parameter ident : countType.

(* -------------------------------------------------------------------- *)
Section CoreMem.

Definition hupd {F : IhbType.type -> Type}
    (f : forall T : IhbType.type, ident -> F T)
    (T : IhbType.type) (x : ident) (v : F T) : forall U : IhbType.type, ident -> F U :=
  fun U y =>
    if pselect (T = U) is left eq then
      (if x == y then ecast U (F U) eq v else f U y)
    else f U y.

Arguments hupd {F} f T x v : simpl never.

Lemma hupd_eq {F : IhbType.type -> Type} f (T : IhbType.type) (x : ident) (v : F T) :
  hupd f T x v T x = v.
Proof.
rewrite /hupd; case: (pselect _) => // eq; rewrite eqxx.
suff ->: eq = erefl T by done.
by apply/UIP_dec=> {}x y; apply/pselect.
Qed.

Lemma hupd_nex {F : IhbType.type -> Type} f (T U : IhbType.type) (x y : ident) (v : F T) :
  x != y -> hupd f T x v U y = f U y.
Proof.
by move=> ne_xy; rewrite /hupd; case: pselect => //; rewrite (negbTE ne_xy).
Qed.

Lemma hupd_net {F : IhbType.type -> Type} f (T U : IhbType.type) (x y : ident) (v : F T) :
  T <> U -> hupd f T x v U y = f U y.
Proof. by rewrite /hupd; case: pselect. Qed.

Lemma hupd_ne {F : IhbType.type -> Type} f (T U : IhbType.type) (x y : ident) (v : F T) :
  (T <> U \/ x != y) -> hupd f T x v U y = f U y.
Proof. by case=> h; [exact: hupd_net | exact: hupd_nex]. Qed.

(* -------------------------------------------------------------------- *)
Record coremem := CoreMem {
  mmain : forall T : IhbType.type, ident -> T;
  mloc  : forall T : IhbType.type, ident -> T;
}.

Definition coremem_get (m : coremem) (T : IhbType.type) (x : ident) : T :=
  mloc m T x.

Coercion coremem_get : coremem >-> Funclass.

Definition coremem_set (m : coremem) (T : IhbType.type) (x : ident) (v : T) :=
  CoreMem (mmain m) (hupd (mloc m) T x v).

Definition coremem_getg (m : coremem) (T : IhbType.type) (x : ident) : T :=
  mmain m T x.

Definition coremem_setg (m : coremem) (T : IhbType.type) (x : ident) (v : T) :=
  CoreMem (hupd (mmain m) T x v) (mloc m).

Definition coremem_new (m : coremem) :=
  CoreMem (mmain m) (fun (U : IhbType.type) (_ : ident) => witness U).

Definition coremem_restore (m0 m : coremem) := CoreMem (mmain m) (mloc m0).

Arguments coremem_set     : simpl never.
Arguments coremem_setg    : simpl never.
Arguments coremem_new     : simpl never.
Arguments coremem_restore : simpl never.

(* -------------------------------------------------------------------- *)
Lemma get_set_eq {T : IhbType.type} (m : coremem) (x : ident) (v : T) :
  (coremem_set m x v) T x = v.
Proof. exact: hupd_eq. Qed.

Lemma get_set_ne {T U : IhbType.type} (m : coremem) (x y : ident) (v : T) :
  (T <> U \/ x != y) -> (coremem_set m x v) U y = m U y.
Proof. exact: hupd_ne. Qed.

Lemma getg_setg_eq {T : IhbType.type} (m : coremem) (x : ident) (v : T) :
  coremem_getg (coremem_setg m x v) T x = v.
Proof. exact: hupd_eq. Qed.

Lemma getg_setg_ne {T U : IhbType.type} (m : coremem) (x y : ident) (v : T) :
  (T <> U \/ x != y) ->
  coremem_getg (coremem_setg m x v) U y = coremem_getg m U y.
Proof. exact: hupd_ne. Qed.

Lemma get_setg {T U : IhbType.type} (m : coremem) (x y : ident) (v : T) :
  (coremem_setg m x v) U y = m U y.
Proof. by []. Qed.

Lemma getg_set {T U : IhbType.type} (m : coremem) (x y : ident) (v : T) :
  coremem_getg (coremem_set m x v) U y = coremem_getg m U y.
Proof. by []. Qed.

Lemma get_new {U : IhbType.type} (m : coremem) (y : ident) :
  (coremem_new m) U y = witness U.
Proof. by []. Qed.

Lemma getg_new {U : IhbType.type} (m : coremem) (y : ident) :
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

Lemma restore_set {T : IhbType.type} (m0 m : coremem) (x : ident) (v : T) :
  coremem_restore m0 (coremem_set m x v) = coremem_restore m0 m.
Proof. by []. Qed.

Lemma restore_setg {T : IhbType.type} (m0 m : coremem) (x : ident) (v : T) :
  coremem_restore m0 (coremem_setg m x v) = coremem_setg (coremem_restore m0 m) x v.
Proof. by []. Qed.

Lemma get_restore {U : IhbType.type} (m0 m : coremem) (y : ident) :
  (coremem_restore m0 m) U y = m0 U y.
Proof. by []. Qed.

Lemma getg_restore {U : IhbType.type} (m0 m : coremem) (y : ident) :
  coremem_getg (coremem_restore m0 m) U y = coremem_getg m U y.
Proof. by []. Qed.

Lemma coremem_comparable : comparable coremem.
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition coremem_eqType :=
  hasDecEq.Build coremem (compareP coremem_comparable).

HB.instance Definition coremem_choiceType :=
  gen_choiceMixin coremem.
End CoreMem.

(* -------------------------------------------------------------------- *)
HB.instance Definition coremem_memType :=
  isMemType.Build ident coremem
    (@get_set_eq) (@get_set_ne) (@getg_setg_eq) (@getg_setg_ne)
    (@get_setg) (@getg_set) (@getg_new)
    restore_id restoreA restore_new (@restore_set) (@restore_setg)
    (@get_restore) (@getg_restore).

Definition cmem : memType ident := coremem.

Notation dmem := (Distr cmem).

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
Notation rident := (ident * side)%type.

Definition coremem2 := (cmem * cmem)%type.

Definition coremem2_get (m : coremem2) T xs :=
  mget T (m#(xs.2))%M xs.1.

Definition coremem2_set (m : coremem2) (T : IhbType.type) xs (v : T) :=
  match xs.2 return coremem2 with
  | '1 => (mset m.1 xs.1 v, m.2)
  | '2 => (m.1, mset m.2 xs.1 v)
  end.

Definition coremem2_getg (m : coremem2) T xs :=
  mgetg T (m#(xs.2))%M xs.1.

Definition coremem2_setg (m : coremem2) (T : IhbType.type) xs (v : T) :=
  match xs.2 return coremem2 with
  | '1 => (msetg m.1 xs.1 v, m.2)
  | '2 => (m.1, msetg m.2 xs.1 v)
  end.

Definition coremem2_new (m : coremem2) : coremem2 := (mnew m.1, mnew m.2).

Definition coremem2_restore (m0 m : coremem2) : coremem2 :=
  (mrestore m0.1 m.1, mrestore m0.2 m.2).

Coercion coremem2_get : coremem2 >-> Funclass.

Set Printing Coercions.

Lemma get_set2_eq {T} m x v : (@coremem2_set m T x v) T x = v.
Proof. by case: m x => m1 m2 [x []] /=; apply mget_eq. Qed.

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

Lemma getg_set2 {T U} m x y v :
  coremem2_getg (@coremem2_set m T x v) U y = coremem2_getg m U y.
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
  Choice.copy coremem2 (cmem * cmem)%type.

(* -------------------------------------------------------------------- *)
HB.instance Definition coremem2_memType :=
  isMemType.Build rident coremem2
    (@get_set2_eq) (@get_set2_ne) (@getg_setg2_eq) (@getg_setg2_ne)
    (@get_setg2) (@getg_set2) (@getg_new2)
    restore2_id restore2A restore2_new (@restore2_set) (@restore2_setg)
    (@get_restore2) (@getg_restore2).

Definition rmem : memType rident := coremem2.

Arguments rmem : simpl never.

(* -------------------------------------------------------------------- *)
Notation vars    := (vars_ ident).
Notation expr    := (expr_ _ cmem).
Notation cmd     := (cmd_  _ cmem ident).
Notation bexpr   := (expr bool).
Notation dexpr T := (expr (Distr T)).
Notation prp     := (@prp_ _ cmem).

(* -------------------------------------------------------------------- *)
Notation app2_ f x1 x2 := (app_ (app_ f x1) x2).

Reserved Notation "x =b y" (at level 70, no associativity).
Reserved Notation "x =i y" (at level 70, no associativity).

Definition beq (x y : bool) : bool := x == y.
Definition ieq (x y : int ) : bool := x == y.

Notation "c %:S"    := (@cst_ _ _ _ c) (at level 2, format "c %:S").
Notation "e1 =b e2" := (app2_ (cst_ beq) e1 e2)   : xsyn_scope.
Notation "e1 =i e2" := (app2_ (cst_ ieq) e1 e2)   : xsyn_scope.
Notation "e1 || e2" := (app2_ (cst_ orb  ) e1 e2) : xsyn_scope.
Notation "e1 && e2" := (app2_ (cst_ andb ) e1 e2) : xsyn_scope.
Notation "~~ e"     := (app_ (cst_ negb) e)       : xsyn_scope.
Notation "e1 + e2"  := (app2_ (cst_ +%R) e1 e2)   : xsyn_scope.
Notation "e1 * e2"  := (app2_ (cst_ *%R) e1 e2)   : xsyn_scope.
Notation "e1 :: e2" := (app2_ (cst_ cons) e1 e2)  : xsyn_scope.
Notation "` x"      := (@var_ _ _ _ x%V)          : xsyn_scope.
Notation "x %:G"    := (@gvar_ _ _ _ x%V) (at level 2, format "x %:G") : xsyn_scope.

(* -------------------------------------------------------------------- *)
Section SynInject.
Context {I1 I2 fname: eqType} {mem1 : memType I1} {mem2:memType I2}
        (h : I1 -> I2) (mh : mem2 -> mem1).

Local Notation vars1 := (vars_ I1).
Local Notation vars2 := (vars_ I2).
Local Notation expr1 := (@expr_ I1 mem1).
Local Notation expr2 := (@expr_ I2 mem2).
Local Notation cmd1  := (cmd_  I1 mem1 fname).
Local Notation cmd2  := (cmd_  I2 mem2 fname).

Definition ivar {T : IhbType.type} (x : vars1 T) : vars2 T :=
  let: Var x := x in Var T (h x).

Definition iprop (p : pred mem1) : pred mem2 :=
  fun m => p (mh m).

Fixpoint iexpr {T : Type} (e : expr1 T) : expr2 T :=
  match e with
  | var_ _   x     => var_ (ivar x)
  | cst_ _   c     => cst_ c
  | prp_     p     => prp_ (iprop p)
  | app_ _ _ e1 e2 => app_ (iexpr e1) (iexpr e2)
  | gvar_ _  x     => gvar_ (ivar x)
  end.

Definition ibind (b : @binding I1 mem1) : @binding I2 mem2 :=
  let: existT t (x, e) := b in bind_of (ivar x) (iexpr e).

Fixpoint icmd (c : cmd1) : cmd2 :=
  match c with
  | abort => abort
  | skip  => skip

  | x <<- e =>
      ivar x <<- iexpr e

  | gassign _ x e =>
      gassign (ivar x) (iexpr e)

  | x <$- e =>
      ivar x <$- iexpr e

  | block bs c rs =>
      block (map ibind bs) (icmd c) (map ibind rs)

  | If e then c1 else c2 =>
      If iexpr e then icmd c1 else icmd c2

  | While e Do c =>
      While iexpr e Do icmd c

  | seqc c1 c2 =>
      seqc (icmd c1) (icmd c2)

  | call n => call n
  end.
End SynInject.

(* -------------------------------------------------------------------- *)
Notation rvars := (vars_ rident).
Notation rexpr := (expr_ _ rmem).
Notation rcmd  := (cmd_  _ rmem ident).

Implicit Types (s : side).

Notation   irvar  s := (@ivar  _ _ (fun x => (x, s))) (only parsing).
Definition irexpr s := (@iexpr _ _ cmem rmem (fun x : ident => (x, s)) (fun m=> (m#s)%M)).
Definition ircmd  s := (@icmd  _ _ ident cmem rmem (fun x : ident => (x, s)) (fun m=> (m#s)%M)).

Reserved Notation "x # s" (at level 2, format "x # s").

Notation "x # s" := (ivar (pair^~ s) x) : vsyn_scope.
Notation "e # s" := (irexpr s e) : xsyn_scope.
Notation "c # s" := (ircmd s c) : syn_scope.
Notation rmem1 m := (m.1 : mem).
Notation rmem2 m := (m.2 : mem).
Notation rprp    := (@prp_ _ rmem).

(* -------------------------------------------------------------------- *)
Notation assn  := (pred cmem).
Notation dassn := (pred dmem).
Notation rassn := (pred rmem).
