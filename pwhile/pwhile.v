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
HB.mixin Record isMemType (A : codeType) (mident : eqType) M of Choice M := {
  mget_     : M -> forall T : A, mident -> interp T;
  mset_     : M -> forall T : A, mident -> interp T -> M;
  mgetg_    : M -> forall T : A, mident -> interp T;
  msetg_    : M -> forall T : A, mident -> interp T -> M;
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
HB.structure Definition MemType (A : codeType) (mident : eqType) :=
  { M of Choice M & isMemType A mident M }.

Section MemTheory.
Variable (A : codeType) (mident : eqType).

Section GetSet.
Variable (M : memType A mident) (T : A).

Definition mget (m : M) (x : mident) := mget_ m T x.

Arguments mget : simpl never.

Definition mset (m : M) (x : mident) (v : interp T) := mset_ m T x v.

Arguments mset : simpl never.

Definition mgetg (m : M) (x : mident) := mgetg_ m T x.

Arguments mgetg : simpl never.

Definition msetg (m : M) (x : mident) (v : interp T) := msetg_ m T x v.

Arguments msetg : simpl never.

End GetSet.

Definition mnew (M : memType A mident) (m : M) := mnew_ m.

Arguments mnew : simpl never.

Definition mrestore (M : memType A mident) (m0 m : M) := mrestore_ m0 m.

Arguments mrestore : simpl never.

(* one-variable block entry, kept as a derived form *)
Definition mpush (M : memType A mident) (T : A)
    (m : M) (x : mident) (v : interp T) := mset (mnew m) x v.

Arguments mpush : simpl never.

Variable (M : memType A mident) (T U : A).

Lemma mget_eq (m : M) (x : mident) (v : interp T) : mget T (mset m x v) x = v.
Proof. by unlock mget mset; apply/mget_eq_. Qed.

Lemma mget_neq (m : M) (x y : mident) (v : interp T) : (T <> U \/ x != y) ->
  mget U (mset m x v) y = mget U m y.
Proof. by unlock mget mset; apply/mget_neq_. Qed.

Lemma mgetg_eq (m : M) (x : mident) (v : interp T) : mgetg T (msetg m x v) x = v.
Proof. by unlock mgetg msetg; apply/mgetg_eq_. Qed.

Lemma mgetg_neq (m : M) (x y : mident) (v : interp T) : (T <> U \/ x != y) ->
  mgetg U (msetg m x v) y = mgetg U m y.
Proof. by unlock mgetg msetg; apply/mgetg_neq_. Qed.

Lemma mget_setg (m : M) (x y : mident) (v : interp T) :
  mget U (msetg m x v) y = mget U m y.
Proof. by unlock mget msetg; apply/mget_setg_. Qed.

Lemma mgetg_set (m : M) (x y : mident) (v : interp T) :
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

Lemma mrestore_set (m0 m : M) (x : mident) (v : interp T) :
  mrestore m0 (mset m x v) = mrestore m0 m.
Proof. by unlock mrestore mset; apply/mrestore_set_. Qed.

Lemma mrestore_setg (m0 m : M) (x : mident) (v : interp T) :
  mrestore m0 (msetg m x v) = msetg (mrestore m0 m) x v.
Proof. by unlock mrestore msetg; apply/mrestore_setg_. Qed.

Lemma mget_restore (m0 m : M) (y : mident) :
  mget U (mrestore m0 m) y = mget U m0 y.
Proof. by unlock mget mrestore; apply/mget_restore_. Qed.

Lemma mgetg_restore (m0 m : M) (y : mident) :
  mgetg U (mrestore m0 m) y = mgetg U m y.
Proof. by unlock mgetg mrestore; apply/mgetg_restore_. Qed.

(* the one-variable block entry, derived *)
Lemma mget_push (m : M) (x : mident) (v : interp T) : mget T (mpush m x v) x = v.
Proof. by unlock mpush; apply/mget_eq. Qed.

Lemma mgetg_push (m : M) (x y : mident) (v : interp T) :
  mgetg U (mpush m x v) y = mgetg U m y.
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
(* Expressions and probabilistic expressions *)

Section Vars.
Context {A : codeType} {ident : eqType}.

Inductive vars_r (T : A) :=
| Var of ident.

Definition vars_of of phant ident := vars_r.
End Vars.

Notation vars_ ident := (vars_of (Phant ident)).

(* -------------------------------------------------------------------- *)
Section Syntax.
  Context
    {R : realType}
    {A : codeType}
    {ident : eqType}
    {mem : memType A ident}
    {fname : eqType}.

Local Notation Distr T := {distr T%type / R}.
Local Notation vars := (vars_ ident).

Definition vname {T : A} (v : vars T) :=
  let: Var name := v in name.

Definition vtype {T : A} (v : vars T) := T.

Inductive expr_ : Type -> Type :=
| var_  {T : A} of vars T : expr_ (interp T)
| cst_  {T}     of T : expr_ T
| prp_          of pred mem : expr_ bool
| app_  {T U}   of expr_ (T -> U) & expr_ T : expr_ U
| gvar_ {T : A} of vars T : expr_ (interp T).

Notation bexpr   := (expr_ bool).
Notation dexpr T := (expr_ (Distr T)).

Definition binding := {T : A & (vars T * expr_ (interp T))%type}.

Definition bind_of {T : A} (x : vars T) (e : expr_ (interp T)) : binding :=
  existT _ T (x, e).

(* -------------------------------------------------------------------- *)
Bind Scope syn_scope with expr_.

(* -------------------------------------------------------------------- *)
Section VarsEqType.
  Variables (T : A) (I : eqType).

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

Lemma eq_vars {t u : A} (x : vars t) (y : vars u) :
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
| assign {T : A}  of vars T & expr_ (interp T)
| gassign {T : A} of vars T & expr_ (interp T)
| random {T : A}  of vars T & dexpr (interp T)
| block           of seq binding & cmd_ & seq binding
| cond            of bexpr & cmd_ & cmd_
| while           of bexpr & cmd_
| seqc            of cmd_ & cmd_
| call            of fname.

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
Notation app2_ f x1 x2 := (app_ (app_ f x1) x2).

Reserved Notation "x =b y" (at level 70, no associativity).
Reserved Notation "x =i y" (at level 70, no associativity).

Definition beq (x y : bool) : bool := x == y.
Definition ieq (x y : int ) : bool := x == y.

Notation "c %:S"    := (@cst_ _ _ _ _ c) (at level 2, format "c %:S").
Notation "e1 =b e2" := (app2_ (cst_ beq) e1 e2)   : xsyn_scope.
Notation "e1 =i e2" := (app2_ (cst_ ieq) e1 e2)   : xsyn_scope.
Notation "e1 || e2" := (app2_ (cst_ orb  ) e1 e2) : xsyn_scope.
Notation "e1 && e2" := (app2_ (cst_ andb ) e1 e2) : xsyn_scope.
Notation "~~ e"     := (app_ (cst_ negb) e)       : xsyn_scope.
Notation "e1 + e2"  := (app2_ (cst_ +%R) e1 e2)   : xsyn_scope.
Notation "e1 * e2"  := (app2_ (cst_ *%R) e1 e2)   : xsyn_scope.
Notation "e1 :: e2" := (app2_ (cst_ cons) e1 e2)  : xsyn_scope.
Notation "` x"      := (@var_ _ _ _ _ x%V)        : xsyn_scope.
Notation "x %:G"    := (@gvar_ _ _ _ _ x%V) (at level 2, format "x %:G") : xsyn_scope.

(* -------------------------------------------------------------------- *)
Section SynInject.
Context {R : realType} {A : codeType} {I1 I2 fname: eqType}
        {mem1 : memType A I1} {mem2 : memType A I2}
        (h : I1 -> I2) (mh : mem2 -> mem1).

Local Notation vars1 := (vars_ I1).
Local Notation vars2 := (vars_ I2).
Local Notation expr1 := (@expr_ A I1 mem1).
Local Notation expr2 := (@expr_ A I2 mem2).
Local Notation cmd1  := (cmd_  R A I1 mem1 fname).
Local Notation cmd2  := (cmd_  R A I2 mem2 fname).

Definition ivar {T : A} (x : vars1 T) : vars2 T :=
  let: Var x := x in Var T (h x).

Definition iprop (p : pred mem1) : pred mem2 :=
  fun m => p (mh m).

Fixpoint iexpr {T : Type} (e : expr1 T) : expr2 T :=
  match e with
  | var_ _   x     => var_ (ivar x)
  | cst_ _   T     => cst_ T
  | prp_     p     => prp_ (iprop p)
  | app_ _ _ e1 e2 => app_ (iexpr e1) (iexpr e2)
  | gvar_ _  x     => gvar_ (ivar x)
  end.

Definition ibind (b : @binding A I1 mem1) : @binding A I2 mem2 :=
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
  isMemType.Build A ident coremem
    (@get_set_eq) (@get_set_ne) (@getg_setg_eq) (@getg_setg_ne)
    (@get_setg) (@getg_set) (@getg_new)
    restore_id restoreA restore_new (@restore_set) (@restore_setg)
    (@get_restore) (@getg_restore).

Definition cmem : memType A ident := coremem.

(* -------------------------------------------------------------------- *)
Notation rident := (ident * side)%type.

Definition coremem2 := (cmem * cmem)%type.

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
  Choice.copy coremem2 (cmem * cmem)%type.

(* -------------------------------------------------------------------- *)
HB.instance Definition coremem2_memType :=
  isMemType.Build A rident coremem2
    (@get_set2_eq) (@get_set2_ne) (@getg_setg2_eq) (@getg_setg2_ne)
    (@get_setg2) (@getg_set2) (@getg_new2)
    restore2_id restore2A restore2_new (@restore2_set) (@restore2_setg)
    (@get_restore2) (@getg_restore2).

Definition rmem : memType A rident := coremem2.

Arguments rmem : simpl never.

(* -------------------------------------------------------------------- *)
Definition irexpr s :=
  (@iexpr A _ _ cmem rmem (fun x : ident => (x, s)) (fun m => (m#s)%M)).

Definition ircmd s :=
  (@icmd R A _ _ ident cmem rmem (fun x : ident => (x, s)) (fun m => (m#s)%M)).

End Concrete.

Arguments cmem : clear implicits.
Arguments rmem : clear implicits.
Arguments rmem : simpl never.

(* -------------------------------------------------------------------- *)
Notation rident ident := (ident * side)%type.

Notation irvar s := (@ivar _ _ _ (fun x => (x, s))) (only parsing).

Reserved Notation "x # s" (at level 2, format "x # s").

Notation "x # s" := (ivar (pair^~ s) x) : vsyn_scope.
Notation "e # s" := (irexpr s e) : xsyn_scope.
Notation "c # s" := (ircmd s c) : syn_scope.
