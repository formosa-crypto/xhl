(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From elpi.apps          Require Import derive.std.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
From mathcomp.analysis  Require Import counting_distr.
(* ----------------- *) Require Import inhabited notations mem.

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
    {A B : codeType}
    {X Xg : eqType}
    {mem : memType A B X Xg}
    {fname : eqType}.

Local Notation Distr T := {distr T%type / R}.
Local Notation vars := (vars_ X).
Local Notation gvars := (vars_ Xg).

Definition vname {T : A} (v : vars T) :=
  let: Var name := v in name.

Definition vtype {T : A} (v : vars T) := T.

Inductive expr_ : Type -> Type :=
| var_  {T : A} of vars T : expr_ (interp T)
| cst_  {T}     of T : expr_ T
| prp_          of pred mem : expr_ bool
| app_  {T U}   of expr_ (T -> U) & expr_ T : expr_ U
| gvar_ {T : B} of gvars T : expr_ (interp T).

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
| gassign {T : B} of gvars T & expr_ (interp T)
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

Notation "c %:S"    := (@cst_ _ _ _ _ _ _ c) (at level 2, format "c %:S").
Notation "e1 =b e2" := (app2_ (cst_ beq) e1 e2)    : xsyn_scope.
Notation "e1 =i e2" := (app2_ (cst_ ieq) e1 e2)    : xsyn_scope.
Notation "e1 || e2"  := (app2_ (cst_ orb  ) e1 e2)  : xsyn_scope.
Notation "e1 && e2" := (app2_ (cst_ andb ) e1 e2)  : xsyn_scope.
Notation "~~ e"     := (app_ (cst_ negb) e)        : xsyn_scope.
Notation "e1 + e2"  := (app2_ (cst_ +%R) e1 e2)    : xsyn_scope.
Notation "e1 * e2"  := (app2_ (cst_ *%R) e1 e2)    : xsyn_scope.
Notation "e1 :: e2"  := (app2_ (cst_ cons) e1 e2)   : xsyn_scope.
Notation "` x"      := (@var_ _ _ _ _ _ _ x%V)     : xsyn_scope.
Notation "x %:G"    := (@gvar_ _ _ _ _ _ _ x%V) (at level 2, format "x %:G") : xsyn_scope.

(* -------------------------------------------------------------------- *)
Section SynInject.
Context {R : realType} {A B : codeType} {I1 I1g I2 I2g fname: eqType}
        {mem1 : memType A B I1 I1g} {mem2 : memType A B I2 I2g}
        (h : I1 -> I2) (hg : I1g -> I2g) (mh : mem2 -> mem1).

Local Notation vars1 := (vars_ I1).
Local Notation vars2 := (vars_ I2).
Local Notation gvars1 := (vars_ I1g).
Local Notation gvars2 := (vars_ I2g).
Local Notation expr1 := (@expr_ A B I1 I1g mem1).
Local Notation expr2 := (@expr_ A B I2 I2g mem2).
Local Notation cmd1  := (cmd_  R A B I1 I1g mem1 fname).
Local Notation cmd2  := (cmd_  R A B I2 I2g mem2 fname).

Definition ivar {T : A} (x : vars1 T) : vars2 T :=
  let: Var x := x in Var T (h x).

Definition givar {T : B} (x : gvars1 T) : gvars2 T :=
  let: Var x := x in Var T (hg x).

Definition iprop (p : pred mem1) : pred mem2 :=
  fun m => p (mh m).

Fixpoint iexpr {T : Type} (e : expr1 T) : expr2 T :=
  match e with
  | var_ _   x     => var_ (ivar x)
  | cst_ _   T     => cst_ T
  | prp_     p     => prp_ (iprop p)
  | app_ _ _ e1 e2 => app_ (iexpr e1) (iexpr e2)
  | gvar_ _  x     => gvar_ (givar x)
  end.

Definition ibind (b : @binding A B I1 I1g mem1) : @binding A B I2 I2g mem2 :=
  let: existT t (x, e) := b in bind_of (ivar x) (iexpr e).

Fixpoint icmd (c : cmd1) : cmd2 :=
  match c with
  | abort => abort
  | skip  => skip

  | x <<- e =>
      ivar x <<- iexpr e

  | gassign _ x e =>
      gassign (givar x) (iexpr e)

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

(* -------------------------------------------------------------------- *)
End SynInject.

Section Lift.
Variable (R : realType) (A B : codeType) (X Xg : eqType)
         (M: memType A B X Xg).

Notation rident := (X * side)%type.

Definition irexpr s :=
  (@iexpr A B _ _ _ _ M (rmem A B X Xg M)
     (fun x : X => (x, s)) (fun x : Xg => (x, s))
     (fun m => (m#s)%M)).

Definition ircmd s :=
  (@icmd R A B _ _ _ _ X M (rmem A B X Xg M)
     (fun x : X => (x, s)) (fun x : Xg => (x, s))
     (fun m => (m#s)%M)).

End Lift.

(* -------------------------------------------------------------------- *)
Notation rident ident := (ident * side)%type.

Notation irvar s := (@ivar _ _ _ (fun x => (x, s))) (only parsing).
Notation girvar s := (@givar _ _ _ (fun x => (x, s))) (only parsing).

Reserved Notation "x # s" (at level 2, format "x # s").
Reserved Notation "x #g s" (at level 2, format "x #g s").

Notation "x # s" := (ivar (pair^~ s) x) : vsyn_scope.
Notation "x #g s" := (givar (pair^~ s) x) : vsyn_scope.
Notation "e # s" := (irexpr s e) : xsyn_scope.
Notation "c # s" := (ircmd s c) : syn_scope.
