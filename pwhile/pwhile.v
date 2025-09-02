(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis  Require Import reals distr.
(* ----------------- *) Require Import inhabited notations.

Require Import Eqdep_dec.

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

Notation Distr T := {distr T / R}.

(* -------------------------------------------------------------------- *)
Section MemType.
Variable (mident : eqType).

Record memType_ : Type := mkMem {
  mheap    :> choiceType;
  mget_    :  mheap -> forall (T : IhbType.type), mident -> T;
  mset_    :  mheap -> forall (T : IhbType.type), mident -> T -> mheap;
  mget_eq_  : forall T m x v, @mget_ (@mset_ m T x v) T x = v; 
  mget_neq_ : forall T U m x y v, (T <> U \/ x != y) ->
                @mget_ (@mset_ m T x v) U y = @mget_ m U y;
}.

Section GetSet.
Variable (M : memType_) (T : IhbType.type).

Definition mget (m : M) (x : mident) :=
  nosimpl (@mget_ M m T x).

Definition mset (m : M) (x : mident) (v : T) :=
  nosimpl (@mset_ M m T x v).

End GetSet.

Variable (M : memType_) (T U : IhbType.type).

Lemma mget_eq (m : M) (x : mident) (v : T) : mget T (mset m x v) x = v.
Proof. by unlock mget mset; apply/mget_eq_. Qed.

Lemma mget_neq (m : M) (x y : mident) (v : T) : (T <> U \/ x != y) ->
  mget U (mset m x v) y = mget U m y.
Proof. by unlock mget mset; apply/mget_neq_. Qed.

Definition memType_of of phant mident := memType_.
End MemType.

Notation memType T := (memType_of (Phant T)).

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
Context {ident : eqType} {mem : memType ident}.

Local Notation vars := (vars_ ident).

Definition vname {T} (v : vars T) :=
  let: Var name := v in name.

Definition vtype {T} (v : vars T) := T.

Inductive expr_ : Type -> Type :=
| var_  {T}   of vars T : expr_ T
| cst_  {T}   of T : expr_ T
| prp_        of pred mem : expr_ bool
| app_  {T U} of expr_ (T -> U) & expr_ T : expr_ U.

Notation bexpr   := (expr_ bool).
Notation dexpr T := (expr_ (Distr T)).

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

(*
Canonical tvars_eqType (I : eqType) :=
  Equality.copy 


Eval hnf in @tag_eqType
  (EqType ihbType (comparableMixin (fun x y => pselect (x = y))))
  (vars_eqType^~ I).
*)

(* -------------------------------------------------------------------- *)
Lemma eq_vars {t u : IhbType.type} (x : vars t) (y : vars u) :
      (Tagged vars y = Tagged vars x)
  <-> (vtype x = vtype y /\ vname x == vname y).
Proof using Type. (*split.
+ case: x y => [x] [y]; rewrite /vtype /= => /(@eqP (tvars_eqType ident)).
  rewrite -tag_eqE /tag_eq /= => /andP[/eqP] /= ->.
  by rewrite tagged_asE => /eqP[->]; rewrite eqxx.
+ by case: x y => [x] [y]; rewrite /vtype /= => -[-> /eqP->].
Qed.*) Admitted.

(* -------------------------------------------------------------------- *)
(* Commands *)

Inductive cmd_ : Type :=
| abort
| skip
| assign {t} of vars t & expr_ t
| random {t} of vars t & dexpr t
| cond       of bexpr & cmd_ & cmd_
| while      of bexpr & cmd_
| seqc       of cmd_ & cmd_.

Bind Scope syn_scope with cmd_.
End Syntax.

(* -------------------------------------------------------------------- *)
Notation "'If' e 'then' c1 'else' c2"
  := (cond e%X c1%S c2%S) : syn_scope.

Notation "'IfT' e 'then' c1"
  := (cond e%X c1%S skip) : syn_scope.

Notation "'While' e 'Do' c"
  := (while e%X c%S) : syn_scope.

Notation "x <<- e"
  := (assign x%V e%X) : syn_scope.

Notation "x <$- d"
  := (random x%V d%X) : syn_scope.

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

Inductive coremem :=
  CoreMem (m : forall {T : IhbType.type}, ident -> T).

Definition coremem_get := (fun m => let: CoreMem m := m in m).

Coercion coremem_get : coremem >-> Funclass.

Definition coremem_set := nosimpl (fun (m : coremem) {T : IhbType.type} x v =>
  CoreMem (fun U y =>
    if pselect (T = U) is left eq then
      if x == y then ecast _ _ eq v else m U y
    else coremem_get m U y)).

Lemma get_set_eq {T : IhbType.type} (m : coremem) (x : ident) (v : T) :
  (coremem_set m x v) T x = v.
Proof.
rewrite /coremem_get /=; case: (pselect _) => // eq; rewrite eqxx.
suff ->: eq = erefl T by done.
by apply/UIP_dec=> {}x y; apply/pselect.
Qed.

Lemma get_set_nex {T U : IhbType.type} (m : coremem) (x y : ident) (v : T) :
  x != y -> (coremem_set m x v) U y = m U y.
Proof.
move=> ne_xy; rewrite /coremem_set /coremem_get /=.
by case: pselect => //; rewrite (negbTE ne_xy).
Qed.

Lemma get_set_net {T U : IhbType.type} (m : coremem) (x y: ident) (v : T) :
  T <> U -> (coremem_set m x v) U y = m U y.
Proof. by rewrite /coremem_set /coremem_get; case: pselect. Qed.

Lemma get_set_ne {T U : IhbType.type} (m : coremem) (x y : ident) (v : T) :
  (T <> U \/ x !=y) -> (coremem_set m x v) U y = m U y.
Proof. by move=> [/get_set_net |/get_set_nex] ->. Qed.

Lemma coremem_comparable : comparable coremem.
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition coremem_eqType :=
  hasDecEq.Build coremem (compareP coremem_comparable).

HB.instance Definition coremem_choiceType :=
  gen_choiceMixin coremem.
End CoreMem.

Arguments coremem : clear implicits.

(* -------------------------------------------------------------------- *)
Definition cmem : memType ident := locked {|
  mheap     := Choice.clone coremem _;
  mget_     := coremem_get;
  mset_     := coremem_set;
  mget_eq_  := @get_set_eq;
  mget_neq_ := @get_set_ne;
|}.

Notation dmem := (Distr cmem).

(* -------------------------------------------------------------------- *)
Inductive side : predArgType := SLeft | SRight.

Coercion bool_of_side (s : side) :=
  match s with SLeft => false | SRight => true end.

Definition side_of_bool (b : bool) :=
  if b then SRight else SLeft.

Lemma side_of_boolK : cancel bool_of_side side_of_bool.
Proof. by case. Qed.

HB.instance Definition side_eqType :=
  Equality.copy side (can_type side_of_boolK).

(*
HB.instance Definition side_choiceType :=
  Choice.copy side (can_type side_of_boolK).
*)

HB.instance Definition side_countType :=
  CanIsCountable side_of_boolK.

HB.instance Definition side_finType :=
  Finite.copy side (can_type side_of_boolK).

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

Definition coremem2 := (mheap cmem * mheap cmem)%type.

Definition coremem2_get (m : coremem2) T xs :=
  mget T (m#(xs.2))%M xs.1.

Definition coremem2_set (m : coremem2) (T : IhbType.type) xs (v : T) :=
  match xs.2 return coremem2 with
  | '1 => (mset m.1 xs.1 v, m.2)
  | '2 => (m.1, mset m.2 xs.1 v)
  end.

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

Canonical coremem2_choiceType := Choice.clone coremem2 _.

(* -------------------------------------------------------------------- *)
Definition rmem : memType rident := nosimpl {|
  mheap     := Choice.clone coremem2 _;
  mget_     := coremem2_get; 
  mset_     := coremem2_set;
  mget_eq_  := @get_set2_eq;
  mget_neq_ := @get_set2_ne;
|}.

(* -------------------------------------------------------------------- *)
Notation vars    := (vars_ ident).
Notation expr    := (expr_ _ cmem).
Notation cmd     := (cmd_  _ cmem).
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

(* -------------------------------------------------------------------- *)
Section SynInject.
Context {I1 I2 : eqType} {mem1 : memType I1} {mem2:memType I2} 
        (h : I1 -> I2) (mh : mem2 -> mem1).

Local Notation vars1 := (vars_ I1).
Local Notation vars2 := (vars_ I2).
Local Notation expr1 := (@expr_ I1 mem1).
Local Notation expr2 := (@expr_ I2 mem2).
Local Notation cmd1  := (cmd_  I1 mem1).
Local Notation cmd2  := (cmd_  I2 mem2).

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
  end.

Fixpoint icmd (c : cmd1) : cmd2 :=
  match c with
  | abort => abort
  | skip  => skip

  | x <<- e =>
      ivar x <<- iexpr e

  | x <$- e =>
      ivar x <$- iexpr e

  | If e then c1 else c2 =>
      If iexpr e then icmd c1 else icmd c2

  | While e Do c =>
      While iexpr e Do icmd c

  | seqc c1 c2 =>
      seqc (icmd c1) (icmd c2)
  end.
End SynInject.

(* -------------------------------------------------------------------- *)
Notation rvars := (vars_ rident).
Notation rexpr := (expr_ _ rmem).
Notation rcmd  := (cmd_  _ rmem).

Implicit Types (s : side).

Notation   irvar  s := (@ivar  _ _ (fun x => (x, s))) (only parsing).
Definition irexpr s := (@iexpr _ _ cmem rmem (fun x : ident => (x, s)) (fun m=> (m#s)%M)).
Definition ircmd  s := (@icmd  _ _ cmem rmem (fun x : ident => (x, s)) (fun m=> (m#s)%M)).

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
