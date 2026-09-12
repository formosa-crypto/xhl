(* -------------------------------------------------------------------- *)
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import counting_distr.
(* ----------------- *) Require Import inhabited passn pwhile psemantic.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Interp.Recursion
  MonadState
  State
  StateFacts
  Rutt
  RuttFacts.

Import Basics.Monads.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope mem_scope.

(* ==================================================================== *)
(* The whole file is read at the concrete memory [cmem] of pwhile.v, *)
(* over an alphabet [A] and identifiers [ident].  Only the declarations  *)
(* that actually mention them are parameterized on section close.        *)
(* ==================================================================== *)
Section ITreeSem.
Context {R : realType} {A : codeType} {ident : countType}.

Local Notation Distr T := {distr T%type / R}.
Local Notation cmem    := (cmem A ident).
Local Notation vars    := (vars_ ident).
Local Notation expr    := (@expr_ A ident cmem).
Local Notation cmd     := (@cmd_ R A ident cmem ident).
Local Notation bexpr   := (expr bool).
Local Notation dexpr T := (expr (Distr T)).

Variant Rnd : Type -> Type :=
  | GetRnd : forall t : A, {distr t / R} -> Rnd t.

Variant Call : Type -> Type :=
  | CallE (f:ident) : Call unit.

(* [EnterBlock bs] installs the block's initial local store and *returns the
 * outer memory*, so that the continuation can hand it back to [LeaveBlock],
 * which is what makes [mret]'s first argument available at block exit
 * without threading a memory through [com_sem].
 *
 * [InstrE] keeps its own identifiers and memory, as before; what used to
 * pin them to the concrete ones was the global [vars]/[bexpr] notations of
 * pwhile.v, spelled out here at [I]/[mem]. *)
Variant InstrE {I : eqType} {mem : memType A I} : Type -> Type :=
  | Assig : forall t : A,  vars_ I t -> expr_ A I mem t  -> InstrE unit
  | GAssig : forall t : A,  vars_ I t -> expr_ A I mem t  -> InstrE unit
  | RAssig :  forall t : A,  vars_ I t -> expr_ A I mem {distr t / R}  -> InstrE unit
  | EvalCond : expr_ A I mem bool -> InstrE bool
  | EnterBlock : seq (@binding A I mem) -> InstrE mem
  | LeaveBlock : mem -> seq (@binding A I mem) -> InstrE unit.

Section ParSem.

  Context
    {E: Type -> Type}
    {XI : Rnd -< E}
    {XII : @InstrE _ cmem -< E}.

  Local Notation continue_loop := (ret (inl tt)).
  Local Notation exit_loop  := (ret (inr tt)).

  Definition isem_while_round {E}
    (sem_i: cmd ->  itree E unit)
    (cnd: bexpr -> itree E bool)
    (c : cmd) (e : bexpr) :
    itree E (unit + unit) :=
    bind (cnd e)(fun b =>
    if b then bind (sem_i c ) (fun _ => continue_loop )
    else exit_loop).

  Definition isem_while_loop {E}
    (sem_i: cmd -> itree E unit)
    (cnd: bexpr -> itree E bool)
    (c : cmd) (e:bexpr)  :
    itree E unit :=
    ITree.iter (fun _ => isem_while_round sem_i cnd c e) tt.

  Fixpoint com_sem (c : cmd) :  itree (Call +' E) unit :=
    match c with
    | abort => ITree.spin
    | skip => Ret tt
    | x <<- e => trigger (Assig x e)
    | gassign _ x e => trigger (GAssig x e)
    | x <$- e => trigger (RAssig x e)
    | block bs c rs =>
        bind (trigger (EnterBlock bs))
          (fun m0 => bind (com_sem c) (fun _ => trigger (LeaveBlock m0 rs)))
    | If e then c1 else c2 =>
           bind (trigger (EvalCond e))
             (fun b =>  match b with
                     | true => com_sem c1
                     | false => com_sem c2
                     end)
    | While e Do c => isem_while_loop com_sem (fun e => trigger (EvalCond e)) c e
    | seqc c1 c2 => bind (com_sem c1) (fun _ => com_sem c2)
    | pwhile.call f => trigger (CallE f)
    end.

  Definition handle_Call (ps: ident -> cmd) :
    Call ~> itree (Call +' E) :=
    fun T (rc : Call T) =>
      match rc with
      | CallE f => com_sem (ps f)
      end.

  Definition interp_call (ps: ident -> cmd)
    T (t: itree (Call +' E) T) : itree E T :=
    interp_mrec (handle_Call ps) t.

End ParSem.

Section InstrSem.

  Context
    {E: Type -> Type}
    {XI : Rnd -< E}
    {XS: @stateE cmem -< E}.

  (* InstrE handler *)
  Definition handle_InstrE : InstrE ~> itree E :=
    fun _ e =>
      match e with
      | Assig _ x e =>
            bind (trigger (@Get cmem))
              (fun m =>
                 let m := m.[x <- (esem e m)] in
                 trigger (@Put cmem m))
      | GAssig _ x e =>
            bind (trigger (@Get cmem))
              (fun m =>
                 let m := m.{x <- (esem e m)} in
                 trigger (@Put cmem m))
      | EnterBlock bs =>
            bind (trigger (@Get cmem))
              (fun m =>
                 bind (trigger (@Put cmem (minit m bs)))
                   (fun _ => Ret m))
      | LeaveBlock m0 rs =>
            bind (trigger (@Get cmem))
              (fun m' => trigger (@Put cmem (mret m0 m' rs)))
      | RAssig _ x e =>
            bind (trigger (@Get cmem))
            (fun m =>
               bind (trigger (GetRnd (esem e m)))
                 (fun t =>
                    let m := m.[x <- t] in
                    trigger (@Put cmem m)))
      | EvalCond e =>
          bind (@trigger (@Get cmem))(fun m => Ret (esem e m))
      end.

  Definition ext_handle_InstrE : InstrE +' E ~> itree E :=
    case_ handle_InstrE (id_ E).

  Definition interp_InstrE (t : itree (InstrE +' E) unit) : itree E unit :=
    interp ext_handle_InstrE t.

End InstrSem.

Definition interp_intr (t: itree (InstrE +' stateE cmem  +' Rnd) unit) s :=
  bind (run_state (interp_InstrE t) s) (fun t => Ret (fst t)) .

Section PropSem.

  Context {T : choiceType}.

  Fixpoint dinterp' (t : itree' Rnd T) (n : nat) : {distr T / R} :=
    if n is n.+1 then
      match t with
      | RetF r => dunit r
      | TauF t => dinterp' (observe t) n
      | VisF _ e k =>
          match e in Rnd Ty return (Ty -> itree Rnd T) -> {distr T / R} with
          | GetRnd _ mu =>
              fun k0 => \dlet_(t <- mu) (dinterp' (observe (k0 t)) n)
          end k
      end
    else dnull.

  Definition dinterp (t : itree Rnd T) : {distr T / R}  :=
    dlim (dinterp' (observe t)).

End PropSem.

Definition interp_full (c:cmd) (ps: ident -> cmd) : cmem -> {distr cmem / R} :=
  fun s => dinterp (interp_intr (interp_call ps (com_sem c)) s).

(* Section Truc2. *)

(*   Definition Distr (T: Type) : Type := {distr (classicType T) / R}. *)

(*   Definition Monad_Distr : Monad Distr := *)
(*     {| *)
(*       ret := fun T => dunit (T := {classic T}); *)
(*       bind := fun T U mu f => dlet (T := {classic T}) f mu; *)
(*     |}. *)

(*   Definition to_classic {T:Type} (x : T) : {classic T} := x. *)
(*   Definition of_classic {T:Type} (x : {classic T}) : T := x. *)

(*   Definition dclassic {T} (mu : {distr T / R}) : {distr {classic T} / R}:= *)
(*     dmargin to_classic mu. *)

(*   Fixpoint diter_n *)
(*     {T I : Type} (step : I -> Distr (I + T)) (i : I) (n : nat) : Distr T := *)
(*     if n is S n then *)
(*       \dlet_(x <- step i) *)
(*         match of_classic x with *)
(*         | inl i => diter_n step i n *)
(*         | inr t => dunit (to_classic t) *)
(*         end *)
(*     else dnull (T:= {classic T}). *)

(*   Definition diter {R I} (step : I -> Distr (I + R)) (i : I) : Distr R := *)
(*     dlim (diter_n step i). *)

(*   Definition MonadIter_Distr : MonadIter Distr := @diter. *)

(*   Definition handle_rnd : Rnd ~> Distr := *)
(*     fun _ e => let 'GetRnd _ mu := e in dclassic mu. *)

(*   Definition interp_rnd T t:= *)
(*     @interp *)
(*       Rnd *)
(*       Distr *)
(*       (@Functor_Monad Distr Monad_Distr) *)
(*       Monad_Distr MonadIter_Distr handle_rnd *)
(*       T *)
(*       t. *)

(* End Truc2. *)

End ITreeSem.
