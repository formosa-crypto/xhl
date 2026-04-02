(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import ClassicalFacts Setoid Morphisms.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
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
(* Import MonadNotation. *)
(* Import ListNotations. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope mem_scope.

(* Section Estate. *)

(*   Variant estate {T}: Type -> Type := *)
(*     | Abort : nat -> T ->  estate T *)
(*     | Ok : T -> estate T. *)

(*   Definition bind A T (f : A ->  estate T) (g : estate A):= *)
(*     match g with *)
(*     | Ok x    => f x *)
(*     | Abort n s => Abort n s *)
(*   end. *)

(* End Estate. *)

  Variant Rnd : Type -> Type :=
    | GetRnd : forall t : IhbType.type, {distr t / R} -> Rnd t.

  Variant Str : Type -> Type :=
    | CallE (f:ident) : Str unit
    | WhE : bexpr -> cmd -> Str unit.

  Variant InstrE {ident : eqType}  {mem : memType ident} : Type -> Type :=
    | Assig : forall t : IhbType.type,  vars t -> expr_ ident mem t  -> InstrE unit
    | RAssig :  forall t : IhbType.type,  vars t -> expr_ ident mem {distr t / R}  -> InstrE unit
    | EvalCond : bexpr -> InstrE bool.

Section ParSem.

  Context
    {E: Type -> Type}
    {XI : Rnd -< E}
    {XII : @InstrE _ cmem -< E}.

  Fixpoint com_sem (c : cmd) :  itree (Str +' E) unit :=
    match c with
    | abort => Ret tt
    | skip => Ret tt
    | x <<- e => trigger (Assig x e)
    | x <$- e => trigger (RAssig x e)
    | If e then c1 else c2 =>
           bind (trigger (EvalCond e))
             (fun b =>  match b with
                     | true => com_sem c1
                     | false => com_sem c2
                     end)
    | While e Do c => trigger (WhE e c)
    | seqc c1 c2 => bind (com_sem c1) (fun _ => com_sem c2)
    | pwhile.call f => trigger (CallE f)
    end.

  Definition handle_Str (ps: ident -> cmd) :
    Str ~> itree (Str +' E) :=
    fun T (rc : Str T) =>
      match rc with
      | CallE f => com_sem (ps f)
      | WhE e c => com_sem (If e then (seqc c (While e Do c)) else skip)
      end.

  Definition interp_call (ps: ident -> cmd)
    T (t: itree (Str +' E) T) : itree E T :=
    interp_mrec (handle_Str ps) t.

End ParSem.

Section InstrSem.

  Context
    {E: Type -> Type}
    {XI : Rnd -< E}
    {XS: @stateE cmem -< E}.

  Definition handle_InstrE : InstrE ~> itree E :=
    fun _ e =>
      match e with
      | Assig _ x e =>
            bind (trigger (@Get cmem))
              (fun m =>
                 let m := m.[x <- (esem e m)] in
                 trigger (@Put cmem m))
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
          match e in Rnd A return (A -> itree Rnd T) -> distr R T with
          | GetRnd _ mu =>
              fun k0 => \dlet_(t <- mu) (dinterp' (observe (k0 t)) n)
          end k
      end
    else dnull.

  Definition dinterp (t : itree Rnd T) : distr R T :=
    dlim (dinterp' (observe t)).

End PropSem.

Definition interp_full (c:cmd) (ps: ident -> cmd) : cmem -> {distr cmem / R} :=
    fun s => dinterp (interp_intr (interp_call ps (com_sem c)) s).
