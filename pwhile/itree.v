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
(*     | Abort :  estate T *)
(*     | Ok : T -> estate T. *)

(*   Definition bind A T (f : A ->  estate T) (g : estate A):= *)
(*     match g with *)
(*     | Ok x    => f x *)
(*     | Abort => Abort *)
(*   end. *)

(* End Estate. *)


  Variant Rnd : Type -> Type :=
    | GetRnd : forall t : IhbType.type, {distr t / R} -> Rnd t.

  Variant Call : Type -> Type :=
    | CallE (f:nat) (m: cmem): Call cmem.

Section ParSem.
  (* Notation ecmem := (@Ecmem cmem). *)

  Context {E} {XI : Rnd -< E}.

  Local Notation continue_loop s := (ret (inl s)).
  Local Notation exit_loop s := (ret (inr s)).

  Definition isem_while_round {E}
    (sem_i: cmd -> cmem -> itree E cmem) (c : cmd) (e : bexpr) (m : cmem) :
    itree E (cmem + cmem) :=
    if esem e m then bind (sem_i c m) (fun m => continue_loop m)
    else exit_loop m.

  Definition isem_while_loop {E}
    (sem_i: cmd -> cmem -> itree E cmem)
    (c : cmd) (e:bexpr) (m : cmem) :
    itree E cmem :=
    ITree.iter (isem_while_round sem_i c e) m.

  Fixpoint com_sem (c : cmd) : cmem -> itree (Call +' E) cmem :=
    match c with
    | abort => fun m => Ret m (* A corriger avec une monade *)
    | skip => fun m => Ret m
    | x <<- e => fun m => Ret m.[x <- (esem e m)]
    | x <$- e => fun m =>
                   bind (trigger (GetRnd (esem e m)))
                     (fun t => Ret m.[x <- t])
    | If e then c1 else c2 =>
    fun m =>
      match esem e m with
      | true => com_sem c1 m
      | false => com_sem c2 m
      end
    | While e Do c => isem_while_loop com_sem c e
    | seqc c1 c2 => fun m => bind (com_sem c1 m) (fun m => com_sem c2 m)
    | pwhile.call f => fun m => bind (trigger (CallE f m)) (fun m => Ret m)
  end.

  Definition handle_Call (ps: nat -> cmd) :
    Call ~> itree (Call +' E) :=
    fun T (rc : Call T) =>
      match rc with
      | CallE f m => com_sem (ps f) m
      end.

  Definition interp_call (ps: nat -> cmd)
    T (t: itree (Call +' E) T) : itree E T :=
    interp_mrec (handle_Call ps) t.

End ParSem.

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

Section FullSem.

  Definition interp_full (c:cmd) (ps: nat -> cmd) : cmem -> {distr cmem / R} :=
    fun s => dinterp (interp_call ps (com_sem c s)).

End FullSem.
