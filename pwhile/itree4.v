(* -------------------------------------------------------------------- *)
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
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
(* Import MonadNotation. *)
(* Import ListNotations. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope mem_scope.

Variant Call : Type -> Type :=
 | CallE: ident -> cmem -> Call nat. (* A corriger *)

Variant Rnd : Type -> Type :=
  | GetRnd : forall t : IhbType.type, {distr t / R}  -> Rnd t.

Section ParSem.

  Context {E: Type -> Type }   {XI : Rnd -< E}.

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
    | abort => fun m => Ret m (* A corriger *)
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
    | pwhile.call f =>
        (* Problème d'univers avec un trigger de CallE si cmem est retourné *)
        fun m =>
          bind (trigger (CallE f m)) (fun _ => Ret m)
    end.

  Definition handle_Call (ps: ident -> cmd) (T:Type):
    Call T -> itree (Call +' E) T :=
    fun (rc : Call T) =>
      match rc with
      | CallE f m =>
          let _ := com_sem (ps f) m in
          Ret 1%nat
      end.

  Definition interp_call (ps: ident -> cmd)
    (t: itree (Call +' E) cmem) : itree E cmem :=
    @interp_mrec Call E (handle_Call ps) cmem t.

End ParSem.

Section Truc2.

  Definition Distr (T: Type) : Type := {distr (classicType T) / R}.

  Definition Monad_Distr : Monad Distr :=
    {|
      ret := fun T => dunit (T := {classic T});
      bind := fun T U mu f => dlet (T := {classic T}) f mu;
    |}.

  Definition to_classic {T:Type} (x : T) : {classic T} := x.
  Definition of_classic {T:Type} (x : {classic T}) : T := x.

  Definition dclassic {T} (mu : {distr T / R}) : {distr {classic T} / R}:=
    dmargin to_classic mu.

  Fixpoint diter_n
    {T I : Type} (step : I -> Distr (I + T)) (i : I) (n : nat) : Distr T :=
    if n is S n then
      \dlet_(x <- step i)
        match of_classic x with
        | inl i => diter_n step i n
        | inr t => dunit (to_classic t)
        end
    else dnull (T:= {classic T}).

  Definition diter {R I} (step : I -> Distr (I + R)) (i : I) : Distr R :=
    dlim (diter_n step i).

  Definition MonadIter_Distr : MonadIter Distr := @diter.

  Definition handle_rnd : Rnd ~> Distr :=
    fun _ e => let 'GetRnd _ mu := e in dclassic mu.

  Definition interp_rnd T t:=
    @interp
      Rnd
      Distr
      (@Functor_Monad Distr Monad_Distr)
      Monad_Distr MonadIter_Distr handle_rnd
      T
      t.

End Truc2.

Section FullSem.

  Definition interp_full (c:cmd) (ps: ident -> cmd) :=
    fun s => interp_rnd (interp_call ps( com_sem c s)).

End FullSem.
