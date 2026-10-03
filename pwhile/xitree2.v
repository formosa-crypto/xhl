(* -------------------------------------------------------------------- *)
(* Interaction-tree semantics (state-in-effects style) for the language   *)
(* with exceptions.  Copy of [itree2.v] adapted to [xpwhile]/[xpsemantic].*)
(*                                                                        *)
(* [com_sem] now returns [unit + exnv] instead of [unit]: [inl tt] is a    *)
(* normal exit, [inr v] an exception propagating outwards.  Sequencing,    *)
(* the loop body and block exit all branch on it, exactly as [obind] /     *)
(* [oubn] / [osem_aux]'s [block] case do on the denotational side.         *)
(*                                                                        *)
(* Two small additions to [InstrE]:                                        *)
(*  - [EvalE], the value-returning analogue of [EvalCond], used by [raise] *)
(*    to evaluate its payload in the current memory;                       *)
(*  - nothing for the handler's binder: it writes the caught value with    *)
(*    [Assig x (cst_ v)], and the exceptional block exit reuses            *)
(*    [LeaveBlock m0 [::]], which is [mrestore m0 m'] by definition of     *)
(*    [mret].                                                              *)
(* -------------------------------------------------------------------- *)
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import counting_distr.
(* ----------------- *) Require Import inhabited passn mem xpwhile xpsemantic.

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
Section ITreeSem.
Context {R : realType} {A B : codeType} {X Xg Y : eqType}
        {M : memType A B X Xg} {exn : eqType} {exnty : exn -> A}.

Local Notation Distr T := {distr T%type / R}.
Local Notation vars    := (vars_ X).
Local Notation gvar    := (vars_ Xg).
Local Notation expr    := (@expr_ A B X Xg M).
Local Notation cmd     := (@cmd_ R A B X Xg M exn exnty Y).
Local Notation bexpr   := (expr bool).
Local Notation dexpr T := (expr (Distr T)).
Local Notation psi     := (Y -> cmd).

Local Notation exnv    := (exnv A exn exnty).
Local Notation outcome := (outcome A B X Xg M exn exnty).

(* the result of a command: [inl tt] normal, [inr v] exceptional *)
Local Notation res := (unit + exnv)%type.

Variant Rnd : Type -> Type :=
  | GetRnd : forall t : A, {distr t / R} -> Rnd t.

Variant Call : Type -> Type :=
  | CallE (f:Y) : Call res.

Variant InstrE {I Ig : eqType} {mem : memType A B I Ig} : Type -> Type :=
  | Assig : forall t : A,  vars_ I t -> expr_ A B I Ig mem t  -> InstrE unit
  | GAssig : forall t : B,  vars_ Ig t -> expr_ A B I Ig mem t  -> InstrE unit
  | RAssig :  forall t : A,  vars_ I t -> expr_ A B I Ig mem {distr t / R}  -> InstrE unit
  | EvalCond : expr_ A B I Ig mem bool -> InstrE bool
  (* [interp] is shadowed by ITree's, so the result type is written with
   * the [codeType] coercion, exactly as [GetRnd] above does. *)
  | EvalE : forall t : A, expr_ A B I Ig mem t -> InstrE t
  | EnterBlock : seq (@binding A B I Ig mem) -> InstrE mem
  | LeaveBlock : mem -> seq (@binding A B I Ig mem) -> InstrE unit.

Section ParSem.

  Context
    {E: Type -> Type}
    {XI : Rnd -< E}
    {XII : @InstrE _ _ M -< E}.

  Local Notation continue_loop := (ret (inl tt)).

  Definition isem_while_round {E}
    (sem_i: cmd ->  itree E res)
    (cnd: bexpr -> itree E bool)
    (c : cmd) (e : bexpr) :
    itree E (unit + res) :=
    bind (cnd e) (fun b =>
    if b then bind (sem_i c)
                 (fun r => if r is inl tt then continue_loop else ret (inr r))
    else ret (inr (inl tt))).

  Definition isem_while_loop {E}
    (sem_i: cmd -> itree E res)
    (cnd: bexpr -> itree E bool)
    (c : cmd) (e:bexpr)  :
    itree E res :=
    ITree.iter (fun _ => isem_while_round sem_i cnd c e) tt.

  Fixpoint com_sem (c : cmd) :  itree (Call +' E) res :=
    match c with
    | abort => ITree.spin
    | skip => Ret (inl tt)
    | x <<- e => bind (trigger (Assig x e)) (fun _ => Ret (inl tt))
    | gassign _ x e => bind (trigger (GAssig x e)) (fun _ => Ret (inl tt))
    | x <$- e => bind (trigger (RAssig x e)) (fun _ => Ret (inl tt))
    | block bs c rs =>
        bind (trigger (EnterBlock bs))
          (fun m0 => bind (com_sem c)
             (fun r => match r with
                       | inl tt =>
                           bind (trigger (LeaveBlock m0 rs))
                             (fun _ => Ret (inl tt))
                       (* restore the caller's locals, skip [rs] *)
                       | inr v =>
                           bind (trigger (LeaveBlock m0 [::]))
                             (fun _ => Ret (inr v))
                       end))
    | If e then c1 else c2 =>
           bind (trigger (EvalCond e))
             (fun b =>  match b with
                     | true => com_sem c1
                     | false => com_sem c2
                     end)
    | While e Do c => isem_while_loop com_sem (fun e => trigger (EvalCond e)) c e
    | seqc c1 c2 =>
        bind (com_sem c1)
          (fun r => if r is inl tt then com_sem c2 else Ret r)
    | xpwhile.call f => trigger (CallE f)
    | raise k e =>
        bind (trigger (EvalE (t := exnty k) e))
          (fun v => Ret (inr (existT _ k v)))
    | try_ c k x h =>
        bind (com_sem c)
          (fun r => match r with
                    | inl tt => Ret (inl tt)
                    | inr t =>
                        let: existT k' v := t in
                        match k' =P k with
                        | ReflectT eq =>
                            bind (trigger
                                    (Assig x (cst_ (ecast z (exnty z) eq v))))
                              (fun _ => com_sem h)
                        | ReflectF _ => Ret (inr t)
                        end
                    end)
    end.

  Definition handle_Call (ps: psi) :
    Call ~> itree (Call +' E) :=
    fun T (rc : Call T) =>
      match rc with
      | CallE f => com_sem (ps f)
      end.

  Definition interp_call (ps: psi)
    T (t: itree (Call +' E) T) : itree E T :=
    interp_mrec (handle_Call ps) t.

End ParSem.

Section InstrSem.

  Context
    {E: Type -> Type}
    {XI : Rnd -< E}
    {XS: @stateE M -< E}.

  (* InstrE handler *)
  Definition handle_InstrE : InstrE ~> itree E :=
    fun _ e =>
      match e with
      | Assig _ x e =>
            bind (trigger (@Get M))
              (fun m =>
                 let m := m.[x <- (esem e m)] in
                 trigger (@Put M m))
      | GAssig _ x e =>
            bind (trigger (@Get M))
              (fun m =>
                 let m := m.{x <- (esem e m)} in
                 trigger (@Put M m))
      | EnterBlock bs =>
            bind (trigger (@Get M))
              (fun m =>
                 bind (trigger (@Put M (minit m bs)))
                   (fun _ => Ret m))
      | LeaveBlock m0 rs =>
            bind (trigger (@Get M))
              (fun m' => trigger (@Put M (mret m0 m' rs)))
      | RAssig _ x e =>
            bind (trigger (@Get M))
            (fun m =>
               bind (trigger (GetRnd (esem e m)))
                 (fun t =>
                    let m := m.[x <- t] in
                    trigger (@Put M m)))
      | EvalCond e =>
          bind (@trigger (@Get M))(fun m => Ret (esem e m))
      | EvalE _ e =>
          bind (@trigger (@Get M))(fun m => Ret (esem e m))
      end.

  Definition ext_handle_InstrE : InstrE +' E ~> itree E :=
    case_ handle_InstrE (id_ E).

  Definition interp_InstrE {T} (t : itree (InstrE +' E) T) : itree E T :=
    interp ext_handle_InstrE t.

End InstrSem.

(* The final memory is paired with the outcome tag, giving an [outcome]. *)
Definition interp_intr (t: itree (InstrE +' stateE M +' Rnd) res) s
    : itree Rnd outcome :=
  bind (run_state (interp_InstrE t) s)
    (fun p => Ret (if p.2 is inr v then OExc p.1 v else ONorm p.1)).

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

Definition interp_full (c:cmd) (ps: psi) : M -> {distr outcome / R} :=
  fun s => dinterp (interp_intr (interp_call ps (com_sem c)) s).

End ITreeSem.
