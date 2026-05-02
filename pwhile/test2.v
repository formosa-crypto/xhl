(* ========================================================================= *)
(*  WHILE + GOTO — CompCert-style continuation semantics in Rocq            *)
(*                                                                           *)
(*  Key idea (from Leroy's Clight semantics):                               *)
(*  - The AST stays structured (no flattening to a linear program).         *)
(*  - A *continuation* (κ) records what remains to execute after the        *)
(*    current statement.                                                     *)
(*  - goto is handled by *unwinding* the continuation stack and searching   *)
(*    for the target label *inside* the original statement bodies.           *)
(*  - This supports forward & backward jumps, jumps out of loops, and       *)
(*    jumps across nesting — full C-style goto.                             *)
(* ========================================================================= *)

Require Import String.
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

(* ========================================================================= *)
(*  1. BASIC DEFINITIONS                                                     *)
(* ========================================================================= *)

Definition ident := string.
Definition label := string.

Definition store := ident -> Z.

Definition empty_store : store := fun _ => 0.

Definition supdate (σ : store) (x : ident) (v : Z) : store :=
  fun y => if String.eqb x y then v else σ y.

(* ========================================================================= *)
(*  2. EXPRESSIONS                                                           *)
(* ========================================================================= *)

Inductive aexp : Type :=
  | ANum   : Z -> aexp
  | AVar   : ident -> aexp
  | APlus  : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult  : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue  : bexp
  | BFalse : bexp
  | BEq    : aexp -> aexp -> bexp
  | BLe    : aexp -> aexp -> bexp
  | BNot   : bexp -> bexp
  | BAnd   : bexp -> bexp -> bexp.

Fixpoint aeval (σ : store) (a : aexp) : Z :=
  match a with
  | ANum n       => n
  | AVar x       => σ x
  | APlus a1 a2  => aeval σ a1 + aeval σ a2
  | AMinus a1 a2 => aeval σ a1 - aeval σ a2
  | AMult a1 a2  => aeval σ a1 * aeval σ a2
  end.

Fixpoint beval (σ : store) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => Z.eqb (aeval σ a1) (aeval σ a2)
  | BLe a1 a2   => Z.leb (aeval σ a1) (aeval σ a2)
  | BNot b1     => negb (beval σ b1)
  | BAnd b1 b2  => andb (beval σ b1) (beval σ b2)
  end.

(* ========================================================================= *)
(*  3. STATEMENTS                                                            *)
(*                                                                           *)
(*  Identical to a standard WHILE language, extended with labeled            *)
(*  statements and goto. A label attaches to a statement (as in C:          *)
(*  "lbl: stmt"), and goto names a label.                                    *)
(* ========================================================================= *)

Inductive stmt : Type :=
  | Sskip   : stmt
  | Sassign : ident -> aexp -> stmt
  | Sseq    : stmt -> stmt -> stmt
  | Sif     : bexp -> stmt -> stmt -> stmt
  | Sloop   : stmt -> stmt -> stmt
  | Sbreak  : stmt
  | Slabel  : label -> stmt -> stmt
  | Sgoto   : label -> stmt.

Definition Swhile (e: bexp) (s: stmt) :=
  Sloop (Sseq (Sif e Sskip Sbreak) s) Sskip.

(* ========================================================================= *)
(*  4. CONTINUATIONS                                                         *)
(*                                                                           *)
(*  A continuation κ represents "what to do after the current focus          *)
(*  statement finishes."  This is the central data structure.                *)
(*                                                                           *)
(*  CompCert's Clight uses exactly this scheme (see Csem.v / Cshmgen.v).    *)
(*  The continuation records the surrounding program context so that         *)
(*  goto can unwind and re-enter at the right point.                         *)
(* ========================================================================= *)

Inductive cont : Type :=
  | Kstop  : cont
  | Kseq   : stmt -> cont -> cont
  | Kloop1: stmt -> stmt -> cont -> cont
  | Kloop2: stmt -> stmt -> cont -> cont.

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
  | _ => k
  end.

Fixpoint stop_cont (k: cont) : cont :=
  match k with
  | Kseq s k => stop_cont k
  | Kloop1 s1 s2 k => stop_cont k
  | Kloop2 s1 s2 k => stop_cont k
  | _ => k
  end.

(* ========================================================================= *)
(*  5. FINDING A LABEL INSIDE A STATEMENT                                    *)
(*                                                                           *)
(*  When a goto l is executed, we need to find the statement labeled l       *)
(*  in the original program and build the right continuation for it.         *)
(*                                                                           *)
(*  find_label l s κ = Some (s', κ')  means:                                *)
(*    "Inside statement s (with continuation κ), there is a sub-statement   *)
(*     labeled l, and execution should resume at (s', κ')."                 *)
(*                                                                           *)
(*  This is the key function that makes CompCert-style goto work.           *)
(*  It searches the AST recursively, threading the continuation so          *)
(*  that when the label is found, the remaining program context is          *)
(*  correctly captured.                                                      *)
(* ========================================================================= *)


Fixpoint find_label (lbl: label) (s: stmt) (k: cont)
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sif a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 s2 =>
      match find_label lbl s1 (Kloop1 s1 s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 (Kloop2 s1 s2 k)
      end
  | Slabel lbl' s' =>
      if String.eqb lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end.

(* ========================================================================= *)
(*  6. SMALL-STEP SEMANTICS                                                  *)
(*                                                                           *)
(*  State = (focus_stmt, continuation, store)                                *)
(*                                                                           *)
(*  At each step the machine looks at the focus statement:                   *)
(*  - Simple stmts (skip, assign) execute and pop to the continuation.      *)
(*  - Compound stmts (seq, if, while) push frames onto the continuation.    *)
(*  - goto unwinds the continuation searching for the target label.         *)
(*  - label pushes a Klabel marker (for goto to find on unwind) and         *)
(*    descends into the body.                                                *)
(* ========================================================================= *)

Variant state : Type :=
  | State
      (s: stmt)
      (f: stmt)
      (k: cont)
      (m: store) : state
  | Final  : store -> state.

Inductive step : state -> state -> Prop :=

  (* --- assignment --- *)
  | step_assign : forall x a κ c σ,
      step (State (Sassign x a) c κ σ)
        (State Sskip c κ (supdate σ x (aeval σ a)))

  (* --- sequence --- *)
  | step_seq:  forall c s1 s2 k σ,
      step (State (Sseq s1 s2) c k σ)
           (State s1 c (Kseq s2 k) σ)
  | step_skip_seq: forall c s k  σ,
      step (State c Sskip (Kseq s k) σ)
           (State s c k σ)
  | step_break_seq: forall c s k  σ,
      step (State Sbreak c (Kseq s k) σ)
           (State Sbreak c k  σ)

  (* --- if-then-else --- *)
  | step_ifthenelse:  forall c a s1 s2 k σ b,
      beval σ a = b ->
      step (State (Sif a s1 s2) c k σ)
           (State (if b then s1 else s2) c k  σ)

  (* --- loop --- *)
  | step_loop: forall c s1 s2 k σ,
      step (State (Sloop s1 s2) c k σ)
        (State s1 c (Kloop1 s1 s2 k) σ)
  | step_skip_loop1 : forall s1 s2 c κ σ,
      step (State Sskip c (Kloop1 s1 s2 κ) σ)
           (State s2 c (Kloop2 s1 s2 κ) σ)
  | step_break_loop1 : forall s1 s2 c κ σ,
      step (State Sbreak c (Kloop1 s1 s2 κ) σ)
        (State Sbreak c κ σ)
  | step_skip_loop2: forall c s1 s2 k σ,
      step (State Sskip c (Kloop2 s1 s2 k) σ)
        (State (Sloop s1 s2) c k σ)
  | step_break_loop2: forall c s1 s2 k σ,
      step (State Sbreak c (Kloop2 s1 s2 k) σ)
        (State Sskip c k σ)

  (* --- label --- *)
  | step_label: forall c lbl s k σ,
      step (State (Slabel lbl s) c k σ)
           (State s c k σ)

  (* --- goto --- *)
  | step_goto: forall c lbl k σ s' k',
      find_label lbl c (call_cont k) = Some (s', k') ->
      step (State (Sgoto lbl) c k σ)
           (State  s' c k' σ)

  (* --- stop --- *)
  | step_skip_stop : forall σ c ,
      step (State Sskip c Kstop σ)
           (Final σ)
.

(* ========================================================================= *)
(*  7. MULTI-STEP & TERMINATION                                              *)
(* ========================================================================= *)

Inductive multi_step : state -> state -> Prop :=
  | ms_refl : forall st,
      multi_step st st
  | ms_trans : forall st1 st2 st3,
      step st1 st2 ->
      multi_step st2 st3 ->
      multi_step st1 st3.

Definition initial_state (s : stmt) (σ : store) : state :=
  State s s Kstop σ.

Definition terminates (s : stmt) (σ σ' : store) : Prop :=
  multi_step (initial_state s σ) (Final σ').

CoInductive diverges : state -> Prop :=
  | div_step : forall st1 st2,
      step st1 st2 ->
      diverges st2 ->
      diverges st1.

(* ========================================================================= *)
(*  8. EXAMPLE PROGRAMS                                                      *)
(* ========================================================================= *)

(* --- Example 1: Forward goto (break from loop) ---

     x := 0;
     while true do
       if ¬(x <= 9) then goto done else skip end;
       x := x + 1
     end;
     done: skip
*)

Definition test : stmt :=
    (Slabel "loop"
          (Sgoto "loop")).

Definition truc := initial_state test empty_store.

Goal multi_step truc truc.
Proof.
  unfold truc at 1, test.
  eapply ms_trans.
  apply step_label.
  eapply ms_trans.
  apply step_goto; simpl ;reflexivity.
  eapply ms_trans.
  apply step_goto; simpl ;reflexivity.
  eapply ms_trans.
  apply step_goto; simpl ;reflexivity.
  eapply ms_trans.
  apply step_goto; simpl ;reflexivity.
  Abort.

(* This those not work! no semantic/ Label should not have associated stmt. Klabel check
 the label if it shoudl continuui, otherwise go into the continuation *)

Definition ex_forward_goto : stmt :=
  Sseq
    (Sassign "x" (ANum 0))
  (Sseq
    (Swhile BTrue
      (Sseq
        (Sif (BNot (BLe (AVar "x") (ANum 9)))
             (Sgoto "done")
             Sskip)
        (Sassign "x" (APlus (AVar "x") (ANum 1)))))
    (Slabel "done" Sskip)).

(* --- Example 2: Backward goto (loop without while) ---

     x := 0;
     loop: if ¬(x <= 9) then goto done else skip end;
           x := x + 1;
           goto loop;
     done: skip
*)

Definition ex_backward_goto : stmt :=
  Sseq
    (Sassign "x" (ANum 0))
  (Sseq
    (Slabel "loop"
      (Sseq
        (Sif (BNot (BLe (AVar "x") (ANum 9)))
             (Sgoto "done")
             Sskip)
        (Sseq
          (Sassign "x" (APlus (AVar "x") (ANum 1)))
          (Sgoto "loop"))))
    (Slabel "done" Sskip)).

