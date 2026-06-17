From Stdlib Require Import String ZArith List Bool.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Interp.Recursion
  MonadState
  Events.Exception.

Import Basics.Monads.

Definition ident := string.
Definition label := string.

Definition store := ident -> Z.

Definition empty_store : store := fun _ => 0.

Definition supdate (σ : store) (x : ident) (v : Z) : store :=
  fun y => if String.eqb x y then v else σ y.

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

Inductive stmt : Type :=
  | Sskip     : stmt
  | Sassign   : ident -> aexp -> stmt
  | Sseq      : stmt -> stmt -> stmt
  | Sif       : bexp -> stmt -> stmt -> stmt
  | Sloop     : stmt -> stmt -> stmt
  | Sbreak    : stmt
  | Scontinue : stmt
  | Scall     : ident -> stmt
  | Sreturn   : stmt
  | Slabel    : label -> stmt -> stmt
  | Sgoto     : label -> stmt.

Definition Swhile (e: bexp) (s: stmt) :=
  Sloop (Sseq (Sif e Sskip Sbreak) s) Sskip.

Inductive cont : Type :=
  | Kstop  : cont
  | Kseq   : stmt -> cont -> cont
  | Kloop1: stmt -> stmt -> cont -> cont
  | Kloop2: stmt -> stmt -> cont -> cont.

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

Definition runtime_env : Type := (stmt *  ident * cont * store).

Variant Call : Type -> Type :=
  | CallE (f:ident) (m: store): Call store.

Definition impExcE : Type -> Type := exceptE unit.

Section ParSem.
  Context {E: Type -> Type} (ps: ident -> stmt).

  Definition step : runtime_env -> itree (Call +' impExcE +'  E) (runtime_env + store)%type  :=
    fun '(s,f,k,m) =>
      match s with
      | Sassign x a => Ret (inl (Sskip, f, k, (supdate m x (aeval m a))))
      | Sseq s1 s2 => Ret (inl (s1, f, Kseq s2 k, m))
      | Sif a s1 s2 => Ret (inl (if beval m a then s1 else s2, f, k, m))
      | Sloop s1 s2 => Ret (inl (s1, f, Kloop1 s1 s2 k, m))
      | Slabel lbl s => Ret (inl (s, f, k, m))
      | Sgoto lbl =>
          match find_label lbl (ps f) Kstop with
          | Some (s',k') => Ret (inl (s',f,k',m))
          | None => throw tt
          end
      | Sskip =>
          match k with
          | Kseq s k' => Ret (inl (s, f, k', m))
          | Kloop1 s1 s2 k' => Ret (inl (s2, f, Kloop2 s1 s2 k', m))
          | Kloop2 s1 s2 k' => Ret (inl (Sloop s1 s2, f, k', m))
          | Kstop => Ret (inr m)
          end
      | Scontinue =>
          match k with
          | Kseq s k' => Ret (inl (Scontinue, f, k', m))
          | Kloop1 s1 s2 k' => Ret (inl (s2, f, Kloop2 s1 s2 k', m))
          | Kloop2 s1 s2 k' => throw tt
          | Kstop => throw tt
          end
      | Sbreak =>
          match k with
          | Kseq s k' => Ret (inl (Sbreak, f, k', m))
          | Kloop1 s1 s2 k' => Ret (inl (Sskip, f, k', m))
          | Kloop2 s1 s2 k' => Ret (inl (Sskip, f, k', m))
          | Kstop => throw tt
          end
      | Scall f => bind (trigger (CallE f m)) (fun m => Ret (inr m))
      | Sreturn => Ret (inr m)
      end.

  Definition handle_Call (ps: ident -> stmt) :
    Call ~> itree (Call +' impExcE +' E) :=
    fun T (rc : Call T) =>
      match rc with
      | CallE f m => ITree.iter step (ps (f), f, Kstop, m)
      end.

  Definition interp_call (ps: ident -> stmt)
    (t: itree (Call +' impExcE +' E) store) : itree (impExcE +' E) store :=
    interp_mrec (handle_Call ps) t.

  Definition interp_runtime_env : runtime_env -> itree (Call +' impExcE +' E) store :=
    fun '(s, f, k, m) => ITree.iter step (s, f, k, m).

  Definition interp_full (ps: ident -> stmt) :=
    fun s => interp_call ps (interp_runtime_env (ps ("main"), "main", Kstop, s)).

End ParSem.
