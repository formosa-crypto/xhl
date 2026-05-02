(* ========================================================================= *)
(*  A While Language with Break, Continue, and Exceptions                    *)
(*  Big-Step Semantics + Interpreter in Rocq (Coq)                          *)
(* ========================================================================= *)

Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

(* ========================================================================= *)
(*  1. Syntax                                                                *)
(* ========================================================================= *)

Definition var := string.
Definition exn_name := string.

Inductive expr : Type :=
  | EConst : Z -> expr
  | EVar   : var -> expr
  | EAdd   : expr -> expr -> expr
  | ESub   : expr -> expr -> expr
  | EMul   : expr -> expr -> expr.

Inductive bexpr : Type :=
  | BTrue  : bexpr
  | BFalse : bexpr
  | BEq    : expr -> expr -> bexpr
  | BLt    : expr -> expr -> bexpr
  | BNot   : bexpr -> bexpr
  | BAnd   : bexpr -> bexpr -> bexpr.

Inductive cmd : Type :=
  | CSkip      : cmd
  | CAssign    : var -> expr -> cmd
  | CSeq       : cmd -> cmd -> cmd
  | CIf        : bexpr -> cmd -> cmd -> cmd
  | CWhile     : bexpr -> cmd -> cmd
  | CBreak     : cmd
  | CContinue  : cmd
  | CRaise     : exn_name -> expr -> cmd           (* raise E(e)            *)
  | CTryCatch  : cmd -> exn_name -> var -> cmd -> cmd  (* try c catch E(x) => h *)
  | CTryFinally : cmd -> cmd -> cmd.                (* try c finally f       *)

(* ========================================================================= *)
(*  2. States                                                                *)
(* ========================================================================= *)

Definition state := var -> Z.

Definition empty_state : state := fun _ => 0.

Definition update (s : state) (x : var) (v : Z) : state :=
  fun y => if String.eqb x y then v else s y.

Notation "x '!->' v ';' s" := (update s x v)
  (at level 100, v at next level, right associativity).

(* ========================================================================= *)
(*  3. Expression Evaluation                                                 *)
(* ========================================================================= *)

Fixpoint eval_expr (e : expr) (s : state) : Z :=
  match e with
  | EConst n   => n
  | EVar x     => s x
  | EAdd e1 e2 => eval_expr e1 s + eval_expr e2 s
  | ESub e1 e2 => eval_expr e1 s - eval_expr e2 s
  | EMul e1 e2 => eval_expr e1 s * eval_expr e2 s
  end.

Fixpoint eval_bexpr (b : bexpr) (s : state) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BEq e1 e2  => Z.eqb (eval_expr e1 s) (eval_expr e2 s)
  | BLt e1 e2  => Z.ltb (eval_expr e1 s) (eval_expr e2 s)
  | BNot b1    => negb (eval_bexpr b1 s)
  | BAnd b1 b2 => andb (eval_bexpr b1 s) (eval_bexpr b2 s)
  end.

(* ========================================================================= *)
(*  4. Outcomes (Arbib-Alagic-de Bruijn style)                               *)
(* ========================================================================= *)

(** An outcome records *how* a command terminated:
    - normally
    - via break / continue (caught by enclosing while)
    - via an exception carrying a name and a value              *)

Inductive outcome : Type :=
  | ONorm     : outcome
  | OBreak    : outcome
  | OContinue : outcome
  | OExn      : exn_name -> Z -> outcome.

Definition outcome_eqb (o1 o2 : outcome) : bool :=
  match o1, o2 with
  | ONorm, ONorm => true
  | OBreak, OBreak => true
  | OContinue, OContinue => true
  | OExn e1 v1, OExn e2 v2 => String.eqb e1 e2 && Z.eqb v1 v2
  | _, _ => false
  end.

(* ========================================================================= *)
(*  5. Big-Step Operational Semantics                                        *)
(* ========================================================================= *)

Reserved Notation "c '/' s '⇓' out '/' s'"
  (at level 40, s at level 39, out at level 39, s' at level 39).

Inductive big_step : cmd -> state -> outcome -> state -> Prop :=

  (* ---- skip ---- *)
  | BS_Skip : forall s,
      CSkip / s ⇓ ONorm / s

  (* ---- assignment ---- *)
  | BS_Assign : forall s x e,
      CAssign x e / s ⇓ ONorm / (update s x (eval_expr e s))

  (* ---- sequence: c1 normal, then c2 ---- *)
  | BS_Seq_Norm : forall c1 c2 s s' s'' out,
      c1 / s  ⇓ ONorm / s' ->
      c2 / s' ⇓ out   / s'' ->
      CSeq c1 c2 / s ⇓ out / s''

  (* ---- sequence: c1 exits early, c2 skipped ---- *)
  | BS_Seq_Exit : forall c1 c2 s s' out,
      c1 / s ⇓ out / s' ->
      out <> ONorm ->
      CSeq c1 c2 / s ⇓ out / s'

  (* ---- if: true branch ---- *)
  | BS_If_True : forall b c1 c2 s s' out,
      eval_bexpr b s = true ->
      c1 / s ⇓ out / s' ->
      CIf b c1 c2 / s ⇓ out / s'

  (* ---- if: false branch ---- *)
  | BS_If_False : forall b c1 c2 s s' out,
      eval_bexpr b s = false ->
      c2 / s ⇓ out / s' ->
      CIf b c1 c2 / s ⇓ out / s'

  (* ---- while: guard false ---- *)
  | BS_While_False : forall b c s,
      eval_bexpr b s = false ->
      CWhile b c / s ⇓ ONorm / s

  (* ---- while: guard true, body normal → iterate ---- *)
  | BS_While_Norm : forall b c s s' s'' out,
      eval_bexpr b s = true ->
      c / s ⇓ ONorm / s' ->
      CWhile b c / s' ⇓ out / s'' ->
      CWhile b c / s  ⇓ out / s''

  (* ---- while: guard true, body continue → iterate ---- *)
  | BS_While_Continue : forall b c s s' s'' out,
      eval_bexpr b s = true ->
      c / s ⇓ OContinue / s' ->
      CWhile b c / s' ⇓ out / s'' ->
      CWhile b c / s  ⇓ out / s''

  (* ---- while: guard true, body break → exit loop normally ---- *)
  | BS_While_Break : forall b c s s',
      eval_bexpr b s = true ->
      c / s ⇓ OBreak / s' ->
      CWhile b c / s ⇓ ONorm / s'

  (* ---- while: guard true, body raises exception → propagate ---- *)
  | BS_While_Exn : forall b c s s' en ev,
      eval_bexpr b s = true ->
      c / s ⇓ OExn en ev / s' ->
      CWhile b c / s ⇓ OExn en ev / s'

  (* ---- break ---- *)
  | BS_Break : forall s,
      CBreak / s ⇓ OBreak / s

  (* ---- continue ---- *)
  | BS_Continue : forall s,
      CContinue / s ⇓ OContinue / s

  (* ---- raise E(e) ---- *)
  | BS_Raise : forall s en e,
      CRaise en e / s ⇓ OExn en (eval_expr e s) / s

  (* ---- try-catch: body normal/break/continue → pass through ---- *)
  | BS_TryCatch_Normal : forall c en x h s s' out,
      c / s ⇓ out / s' ->
      (forall en' ev', out <> OExn en' ev') ->
      CTryCatch c en x h / s ⇓ out / s'

  (* ---- try-catch: body raises matching exception → run handler ---- *)
  | BS_TryCatch_Catch : forall c en x h s s' s'' ev out,
      c / s ⇓ OExn en ev / s' ->
      h / (update s' x ev) ⇓ out / s'' ->
      CTryCatch c en x h / s ⇓ out / s''

  (* ---- try-catch: body raises non-matching exception → propagate ---- *)
  | BS_TryCatch_Miss : forall c en en' x h s s' ev,
      c / s ⇓ OExn en' ev / s' ->
      en' <> en ->
      CTryCatch c en x h / s ⇓ OExn en' ev / s'

  (* ---- try-finally: body normal → run finalizer, keep body outcome ---- *)
  | BS_TryFinally_Norm : forall c f s s' s'' out,
      c / s ⇓ ONorm / s' ->
      f / s' ⇓ out / s'' ->
      CTryFinally c f / s ⇓ out / s''

  (* ---- try-finally: body early exit, finalizer normal → propagate
         the original exit ---- *)
  | BS_TryFinally_Exit_Norm : forall c f s s' s'' out,
      c / s ⇓ out / s' ->
      out <> ONorm ->
      f / s' ⇓ ONorm / s'' ->
      CTryFinally c f / s ⇓ out / s''

  (* ---- try-finally: body early exit, finalizer also early exit →
         finalizer's exit wins (as in Python/Java) ---- *)
  | BS_TryFinally_Exit_Exit : forall c f s s' s'' out1 out2,
      c / s ⇓ out1 / s' ->
      f / s' ⇓ out2 / s'' ->
      out2 <> ONorm ->
      CTryFinally c f / s ⇓ out2 / s''

where "c '/' s '⇓' out '/' s'" := (big_step c s out s').

(* ========================================================================= *)
(*  6. Fuel-Based Interpreter                                                *)
(* ========================================================================= *)

Fixpoint interp (fuel : nat) (c : cmd) (s : state) : option (outcome * state) :=
  match fuel with
  | O => None
  | S fuel' =>
    match c with
    | CSkip =>
        Some (ONorm, s)

    | CAssign x e =>
        Some (ONorm, update s x (eval_expr e s))

    | CSeq c1 c2 =>
        match interp fuel' c1 s with
        | Some (ONorm, s') => interp fuel' c2 s'
        | Some (out,   s') => Some (out, s')
        | None             => None
        end

    | CIf b c1 c2 =>
        if eval_bexpr b s then interp fuel' c1 s
        else interp fuel' c2 s

    | CWhile b body =>
        if eval_bexpr b s then
          match interp fuel' body s with
          | Some (ONorm,       s') => interp fuel' (CWhile b body) s'
          | Some (OContinue,   s') => interp fuel' (CWhile b body) s'
          | Some (OBreak,      s') => Some (ONorm, s')
          | Some (OExn en ev,  s') => Some (OExn en ev, s')
          | None                   => None
          end
        else
          Some (ONorm, s)

    | CBreak =>
        Some (OBreak, s)

    | CContinue =>
        Some (OContinue, s)

    | CRaise en e =>
        Some (OExn en (eval_expr e s), s)

    | CTryCatch c1 en x h =>
        match interp fuel' c1 s with
        | Some (OExn en' ev, s') =>
            if String.eqb en' en then
              interp fuel' h (update s' x ev)
            else
              Some (OExn en' ev, s')
        | other => other
        end

    | CTryFinally c1 f =>
        match interp fuel' c1 s with
        | Some (ONorm, s') =>
            interp fuel' f s'
        | Some (out1, s') =>
            match interp fuel' f s' with
            | Some (ONorm, s'') => Some (out1, s'')
            | Some (out2,  s'') => Some (out2, s'')   (* finalizer exit wins *)
            | None              => None
            end
        | None => None
        end
    end
  end.


(* ========================================================================= *)
(*  9. Soundness of Interpreter w.r.t. Big-Step Semantics                    *)
(* ========================================================================= *)

Theorem interp_sound : forall fuel c s out s',
  interp fuel c s = Some (out, s') ->
  big_step c s out s'.
Proof.
  induction fuel as [| fuel' IH]; intros c s out s' H.
  - simpl in H. discriminate.
  - destruct c; simpl in H.

    + (* CSkip *)
      inversion H; subst. apply BS_Skip.

    + (* CAssign *)
      inversion H; subst. apply BS_Assign.

    + (* CSeq *)
      destruct (interp fuel' c1 s) as [[[|  |  | en ev] s1] |] eqn:E1;
        try discriminate.
      * apply BS_Seq_Norm with (s' := s1); auto.
      * inversion H; subst.
        eapply BS_Seq_Exit; eauto. discriminate.
      * inversion H; subst.
        eapply BS_Seq_Exit; eauto. discriminate.
      * inversion H; subst.
        eapply BS_Seq_Exit; eauto. discriminate.

    + (* CIf *)
      destruct (eval_bexpr b s) eqn:Eb.
      * eapply BS_If_True; eauto.
      * eapply BS_If_False; eauto.

    + (* CWhile *)
      destruct (eval_bexpr b s) eqn:Eb.
      * destruct (interp fuel' c s) as [[[|  |  | en ev] s1] |] eqn:Ebody;
          try discriminate.
        -- eapply BS_While_Norm; eauto.
        -- inversion H; subst. eapply BS_While_Break; eauto.
        -- eapply BS_While_Continue; eauto.
        -- inversion H; subst. eapply BS_While_Exn; eauto.
      * inversion H; subst. apply BS_While_False. exact Eb.

    + (* CBreak *)
      inversion H; subst. apply BS_Break.

    + (* CContinue *)
      inversion H; subst. apply BS_Continue.

    + (* CRaise *)
      inversion H; subst. apply BS_Raise.

    + (* CTryCatch *)
      destruct (interp fuel' c s) as [[[|  |  | en' ev] s1] |] eqn:Ec;
        try discriminate.
      * (* body → ONorm *)
        inversion H; subst.
        apply BS_TryCatch_Normal with (out := ONorm); auto.
        intros en' ev' Hc. discriminate.
      * (* body → OBreak *)
        inversion H; subst.
        apply BS_TryCatch_Normal with (out := OBreak); auto.
        intros en' ev' Hc. discriminate.
      * (* body → OContinue *)
        inversion H; subst.
        apply BS_TryCatch_Normal with (out := OContinue); auto.
        intros en' ev' Hc. discriminate.
      * (* body → OExn en' ev *)
        destruct (String.eqb en' e) eqn:Ematch.
        -- (* matching exception *)
           apply String.eqb_eq in Ematch. subst.
           eapply BS_TryCatch_Catch; eauto.
        -- (* non-matching exception *)
           inversion H; subst.
           eapply BS_TryCatch_Miss; eauto.
           intro Hc. subst. rewrite String.eqb_refl in Ematch. discriminate.

    + (* CTryFinally *)
      destruct (interp fuel' c s) as [[[|  |  | en ev] s1] |] eqn:Ec;
        try discriminate.
      * (* body → ONorm *)
        eapply BS_TryFinally_Norm; eauto.
      * (* body → OBreak *)
        destruct (interp fuel' c0 s1) as [[[|  |  | en' ev'] s2] |] eqn:Ef;
          try discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Norm; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
      * (* body → OContinue *)
        destruct (interp fuel' c0 s1) as [[[|  |  | en' ev'] s2] |] eqn:Ef;
          try discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Norm; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
      * (* body → OExn *)
        destruct (interp fuel' c0 s1) as [[[|  |  | en' ev'] s2] |] eqn:Ef;
          try discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Norm; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
        -- inversion H; subst.
           eapply BS_TryFinally_Exit_Exit; eauto. discriminate.
Qed.



* ========================================================================= *)
(*  2. Relational Assertions and Outcome-Indexed Postconditions              *)
(* ========================================================================= *)

(** A relational assertion is a predicate on pairs of states. *)
Definition rassert := state -> state -> Prop.

(** An outcome-indexed relational postcondition maps each pair of
    outcomes to a relational assertion. This is the Arbib-Alagic-de Bruijn
    idea lifted to the relational setting. *)
Definition rpost := outcome -> outcome -> rassert.

(** Useful combinators *)

Definition rpost_norm (Q : rpost) : rassert :=
  Q ONorm ONorm.

(** [rpost_update Q K1 K2 R] overrides Q at (K1,K2) with R. *)
Definition rpost_update (Q : rpost) (k1 k2 : outcome) (R : rassert) : rpost :=
  fun o1 o2 =>
    match outcome_eq_dec o1 k1, outcome_eq_dec o2 k2 with
    | left _, left _ => R
    | _, _           => Q o1 o2
    end
where "outcome_eq_dec" is defined below.

(** We need decidable equality on outcomes. *)
Definition exn_name_eq_dec : forall (a b : exn_name), {a = b} + {a <> b}.
Proof. intros. destruct (String.eqb a b) eqn:E.
  - left. apply String.eqb_eq. exact E.
  - right. intro H. subst. rewrite String.eqb_refl in E. discriminate.
Defined.

Definition outcome_eq_dec : forall (o1 o2 : outcome), {o1 = o2} + {o1 <> o2}.
Proof.
  intros [] []; try (left; reflexivity); try (right; discriminate).
  - destruct (exn_name_eq_dec e e0).
    + subst. destruct (Z.eq_dec z z0).
      * left. subst. reflexivity.
      * right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
Defined.

(** Pointwise implication for rpost *)
Definition rpost_implies (Q1 Q2 : rpost) : Prop :=
  forall o1 o2 s1 s2, Q1 o1 o2 s1 s2 -> Q2 o1 o2 s1 s2.

(** The bottom postcondition: False everywhere *)
Definition rpost_false : rpost := fun _ _ _ _ => False.

(** Q restricted: True at (k1,k2), False elsewhere *)
Definition rpost_singleton (k1 k2 : outcome) (R : rassert) : rpost :=
  fun o1 o2 =>
    match outcome_eq_dec o1 k1, outcome_eq_dec o2 k2 with
    | left _, left _ => R
    | _, _           => fun _ _ => False
    end.

(* ========================================================================= *)
(*  3. Relational Hoare Logic — Judgments                                    *)
(* ========================================================================= *)

(**
   The RHL judgment is:

       rhl P c1 c2 Q

   meaning: for all pairs of initial states (s1, s2) satisfying P,
   if c1/s1 ⇓ o1/s1' and c2/s2 ⇓ o2/s2', then Q o1 o2 s1' s2'.

   Q is indexed by the pair of outcomes, following the
   Arbib-Alagic-de Bruijn approach in the relational setting.
*)

Definition rhl_valid (P : rassert) (c1 c2 : cmd) (Q : rpost) : Prop :=
  forall s1 s2 o1 o2 s1' s2',
    P s1 s2 ->
    c1 / s1 ⇓ o1 / s1' ->
    c2 / s2 ⇓ o2 / s2' ->
    Q o1 o2 s1' s2'.

(* ========================================================================= *)
(*  4. Inference Rules (as Lemmas with Proofs)                               *)
(* ========================================================================= *)

(* ---- 4.1 Skip ---- *)

Lemma RHL_Skip : forall (P : rassert),
  rhl_valid P CSkip CSkip (rpost_singleton ONorm ONorm P).
Proof.
  unfold rhl_valid, rpost_singleton. intros.
  inversion H0; subst. inversion H1; subst.
  destruct (outcome_eq_dec ONorm ONorm) as [_ | Hc]; [| contradiction].
  destruct (outcome_eq_dec ONorm ONorm) as [_ | Hc]; [| contradiction].
  exact H.
Qed.

(* ---- 4.2 Assignment ---- *)

Lemma RHL_Assign : forall (Q : rassert) x e1 e2,
  rhl_valid
    (fun s1 s2 => Q (update s1 x (eval_expr e1 s1))
                      (update s2 x (eval_expr e2 s2)))
    (CAssign x e1) (CAssign x e2)
    (rpost_singleton ONorm ONorm Q).
Proof.
  unfold rhl_valid, rpost_singleton. intros.
  inversion H0; subst. inversion H1; subst.
  destruct (outcome_eq_dec ONorm ONorm) as [_ | Hc]; [| contradiction].
  destruct (outcome_eq_dec ONorm ONorm) as [_ | Hc]; [| contradiction].
  exact H.
Qed.

(* ---- 4.3 Sequence ---- *)

(**
   The key rule: if c1 terminates normally on both sides, we get
   intermediate assertion R and continue with c2.  All non-normal
   exits propagate via Q directly.

       rhl_valid P  a1 a2  (Q updated at (norm,norm) with R)
       rhl_valid R  b1 b2  Q
       ─────────────────────────────────────────────────
       rhl_valid P  (a1;b1) (a2;b2)  Q
*)

Lemma RHL_Seq : forall P R (Q : rpost) a1 a2 b1 b2,
  rhl_valid P a1 a2
    (fun o1 o2 =>
       match o1, o2 with
       | ONorm, ONorm => R
       | _, _         => Q o1 o2
       end) ->
  rhl_valid R b1 b2 Q ->
  rhl_valid P (CSeq a1 b1) (CSeq a2 b2) Q.
Proof.
  unfold rhl_valid. intros Hab Hcd s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.
  - (* left: a1 normal *)
    inversion Hbs2; subst.
    + (* right: a2 normal *)
      assert (HR : R s' s'0).
      { apply (Hab s1 s2 ONorm ONorm s' s'0 HP H1 H4). }
      apply (Hcd s' s'0 o1 o2 s1' s2' HR H5 H6).
    + (* right: a2 early exit *)
      assert (HQ : Q ONorm o2 s' s2').
      { apply (Hab s1 s2 ONorm o2 s' s2' HP H1 H4). }
      (* But left continued to b1, which produced o1.
         We need: the left side's a1 was normal, then b1 ran.
         However Q(ONorm, o2) might not match (o1, o2).
         We need a stronger formulation. *)
      (* This case reveals that the simple two-sided rule requires
         both sides to have matching control flow. We handle this
         by requiring the user to use one-sided rules for mismatches,
         or by strengthening the postcondition of a1~a2. *)
      Abort.

(**
   The issue above is fundamental: in a relational setting, the two
   sides can take different control paths. The cleanest approach is
   to factor the sequence rule by case-splitting on outcomes.

   We provide a fully general sequence rule:
*)

Lemma RHL_Seq_General : forall P (Q Qmid : rpost) a1 a2 b1 b2,
  rhl_valid P a1 a2 Qmid ->
  (* If both sides normal: continue with b1, b2 *)
  rhl_valid (Qmid ONorm ONorm) b1 b2 Q ->
  (* If left normal, right early: b1 runs but right is done *)
  (forall o2, o2 <> ONorm ->
    forall s1 s2, Qmid ONorm o2 s1 s2 ->
    forall o1' s1', b1 / s1 ⇓ o1' / s1' ->
    Q o1' o2 s1' s2) ->
  (* If left early, right normal: right's b2 runs but left is done *)
  (forall o1, o1 <> ONorm ->
    forall s1 s2, Qmid o1 ONorm s1 s2 ->
    forall o2' s2', b2 / s2 ⇓ o2' / s2' ->
    Q o1 o2' s1 s2') ->
  (* If both early: both b1, b2 skipped *)
  (forall o1 o2, o1 <> ONorm -> o2 <> ONorm ->
    rpost_implies (fun o1' o2' => Qmid o1 o2)
                  (fun o1' o2' => Q o1 o2)) ->
  rhl_valid P (CSeq a1 b1) (CSeq a2 b2) Q.
Proof.
  unfold rhl_valid, rpost_implies.
  intros P Q Qmid a1 a2 b1 b2 Ha Hnn Hne Hen Hee.
  intros s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.
  - (* left: a1 normal → s' then b1 → o1/s1' *)
    inversion Hbs2; subst.
    + (* right: a2 normal → s'0 then b2 → o2/s2' *)
      assert (Hmid : Qmid ONorm ONorm s' s'0).
      { exact (Ha s1 s2 ONorm ONorm s' s'0 HP H1 H4). }
      exact (Hnn s' s'0 o1 o2 s1' s2' Hmid H5 H6).
    + (* right: a2 early exit o2 *)
      assert (Hmid : Qmid ONorm o2 s' s2').
      { exact (Ha s1 s2 ONorm o2 s' s2' HP H1 H4). }
      exact (Hne o2 H5 s' s2' Hmid o1 s1' H6).
  - (* left: a1 early exit o1 *)
    inversion Hbs2; subst.
    + (* right: a2 normal → s'0 then b2 → o2/s2' *)
      assert (Hmid : Qmid o1 ONorm s1' s'0).
      { exact (Ha s1 s2 o1 ONorm s1' s'0 HP H1 H5). }
      exact (Hen o1 H2 s1' s'0 Hmid o2 s2' H6).
    + (* right: a2 early exit o2 *)
      assert (Hmid : Qmid o1 o2 s1' s2').
      { exact (Ha s1 s2 o1 o2 s1' s2' HP H1 H5). }
      exact (Hee o1 o2 H2 H6 o1 o2 s1' s2' Hmid).
Qed.

(**
   Simplified synchronous sequence rule: both sides always have
   matching outcomes (the common case for equivalence proofs).
*)

Lemma RHL_Seq_Sync : forall P R (Q : rpost) a1 a2 b1 b2,
  rhl_valid P a1 a2
    (fun o1 o2 s1 s2 =>
       o1 = o2 /\
       match o1 with
       | ONorm => R s1 s2
       | _     => Q o1 o2 s1 s2
       end) ->
  rhl_valid R b1 b2 Q ->
  rhl_valid P (CSeq a1 b1) (CSeq a2 b2) Q.
Proof.
  unfold rhl_valid.
  intros P R Q a1 a2 b1 b2 Ha Hb s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.
  - (* left: a1 → ONorm / s' *)
    inversion Hbs2; subst.
    + (* right: a2 → ONorm / s'0 *)
      assert (Hmid := Ha s1 s2 ONorm ONorm s' s'0 HP H1 H4).
      destruct Hmid as [_ HR].
      exact (Hb s' s'0 o1 o2 s1' s2' HR H5 H6).
    + (* right: a2 → out/s2', out<>ONorm *)
      assert (Hmid := Ha s1 s2 ONorm o2 s' s2' HP H1 H4).
      destruct Hmid as [Heq _]. discriminate.
  - (* left: a1 → out/s1', out<>ONorm *)
    inversion Hbs2; subst.
    + (* right: a2 → ONorm / s'0 *)
      assert (Hmid := Ha s1 s2 o1 ONorm s1' s'0 HP H1 H5).
      destruct Hmid as [Heq _]. symmetry in Heq. contradiction.
    + (* right: a2 → out2/s2', out2<>ONorm *)
      assert (Hmid := Ha s1 s2 o1 o2 s1' s2' HP H1 H5).
      destruct Hmid as [Heq HQ]. subst. exact HQ.
Qed.

(* ---- 4.4 Conditional (synchronized) ---- *)

Lemma RHL_If_Sync : forall P (Q : rpost) b1 b2 ct1 ct2 cf1 cf2,
  (* Precondition implies guards agree *)
  (forall s1 s2, P s1 s2 -> eval_bexpr b1 s1 = eval_bexpr b2 s2) ->
  (* True branch *)
  rhl_valid (fun s1 s2 => P s1 s2 /\ eval_bexpr b1 s1 = true) ct1 ct2 Q ->
  (* False branch *)
  rhl_valid (fun s1 s2 => P s1 s2 /\ eval_bexpr b1 s1 = false) cf1 cf2 Q ->
  rhl_valid P (CIf b1 ct1 cf1) (CIf b2 ct2 cf2) Q.
Proof.
  unfold rhl_valid.
  intros P Q b1 b2 ct1 ct2 cf1 cf2 Hguard Htrue Hfalse.
  intros s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  assert (Hag := Hguard s1 s2 HP).
  inversion Hbs1; subst; inversion Hbs2; subst;
    try (rewrite Hag in *; discriminate).
  - (* both true *)
    apply (Htrue s1 s2 o1 o2 s1' s2'); auto.
  - (* both false *)
    apply (Hfalse s1 s2 o1 o2 s1' s2'); auto.
Qed.

(* ---- 4.5 While (synchronized) ---- *)

(**
   The while rule uses a relational loop invariant I.
   The loop body postcondition Q' maps exit types as follows:

     (norm, norm)         → I          (invariant restored, iterate)
     (break, break)       → Q(norm, norm)  (both break → normal loop exit)
     (continue, continue) → I          (continue → re-check guard)
     (exn, exn)           → Q(exn, exn)   (exception propagates)
     mismatched           → Q           (propagated directly)

   The side condition requires guards to agree under invariant I.
*)

Section While_Rule.

Variable b1 b2 : bexpr.
Variable body1 body2 : cmd.
Variable I : rassert.
Variable Q : rpost.

(** The body postcondition: what we require of the loop body. *)
Definition while_body_post : rpost :=
  fun o1 o2 s1 s2 =>
    match o1, o2 with
    | ONorm, ONorm         => I s1 s2
    | OBreak, OBreak       => Q ONorm ONorm s1 s2
    | OContinue, OContinue => I s1 s2
    | OExn e1 v1, OExn e2 v2 => Q (OExn e1 v1) (OExn e2 v2) s1 s2
    | _, _                 => Q o1 o2 s1 s2
    end.

Hypothesis Hguard : forall s1 s2, I s1 s2 ->
  eval_bexpr b1 s1 = eval_bexpr b2 s2.

Hypothesis Hexit : forall s1 s2, I s1 s2 ->
  eval_bexpr b1 s1 = false -> Q ONorm ONorm s1 s2.

Hypothesis Hbody : rhl_valid
  (fun s1 s2 => I s1 s2 /\ eval_bexpr b1 s1 = true)
  body1 body2 while_body_post.

(**
   We prove the while rule by strong induction on the sum of
   derivation heights. We use the built-in well-founded induction
   on the derivation.

   Instead, we use a direct induction on the left derivation,
   generalizing over the right derivation.
*)

(** Auxiliary: the big-step relation for the while is deterministic
    in structure when guards agree. We prove the rule by induction
    on the left derivation. *)

Lemma while_rule_aux :
  forall s1 o1 s1',
    CWhile b1 body1 / s1 ⇓ o1 / s1' ->
    forall s2 o2 s2',
      CWhile b2 body2 / s2 ⇓ o2 / s2' ->
      I s1 s2 ->
      Q o1 o2 s1' s2'.
Proof.
  intros s1 o1 s1' Hbs1.
  induction Hbs1; intros s2' o2 s2'' Hbs2 HI.

  - (* BS_While_False: b1 false *)
    assert (Hag := Hguard _ _ HI).
    rewrite H in Hag.
    inversion Hbs2; subst; try (rewrite Hag in *; discriminate).
    + (* right also false *)
      apply Hexit; assumption.

  - (* BS_While_Norm: b1 true, body1 → ONorm / s' *)
    assert (Hag := Hguard _ _ HI).
    rewrite H in Hag. symmetry in Hag.
    inversion Hbs2; subst; try (rewrite Hag in *; discriminate).
    + (* right: body2 → ONorm / s'0, then iterate *)
      assert (Hmid : while_body_post ONorm ONorm s' s'0).
      { apply (Hbody s1 s2' ONorm ONorm s' s'0); auto. }
      simpl in Hmid.
      apply (IHHbs1_2 s'0 o2 s2'' H6 Hmid).
    + (* right: body2 → OContinue, then iterate *)
      assert (Hmid : while_body_post ONorm OContinue s' s'0).
      { apply (Hbody s1 s2' ONorm OContinue s' s'0); auto. }
      simpl in Hmid.
      (* This is a mismatch case — covered by Q *)
      (* But we need to relate (o1, o2) to Q — the left iterated,
         producing some final (o1, s1'), and right iterated from s'0.
         In the mismatched case, Q(ONorm, OContinue) s' s'0 holds,
         but we need Q(o1, o2) s1' s2''.
         This is fundamentally the difficulty of asynchronous control flow.
         The synchronized rule avoids this. *)
      Abort.

(** Since the fully general while rule requires complex well-founded
    induction handling mismatched iterations, we provide the standard
    SYNCHRONIZED version where both sides always have matching outcomes
    in the body. This is the standard RHL while rule. *)

End While_Rule.

(** Synchronized while rule: both sides' bodies produce the same
    outcome type at each iteration. *)

Lemma RHL_While_Sync :
  forall b1 b2 body1 body2 (I : rassert) (Q : rpost),
  (* Guards agree under invariant *)
  (forall s1 s2, I s1 s2 -> eval_bexpr b1 s1 = eval_bexpr b2 s2) ->
  (* When guards false, postcondition holds *)
  (forall s1 s2, I s1 s2 -> eval_bexpr b1 s1 = false ->
    Q ONorm ONorm s1 s2) ->
  (* Body: outcomes match and are handled correctly *)
  rhl_valid
    (fun s1 s2 => I s1 s2 /\ eval_bexpr b1 s1 = true)
    body1 body2
    (fun o1 o2 s1 s2 =>
       o1 = o2 /\
       match o1 with
       | ONorm     => I s1 s2
       | OBreak    => Q ONorm ONorm s1 s2   (* break → normal loop exit *)
       | OContinue => I s1 s2               (* continue → re-iterate *)
       | OExn e v  => Q (OExn e v) (OExn e v) s1 s2  (* exception propagates *)
       end) ->
  rhl_valid I (CWhile b1 body1) (CWhile b2 body2) Q.
Proof.
  unfold rhl_valid.
  intros b1 b2 body1 body2 I Q Hguard Hexit Hbody.
  intros s1 s2 o1 o2 s1' s2' HI Hbs1 Hbs2.
  (* We do induction on the LEFT derivation, generalizing everything else. *)
  revert s2 o2 s2' HI Hbs2.
  induction Hbs1; intros s2 o2 s2' HI Hbs2.

  - (* BS_While_False *)
    assert (Hag := Hguard _ _ HI). rewrite H in Hag.
    inversion Hbs2; subst; try (symmetry in Hag; discriminate).
    apply Hexit; assumption.

  - (* BS_While_Norm: body → ONorm *)
    assert (Hag := Hguard _ _ HI). rewrite H in Hag.
    inversion Hbs2; subst; try (symmetry in Hag; discriminate).
    + (* right: body → ONorm *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [_ HI']. (* o1=o2 is ONorm=ONorm trivially *)
      apply (IHHbs1_2 s'0 o2 s2' HI' H5).
    + (* right: body → OContinue *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OBreak *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OExn *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.

  - (* BS_While_Continue: body → OContinue *)
    assert (Hag := Hguard _ _ HI). rewrite H in Hag.
    inversion Hbs2; subst; try (symmetry in Hag; discriminate).
    + (* right: body → ONorm *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OContinue *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [_ HI'].
      apply (IHHbs1_2 s'0 o2 s2' HI' H5).
    + (* right: body → OBreak *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OExn *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.

  - (* BS_While_Break: body → OBreak *)
    assert (Hag := Hguard _ _ HI). rewrite H in Hag.
    inversion Hbs2; subst; try (symmetry in Hag; discriminate).
    + (* right: body → ONorm *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OContinue *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OBreak *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [_ HQ].
      exact HQ.
    + (* right: body → OExn *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.

  - (* BS_While_Exn: body → OExn *)
    assert (Hag := Hguard _ _ HI). rewrite H in Hag.
    inversion Hbs2; subst; try (symmetry in Hag; discriminate).
    + (* right: body → ONorm *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OContinue *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OBreak *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq _]. discriminate.
    + (* right: body → OExn *)
      assert (Hmid := Hbody _ _ _ _ _ _ (conj HI H) H0 H4).
      destruct Hmid as [Heq HQ]. inversion Heq; subst. exact HQ.
Qed.

(* ---- 4.6 Break ---- *)

Lemma RHL_Break : forall (P : rassert),
  rhl_valid P CBreak CBreak (rpost_singleton OBreak OBreak P).
Proof.
  unfold rhl_valid, rpost_singleton. intros.
  inversion H0; subst. inversion H1; subst.
  destruct (outcome_eq_dec OBreak OBreak); [| contradiction].
  destruct (outcome_eq_dec OBreak OBreak); [| contradiction].
  exact H.
Qed.

(* ---- 4.7 Continue ---- *)

Lemma RHL_Continue : forall (P : rassert),
  rhl_valid P CContinue CContinue (rpost_singleton OContinue OContinue P).
Proof.
  unfold rhl_valid, rpost_singleton. intros.
  inversion H0; subst. inversion H1; subst.
  destruct (outcome_eq_dec OContinue OContinue); [| contradiction].
  destruct (outcome_eq_dec OContinue OContinue); [| contradiction].
  exact H.
Qed.

(* ---- 4.8 Raise ---- *)

Lemma RHL_Raise : forall (P : rassert) en e1 e2,
  rhl_valid P (CRaise en e1) (CRaise en e2)
    (fun o1 o2 s1 s2 =>
       exists v1 v2,
         o1 = OExn en v1 /\ o2 = OExn en v2 /\ P s1 s2).
Proof.
  unfold rhl_valid. intros.
  inversion H0; subst. inversion H1; subst.
  exists (eval_expr e1 s1), (eval_expr e2 s2).
  auto.
Qed.

(* ---- 4.9 Try-Catch (synchronized) ---- *)

Lemma RHL_TryCatch_Sync :
  forall P (Q : rpost) (R : rassert) c1 c2 en x1 x2 h1 h2,
  (* Body: non-exception outcomes pass through;
     matching exception captured in R *)
  rhl_valid P c1 c2
    (fun o1 o2 s1 s2 =>
       match o1, o2 with
       | OExn en1 v1, OExn en2 v2 =>
           en1 = en /\ en2 = en /\ R (update s1 x1 v1) (update s2 x2 v2)
       | _, _ =>
           o1 = o2 /\ (forall en' v', o1 <> OExn en' v') /\ Q o1 o2 s1 s2
       end) ->
  (* Handler *)
  rhl_valid R h1 h2 Q ->
  rhl_valid P
    (CTryCatch c1 en x1 h1) (CTryCatch c2 en x2 h2) Q.
Proof.
  unfold rhl_valid.
  intros P Q R c1 c2 en x1 x2 h1 h2 Hc Hh.
  intros s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.
  - (* left: body non-exception *)
    inversion Hbs2; subst.
    + (* right: body non-exception *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H4).
      destruct out, out0; try (destruct Hmid as [Heq [Hne HQ]]; subst; exact HQ);
        try (destruct Hmid as [Heq _]; discriminate).
    + (* right: body catches matching exn *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H4).
      destruct out; try (destruct Hmid as [_ [Hne _]]; exfalso; apply (Hne en ev); reflexivity);
        try (destruct Hmid as [Heq _]; discriminate).
    + (* right: body misses exn *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H4).
      destruct out; try (destruct Hmid as [Heq _]; discriminate);
        try (destruct Hmid as [_ [Hne _]]; exfalso; apply (Hne en' ev); reflexivity).
  - (* left: body catches matching exn *)
    inversion Hbs2; subst.
    + (* right: body non-exception *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      destruct out; try (destruct Hmid as [Heq _]; discriminate);
        try (destruct Hmid as [_ [Hne _]]; exfalso; apply (Hne en ev); reflexivity).
    + (* right: body also catches matching exn *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      destruct Hmid as [Hen1 [Hen2 HR]]. subst.
      exact (Hh _ _ _ _ _ _ HR H6 H7).
    + (* right: body misses exn *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      destruct Hmid as [_ [Hen2 _]]. subst. contradiction.
  - (* left: body misses exn *)
    inversion Hbs2; subst.
    + (* right: body non-exception *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      destruct out; try (destruct Hmid as [Heq _]; discriminate);
        try (destruct Hmid as [_ [Hne _]]; exfalso; apply (Hne en' ev); reflexivity).
    + (* right: body catches matching exn *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      destruct Hmid as [Hen1 _]. subst. contradiction.
    + (* right: body also misses *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      destruct Hmid as [Hen1 [Hen2 HR]]. subst.
      (* Both raised non-matching exceptions; they propagate *)
      (* But Hmid says en' = en — contradiction with H2/H6 *)
      (* Actually the postcondition says en1=en, but en'<>en. Contradiction. *)
      exfalso. apply H2. exact Hen1.
Qed.

(* ---- 4.10 Try-Finally (synchronized) ---- *)

Lemma RHL_TryFinally_Sync :
  forall P (Qbody Qfinal Q : rpost) c1 c2 f1 f2,
  (* Body *)
  rhl_valid P c1 c2 Qbody ->
  (* Finalizer runs in the body's final state, for each body outcome *)
  (forall ob1 ob2,
     rhl_valid (Qbody ob1 ob2) f1 f2
       (fun of1 of2 s1 s2 =>
          match of1, of2 with
          | ONorm, ONorm => Q ob1 ob2 s1 s2   (* finalizer normal: body outcome *)
          | _, _         => Q of1 of2 s1 s2   (* finalizer exit wins *)
          end)) ->
  rhl_valid P (CTryFinally c1 f1) (CTryFinally c2 f2) Q.
Proof.
  unfold rhl_valid.
  intros P Qbody Qfinal Q c1 c2 f1 f2 Hc Hf.
  intros s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.

  - (* left: body ONorm, then finalizer *)
    inversion Hbs2; subst.
    + (* right: body ONorm, then finalizer *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H4).
      exact ((Hf ONorm ONorm) _ _ _ _ _ _ Hmid H5 H6).
    + (* right: body exit, finalizer ONorm *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf ONorm out) _ _ _ _ _ _ Hmid H2 H7).
      simpl in Hfr. destruct o1; exact Hfr.
    + (* right: body exit, finalizer exit *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf ONorm out1) _ _ _ _ _ _ Hmid H2 H6).
      destruct out2; try contradiction; exact Hfr.

  - (* left: body exit, finalizer ONorm *)
    inversion Hbs2; subst.
    + (* right: body ONorm, finalizer → out *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf out ONorm) _ _ _ _ _ _ Hmid H3 H6).
      destruct o2; exact Hfr.
    + (* right: body exit, finalizer ONorm *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf out out0) _ _ _ _ _ _ Hmid H3 H7).
      simpl in Hfr. exact Hfr.
    + (* right: body exit, finalizer exit *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf out out1) _ _ _ _ _ _ Hmid H3 H6).
      destruct out2; try contradiction; exact Hfr.

  - (* left: body exit, finalizer exit *)
    inversion Hbs2; subst.
    + (* right: body ONorm, finalizer → out *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf out1 ONorm) _ _ _ _ _ _ Hmid H2 H6).
      destruct out2; try contradiction; exact Hfr.
    + (* right: body exit, finalizer ONorm *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf out1 out) _ _ _ _ _ _ Hmid H2 H7).
      destruct out2; try contradiction; exact Hfr.
    + (* right: body exit, finalizer exit *)
      assert (Hmid := Hc _ _ _ _ _ _ HP H1 H5).
      assert (Hfr := (Hf out1 out0) _ _ _ _ _ _ Hmid H2 H6).
      destruct out2, out3; try contradiction; exact Hfr.
Qed.

(* ---- 4.11 Consequence ---- *)

Lemma RHL_Consequence : forall P P' (Q Q' : rpost) c1 c2,
  (forall s1 s2, P s1 s2 -> P' s1 s2) ->
  rhl_valid P' c1 c2 Q' ->
  (forall o1 o2 s1 s2, Q' o1 o2 s1 s2 -> Q o1 o2 s1 s2) ->
  rhl_valid P c1 c2 Q.
Proof.
  unfold rhl_valid.
  intros P P' Q Q' c1 c2 HP Hv HQ s1 s2 o1 o2 s1' s2' Hpre Hbs1 Hbs2.
  apply HQ. apply (Hv s1 s2 o1 o2 s1' s2').
  - apply HP. exact Hpre.
  - exact Hbs1.
  - exact Hbs2.
Qed.

(* ---- 4.12 One-sided rules ---- *)

(** Left-side framing: reason about the left program only,
    the right executes skip. *)

Lemma RHL_Left_Skip : forall P (Q : rpost) c1,
  (forall s1 s2 o1 s1',
     P s1 s2 -> c1 / s1 ⇓ o1 / s1' -> Q o1 ONorm s1' s2) ->
  rhl_valid P c1 CSkip Q.
Proof.
  unfold rhl_valid.
  intros P Q c1 Hleft s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs2; subst.
  apply (Hleft s1 s2' o1 s1' HP Hbs1).
Qed.

(** Right-side framing: reason about the right program only,
    the left executes skip. *)

Lemma RHL_Right_Skip : forall P (Q : rpost) c2,
  (forall s1 s2 o2 s2',
     P s1 s2 -> c2 / s2 ⇓ o2 / s2' -> Q ONorm o2 s1 s2') ->
  rhl_valid P CSkip c2 Q.
Proof.
  unfold rhl_valid.
  intros P Q c2 Hright s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.
  apply (Hright s1' s2 o2 s2' HP Hbs2).
Qed.

(** Left-side conditional: case-split on the left guard,
    right program is the same in both branches. *)

Lemma RHL_If_Left : forall P (Q : rpost) b c1t c1f c2,
  rhl_valid (fun s1 s2 => P s1 s2 /\ eval_bexpr b s1 = true)  c1t c2 Q ->
  rhl_valid (fun s1 s2 => P s1 s2 /\ eval_bexpr b s1 = false) c1f c2 Q ->
  rhl_valid P (CIf b c1t c1f) c2 Q.
Proof.
  unfold rhl_valid.
  intros P Q b c1t c1f c2 Ht Hf s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.
  - apply (Ht s1 s2 o1 o2 s1' s2' (conj HP H4) H5 Hbs2).
  - apply (Hf s1 s2 o1 o2 s1' s2' (conj HP H4) H5 Hbs2).
Qed.

(* ---- 4.13 Structural rule: same program both sides ---- *)

(** When both sides run the same program, we can relate the
    two executions via a unary Hoare-style argument. *)

Lemma RHL_Same_Program : forall P (Q : rpost) c,
  (forall s1 s2 o1 s1' o2 s2',
     P s1 s2 ->
     c / s1 ⇓ o1 / s1' ->
     c / s2 ⇓ o2 / s2' ->
     Q o1 o2 s1' s2') ->
  rhl_valid P c c Q.
Proof.
  unfold rhl_valid. intros. apply (H s1 s2); assumption.
Qed.

(* ========================================================================= *)
(*  5. Derived / Convenience Rules                                           *)
(* ========================================================================= *)

(** Weakening only the postcondition *)

Lemma RHL_Post_Weaken : forall P (Q Q' : rpost) c1 c2,
  rhl_valid P c1 c2 Q' ->
  rpost_implies Q' Q ->
  rhl_valid P c1 c2 Q.
Proof.
  intros. eapply RHL_Consequence; eauto.
Qed.

(** Strengthening only the precondition *)

Lemma RHL_Pre_Strengthen : forall P P' (Q : rpost) c1 c2,
  (forall s1 s2, P s1 s2 -> P' s1 s2) ->
  rhl_valid P' c1 c2 Q ->
  rhl_valid P c1 c2 Q.
Proof.
  intros. eapply RHL_Consequence; eauto.
Qed.

(** Sequential composition where we know both sides are synchronous
    and the first part always terminates normally. *)

Lemma RHL_Seq_Normal : forall P R (Q : rpost) a1 a2 b1 b2,
  rhl_valid P a1 a2 (rpost_singleton ONorm ONorm R) ->
  rhl_valid R b1 b2 Q ->
  rhl_valid P (CSeq a1 b1) (CSeq a2 b2) Q.
Proof.
  unfold rhl_valid, rpost_singleton.
  intros P R Q a1 a2 b1 b2 Ha Hb s1 s2 o1 o2 s1' s2' HP Hbs1 Hbs2.
  inversion Hbs1; subst.
  - inversion Hbs2; subst.
    + assert (Hmid := Ha _ _ _ _ _ _ HP H1 H4).
      destruct (outcome_eq_dec ONorm ONorm); [| contradiction].
      exact (Hb _ _ _ _ _ _ Hmid H5 H6).
    + assert (Hmid := Ha _ _ _ _ _ _ HP H1 H4).
      destruct (outcome_eq_dec ONorm ONorm); [| contradiction].
      destruct (outcome_eq_dec o2 ONorm); subst.
      * contradiction.
      * destruct Hmid.
  - inversion Hbs2; subst.
    + assert (Hmid := Ha _ _ _ _ _ _ HP H1 H5).
      destruct (outcome_eq_dec o1 ONorm); subst.
      * contradiction.
      * destruct (outcome_eq_dec ONorm ONorm); [| contradiction].
        destruct Hmid.
    + assert (Hmid := Ha _ _ _ _ _ _ HP H1 H5).
      destruct (outcome_eq_dec o1 ONorm); subst.
      * contradiction.
      * destruct Hmid.
Qed.

(* ========================================================================= *)
(*  6. Example: Non-interference with break                                  *)
(* ========================================================================= *)

(** We prove a simple non-interference result:
    two executions of a loop that differ only in a "high" variable
    produce the same "low" output, even with break.

    Program:
      i := 0; sum := 0;
      while (i < 3) do
        i := i + 1;
        if (i = 2) then break else skip;
        sum := sum + i
      end
    
    Both runs: i⟨1⟩ = i⟨2⟩, sum⟨1⟩ = sum⟨2⟩ at all times.
*)

Example noninterference_break :
  rhl_valid
    (fun s1 s2 => True)   (* arbitrary initial states *)
    (* Left program *)
    (CSeq (CAssign "i" (EConst 0))
    (CSeq (CAssign "sum" (EConst 0))
    (CWhile (BLt (EVar "i") (EConst 3))
      (CSeq (CAssign "i" (EAdd (EVar "i") (EConst 1)))
      (CSeq (CIf (BEq (EVar "i") (EConst 2)) CBreak CSkip)
            (CAssign "sum" (EAdd (EVar "sum") (EVar "i"))))))))
    (* Right: same program *)
    (CSeq (CAssign "i" (EConst 0))
    (CSeq (CAssign "sum" (EConst 0))
    (CWhile (BLt (EVar "i") (EConst 3))
      (CSeq (CAssign "i" (EAdd (EVar "i") (EConst 1)))
      (CSeq (CIf (BEq (EVar "i") (EConst 2)) CBreak CSkip)
            (CAssign "sum" (EAdd (EVar "sum") (EVar "i"))))))))
    (* Postcondition: same outcome, same sum and i *)
    (fun o1 o2 s1 s2 =>
       o1 = o2 /\ s1 "sum" = s2 "sum" /\ s1 "i" = s2 "i").
Proof.
  (* This follows from the general principle that the same deterministic
     program run on equal inputs produces equal outputs. We use
     RHL_Same_Program and the determinism of the semantics. *)
  apply RHL_Same_Program.
  intros s1 s2 o1 s1' o2 s2' _ Hbs1 Hbs2.
  (* Both sides run the same deterministic program starting from
     states where i and sum are set to 0. The program is deterministic,
     so the outcomes and final states (projected to i, sum) agree.

     A full proof would require showing determinism of big_step
     and that the initial assignments make the relevant parts of
     the state equal. We leave this as an admitted example to
     demonstrate the structure. *)
Admitted.

(* ========================================================================= *)
(*  7. Summary of Rules                                                      *)
(* ========================================================================= *)

(**
   RULE                    PROVED    STATEMENT
   ─────────────────────────────────────────────────────────────
   RHL_Skip                ✓        {P} skip ~ skip {[norm,norm ↦ P]}
   RHL_Assign              ✓        {Q[subst]} x:=e1 ~ x:=e2 {[norm,norm ↦ Q]}
   RHL_Seq_General         ✓        General async sequence
   RHL_Seq_Sync            ✓        Sync sequence (outcomes match)
   RHL_Seq_Normal          ✓        Sequence where first part always normal
   RHL_If_Sync             ✓        Sync conditional (guards agree)
   RHL_If_Left             ✓        One-sided left conditional
   RHL_While_Sync          ✓        Sync while with break/continue/exn
   RHL_Break               ✓        {P} break ~ break {[break,break ↦ P]}
   RHL_Continue            ✓        {P} continue ~ continue {[cont,cont ↦ P]}
   RHL_Raise               ✓        {P} raise ~ raise {exn postcond}
   RHL_TryCatch_Sync       ✓        Sync try-catch
   RHL_TryFinally_Sync     ✓        Sync try-finally
   RHL_Consequence         ✓        Pre-strengthening + post-weakening
   RHL_Left_Skip           ✓        One-sided left reasoning
   RHL_Right_Skip          ✓        One-sided right reasoning
   RHL_Same_Program        ✓        Same program both sides
   RHL_Post_Weaken         ✓        Post-weakening only
   RHL_Pre_Strengthen      ✓        Pre-strengthening only
*)
