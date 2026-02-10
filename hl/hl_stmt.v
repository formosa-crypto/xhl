(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope sem_scope.
Local Open Scope mem_scope.

(* -------------------------------------------------------------------- *)
Section hl.
Context {X Y : eqType} {mem : memType X}.

Definition assn := (pred mem).
Definition assn2 := (mem -> pred mem).

Definition forall_in {T : IhbType.type} (mu : mem -> Distr T) (P : T -> assn) : assn :=
  `[< fun m => forall t,  t \in dinsupp (mu m) -> P t m >]%A.

Definition cmd  := (@cmd_ X mem Y).
Definition psi := Y -> cmd.

(* -------------------------------------------------------------------- *)
(* Classical Hoare triple                                               *)
(* -------------------------------------------------------------------- *)

Definition hl_ (ps: psi) (P : assn) (c : cmd) (Q : assn) :=
  forall m, P m -> range Q (ssem_ ps c m).

Arguments hl_ ps P%_A c%_S Q%_A.

(* -------------------------------------------------------------------- *)
(* Generic Hoare triple                                                 *)
(* -------------------------------------------------------------------- *)

Definition khl_ (ps: psi) (P : assn) (c : cmd) (Q : assn2) :=
  forall m, P m -> range (Q m) (ssem_ ps c m).

Arguments khl_ ps P%_A c%_S Q%_A.

Lemma khl_hl ps P c Q :
  khl_ ps P c Q <-> (forall s0, hl_ ps (xpredI P (fun s => s == s0)) c (Q s0)).
Proof.
  split.
  + by move=> h s0 ? /andP [] ? /eqP ?; subst s0; apply h.
    move => h s hP.
    apply: (h s).
    by apply/andP.
Qed.

Lemma hl_khl ps P c Q :
  khl_ ps P c (fun _ => Q) <-> hl_ ps P c Q.
Proof.
  by split; move => h s hP; apply h.
Qed.

Lemma khl_khl ps P c Q :
  khl_ ps xpredT c (fun s0 s => P s0 ==> Q s0 s) <-> khl_ ps P c Q.
Proof.
  split.
  + move => h s HP.
  have := (h s isT).
  rewrite /range => H m He.
  revert HP.
  apply /implyP.
  by apply H.
  + move => h s HP.
  have := (h s).
  rewrite /range => H m He.
  apply /implyP => ?.
  by apply: H.
Qed.

(* -------------------------------------------------------------------- *)
(* Procedire contract                                                   *)
(* -------------------------------------------------------------------- *)

Definition clause : Type := assn * assn2.

Definition get_pre (an:clause) :=
  let (pre,post) := an in
  pre.

Definition get_post (an:clause) :=
  let (pre,post) := an in
  post.

Definition phi : Type := Y -> clause.

(** Empty procedure contract **)

Definition empty_precondition : assn := xpred0.

Definition empty_postcondition :  assn2 := (fun _ => xpredT).

Definition empty_clause : clause := (empty_precondition, empty_postcondition).

Definition empty_phi: phi := fun _ => empty_clause.

End hl.
