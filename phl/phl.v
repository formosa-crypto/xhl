(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp           Require Import all_boot all_order.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.
From xhl.strassen Require Import misc.

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
Implicit Types P Q S I : assn.
Implicit Types c       : cmd.
Implicit Types d       : R.
Implicit Types ps     : ident -> (@cmd_ ident cmem ident).

(* -------------------------------------------------------------------- *)
Variant bd := Le | Ge | Eq.

Implicit Types r : bd.

Definition rel_of_bd (r : bd) : rel R :=
  match r with
  | Le => [rel x y | x <= y]
  | Ge => [rel x y | y <= x]
  | Eq => [rel x y | x == y]
  end.

Coercion rel_of_bd : bd >-> rel.

Declare Scope bd_scope.

Notation "'="  := Eq (at level 0) : bd_scope.
Notation "'<=" := Le (at level 0) : bd_scope.
Notation "'>=" := Ge (at level 0) : bd_scope.

Bind Scope bd_scope with bd.

Section PHL.
Context ps.

(* -------------------------------------------------------------------- *)
Definition phl P c Q r d :=
  forall m : cmem, P m -> r (\P_[ssem_ ps c m] Q) d.

Arguments phl _%_assn _%_syn_scope _%_assn _%_bd_scope _%_ring_scope.

(* -------------------------------------------------------------------- *)
Lemma phl_skip P c : phl P skip P '= 1.
Proof. by move=> m Pm /=; rewrite ssemE pr_dunit Pm. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_abort : phl predT abort pred0 '= 0.
Proof. by move=> m _ /=; rewrite !ssemE pr_pred0. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_conseq_eq P P' Q c d :
     (forall m, P m -> P' m)
  -> phl P' c Q '= d
  -> phl P  c Q '= d.
Proof. by move=> leP ih m Pm /=; apply/ih/leP. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_conseq_le P P' Q Q' c d d' :
     (forall m, P m -> P' m)
  -> (forall m, Q m -> Q' m)
  -> d' <= d
  -> phl P' c Q' '<= d'
  -> phl P  c Q  '<= d.
Proof.
move=> leP leQ + ih m Pm => /(le_trans _); apply.
apply/(le_trans _ (ih m _))/leP => //.
by apply/le_in_pr => m' _; apply/leQ.
Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_conseq_ge P P' Q Q' c d d' :
     (forall m, P  m -> P' m)
  -> (forall m, Q' m -> Q  m)
  -> d <= d'
  -> phl P' c Q' '>= d'
  -> phl P  c Q  '>= d.
Proof.
move=> leP leQ led + m Pm => /(_ m (leP _ Pm)) /= ih.
apply/(le_trans led)/(le_trans ih)/le_in_pr.
by move=> m' _; apply/leQ.
Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_conseq_eq_le P c Q d :
  phl P c Q '= d -> phl P c Q '<= d.
Proof. by move=> ih m /ih /= /eqP->. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_conseq_eq_ge P c Q d :
  phl P c Q '= d -> phl P c Q '>= d.
Proof. by move=> ih m /ih /= /eqP->. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_conseq_lege_eq P c Q d :
  phl P c Q '<= d -> phl P c Q '>= d -> phl P c Q '= d.
Proof.
move=> hle hge m Pm /=; rewrite eq_le.
by have [/= -> ->] := (hle m Pm, hge m Pm).
Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_ge0 P c Q : phl P c Q '>= 0.
Proof. by move=> m _ /=; apply/ge0_pr. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_le1 P c Q : phl P c Q '<= 1.
Proof. by move=> m _ /=; apply/le1_pr. Qed.

(* -------------------------------------------------------------------- *)
(* ----------------  This would go in distr.v  ------------------------ *)
Lemma has_esp_pr P Q c1 c2 m: \E?_[ssem_ ps c1 m] (fun x : cmem => \P_[ssem_ ps c2 x] Q).
Proof.
  apply bounded_has_exp.
  exists 1. move => ?; rewrite ger0_norm.
  + exact: ge0_pr.
  by exact: le1_pr.
Qed.

Lemma espcE {T: choiceType} mu (f : T -> R)  A :
   espc mu f A = esp (drestr A mu) f / \P_[mu] A .
Proof.
  rewrite /espc.
  erewrite eq_sum; last first.
  * move => x;rewrite mulrA mulrC; reflexivity.
  rewrite sumZ mulrC.
  congr (_ * _).
  rewrite /esp.
  apply eq_sum => x.
  congr (_ * _).
  rewrite pr_pred1 -pr_drestr /pr.
  apply eq_psum => r.
  rewrite !drestrE.
  by case (pred1 x r); case (A r); rewrite !Monoid.simpm.
Qed.

Lemma mass_drestr {T: choiceType} (mu : {distr T / R}) A  : \P_[drestr A mu] predT = \P_[mu] A.
Proof.
 rewrite pr_drestr /pr.
 apply eq_psum => x.
 congr (_ *_).
 by rewrite /in_mem /= andbC andTb.
Qed.

(* -------------------------------------------------------------------- *)

Lemma phl_seq_eq R P Q c1 c2 dR dNR dRQ dNRQ d :
     d = dR * dRQ + dNR * dNRQ
  -> phl P     c1 R     '= dR
  -> phl P     c1 (~ R) '= dNR
  -> phl R     c2 Q     '= dRQ
  -> phl (~ R) c2 Q     '= dNRQ

  -> phl P (c1 ;; c2) Q '= d.
Proof.
move=> -> PR PNR RQ NRQ m Pm /=; rewrite ssemE pr_dlet.
apply/eqP; rewrite (exp_split R); first by apply: has_esp_pr.
have [/= /eqP-> /eqP->] := (PR _ Pm, PNR _ Pm); congr (_ + _).
- case: (dR =P 0) => [->|/eqP nz_dR]; first by rewrite !mul0r.
  congr (_ * _). rewrite espcE. rewrite -(@eq_exp _ _ _ (fun=> dRQ)).
  - move=> m'; rewrite dinsupp_restr => /andP [_ Rm'].
    by apply/esym/eqP ; apply: (RQ m' Rm').
    by rewrite exp_cst mass_drestr  mulrAC divff ?mul1r // (eqP (PR m Pm)).
- case: (dNR =P 0) => [->|/eqP nz_dNR]; first by rewrite !mul0r.
  congr (_ * _); rewrite espcE; rewrite -(@eq_exp _ _ _ (fun=> dNRQ)).
  - move=> m'; rewrite dinsupp_restr => /andP[_ Rm'].
    by apply/esym/eqP; apply: (NRQ m' Rm').
  by rewrite exp_cst mass_drestr mulrAC divff ?mul1r // (eqP (PNR m Pm)).
Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_assgn {T : IhbType.type} Q x (e : expr T) :
  phl (fun m => Q m.[x <- `[{e}] m]) (x <<- e) Q '= 1.
Proof. by move=> m Qm /=; rewrite !ssemE pr_dunit Qm. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_rnd {T : IhbType.type} Q x (e : dexpr T) d :
  let P m :=
    \P_[\dlet_(v <- `[{e}] m) (dunit m.[x <- v])] Q == d
  in phl P (x <$- e) Q '= d.
Proof. by move=> P m Pm /=; rewrite !ssemE; apply: Pm. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_if P (e : bexpr) c1 c2 Q r d :
     phl (P /\   `[{e}]) c1 Q r d
  -> phl (P /\ ~ `[{e}]) c2 Q r d
  -> phl P (If e then c1 else c2) Q r d.
Proof.
move=> hT hF m Pm; case/boolP: (`[{e}] m) => em.
- by rewrite !ssemE em hT //= Pm.
- by rewrite !ssemE (negbTE em) hF //= Pm.
Qed.

End PHL.

(* -------------------------------------------------------------------- *)

From xhl.hl Require hl.

(** Definition of a procedure contract **)

Definition clause : Type := assn * assn * R.

Definition get_pre (an:clause) :=
  let (an,_) := an in
  let (pre,_) := an in
  pre.

Definition get_post (an:clause) :=
  let (an,_) := an in
  let (_,post) := an in
  post.

Definition get_r (an:clause) :=
  let (_,r) := an in
  r.

Definition phi : Type := ident -> clause.

(* -------------------------------------------------------------------- *)
(* Left *)
(* -------------------------------------------------------------------- *)

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx_l (cl : phi) ps (P: assn) (Q: assn) (r:R) (c: cmd) :=
  (forall p, phl ps (get_pre (cl p)) (call p) (get_post (cl p)) Le (get_r (cl p))) ->
  phl ps P c Q Le r.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx_l (cl : phi) (ps_init: ident -> (@cmd_ ident cmem ident)):=
  forall p ps, hoare_triple_ctx_l cl ps
            (get_pre (cl p))
            (get_post (cl p))
            (get_r (cl p))
            (ps_init p).

Lemma sum_dlim_r_r (f: nat -> {distr cmem /R}) [E : pred cmem]  [r : R]:
  (forall n m : nat, (n <= m)%N -> forall x : cmem, f n x <= f m x) ->
  (forall (n : nat), psum (fun x : cmem => ((E x)%:R * f n x)) <= r) ->
  (psum (fun x : cmem => ((E x)%:R * (\dlim_(n) (f n) ) x)) <= r).
Proof.
Admitted.

Lemma recursive_proc_l ps' cl' :
  (forall p, 0 <= (get_r (cl' p))) ->
  hoare_triple_proc_ctx_l cl' ps' ->
  (forall p, phl ps' (get_pre (cl' p))
          (call p)
          (get_post (cl' p))
          Le
          (get_r (cl' p))).
Proof.
  move => H h p s hP.
   rewrite /pr !test8.
   apply sum_dlim_r_r.
    + move => ????.
     apply mono_ssem_aux.
     by apply homo_ubnf.
  move => n.
  rewrite ssem_ubnf_dnull ubnf_ssem (test9 _ _ _ _ ps') test5.
  revert hP; revert p; revert s.
  elim : n => [| n Hn].
  + move => ???. rewrite ssem_false_ps.
    under eq_psum do  rewrite dnullE mulr0.
    by rewrite psum0.
  move => s p hP.
  rewrite (inline2_split n 1).
  apply: h => // p0 s0 hP0.
  by apply: Hn.
Qed.

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple_l :
  forall P Q c cl ps (r:R),
    (forall p, 0 <= (get_r (cl p))) ->
    hoare_triple_proc_ctx_l cl ps  ->
    hoare_triple_ctx_l cl ps P Q r c ->
    phl ps P c Q Le r.
Proof.
  move => ?????? Hcl H H0.
  apply H0.
  by apply: recursive_proc_l.
Qed.

(* -------------------------------------------------------------------- *)
(* Rigth *)
(* -------------------------------------------------------------------- *)

(* (** Hoare triple for a com with procedure context **) *)

(* Definition hoare_triple_ctx_r (cl : phi) ps (P: assn) (Q: assn) (r:R) (c: cmd) := *)
(*   (forall p, phl ps (get_pre (cl p)) (call p) (get_post (cl p)) Ge (get_r (cl p))) -> *)
(*   phl ps P c Q Ge r. *)

(* (** Hoare triple for a procedure with procedure context **) *)

(* Definition hoare_triple_proc_ctx_r (cl : phi) (ps_init: ident -> (@cmd_ ident cmem ident)):= *)
(*   forall p ps, hoare_triple_ctx_r cl ps *)
(*             (get_pre (cl p)) *)
(*             (get_post (cl p)) *)
(*             (get_r (cl p)) *)
(*             (ps_init p). *)

(* Lemma sum_dlim_l_r (f: nat -> {distr cmem /R}) [E : pred cmem]  [r : R]: *)
(*   (forall n m : nat, (n <= m)%N -> forall x : cmem, f n x <= f m x) -> *)
(*   (exists n,  r <= psum (fun x : cmem => ((E x)%:R * f n x))) -> *)
(*   (r <= psum (fun x : cmem => ((E x)%:R * (\dlim_(n) (f n) ) x))). *)
(* Proof. *)
(* Admitted. *)

(* (*The program is lossless, then we can bound*) *)

(* Lemma recursive_proc_r ps' cl' : *)
(*   hoare_triple_proc_ctx_r cl' ps' -> *)
(*   (forall p, phl ps' (get_pre (cl' p)) *)
(*           (call p) *)
(*           (get_post (cl' p)) *)
(*           Ge *)
(*           (get_r (cl' p))). *)
(* Proof. *)
(*   move => h p s hP //=. *)
(*   rewrite /pr !hl.test8. *)
(*    apply sum_dlim_l_r. *)
(*     + move => ????. *)
(*      apply mono_ssem_aux. *)
(*      by apply homo_ubnf. *)
(*   move => n. *)
(*   rewrite hl.ssem_ubnf_dnull hl.ubnf_ssem (hl.test9 _ _ _ _ ps') hl.test5. *)
(*   revert hP; revert p; revert s. *)
(*   elim : n => [| n Hn]. *)
(*   + move => ???. rewrite hl.ssem_false_ps. *)
(*     under eq_psum do  rewrite dnullE mulr0. *)
(*     by rewrite psum0. *)
(*   move => s p hP. *)
(*   rewrite (hl.inline2_split n 1). *)
(*   apply: h => // p0 s0 hP0. *)
(*   by apply: Hn. *)
(* Qed. *)

(* (** Modular Hoare Triple Verification **) *)

(* Theorem recursion_hoare_triple_r : *)
(*   forall P Q c cl ps (r:R), *)
(*     hoare_triple_proc_ctx_r cl ps  -> *)
(*     hoare_triple_ctx_r cl ps P Q r c -> *)
(*     phl ps P c Q Ge r. *)
(* Proof. *)
(*   move => ?????? H H0. *)
(*   apply H0. *)
(*   by apply: recursive_proc_r. *)
(* Qed. *)
