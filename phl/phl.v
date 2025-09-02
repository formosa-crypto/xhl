(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis  Require Import ereal reals realseq realsum distr.
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
Implicit Types P Q S I : assn.
Implicit Types c       : cmd.
Implicit Types d       : R.

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

(* -------------------------------------------------------------------- *)
Definition phl P c Q r d :=
  forall m : cmem, P m -> r (\P_[ssem c m] Q) d.

Arguments phl _%assn _%syn_scope _%assn _%bd_scope _%ring_scope.

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
  congr (_ * _); rewrite espcE; rewrite -(@eq_exp _ _ _ (fun=> dRQ)).
  - move=> m'; rewrite dinsupp_restr => /andP[_ Rm'].
    by apply/esym/eqP; apply: (RQ m' Rm').
  by rewrite exp_cst mass_drestr mulrAC divff ?mul1r // (eqP (PR m Pm)).
- case: (dNR =P 0) => [->|/eqP nz_dNR]; first by rewrite !mul0r.
  congr (_ * _); rewrite espcE; rewrite -(@eq_exp _ _ _ (fun=> dNRQ)).
  - move=> m'; rewrite dinsupp_restr => /andP[_ Rm'].
    by apply/esym/eqP; apply: (NRQ m' Rm').
  by rewrite exp_cst mass_drestr mulrAC divff ?mul1r // (eqP (PNR m Pm)).
Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_assgn {T : ihbType} Q x (e : expr T) :
  phl (fun m => Q m.[x <- `[{e}] m]) (x <<- e) Q '= 1.
Proof. by move=> m Qm /=; rewrite !ssemE pr_dunit Qm. Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_rnd {T : ihbType} Q x (e : dexpr T) d :
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
