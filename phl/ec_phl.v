(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum counting_distr.
From xhl.pwhile         Require Import notations inhabited pwhile psemantic passn range.
                        Require Import phl.
From xhl                Require Import misc.
(* [Require] without [Import]: prhl.v defines its own [psi], [derivable]  *)
(* and [soundness], and hl/hl.v its own [derivable], [derivable2],        *)
(* [soundness], [assn2], [clause], [phi], [get_pre], [get_post], all of   *)
(* which would shadow phl.v's.  Accessed qualified, as erhl/erhl.v does.  *)
From xhl.prhl           Require prhl.
From xhl.hl             Require hl.

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
Implicit Types r      : bd.

(* ==================================================================== *)
(*                                                                      *)
(*   The rules of EasyCrypt's probabilistic Hoare logic (pHL/phoare)    *)
(*                                                                      *)
(*   This file states, as Coq lemmas over [phl_] of phl.v, every rule   *)
(*   of the catalogue in RULES-PHL.md.  Each lemma carries the number   *)
(*   of the section of that document which it formalizes.                *)
(*                                                                      *)
(* -------------------------------------------------------------------- *)
(*   SOURCE OF TRUTH -- the EasyCrypt implementation, not the document.  *)
(*                                                                      *)
(*   Every rule below has been reconciled against EasyCrypt's OCaml      *)
(*   sources ([src/phl/*.ml]).  Each section header cites the tactic     *)
(*   that implements the rule as [ecPhlXxx.ml:NNN], and individual       *)
(*   lemmas add finer line references where the section covers several   *)
(*   shapes.  Where the RULES-PHL.md prose and the code disagree, the    *)
(*   CODE wins and the disagreement is recorded on the spot.  Two such   *)
(*   places are known:                                                   *)
(*     - RULES-PHL.md S1.6's [mk_event_cond] table is transposed for     *)
(*       the two one-sided rows (see the orientation note in S1.6);      *)
(*     - [ecPhlConseq.ml:241-242]'s block comment states the transpose   *)
(*       of what [bdHoare_conseq_conds] ([:218-231]) actually builds     *)
(*       (see the note above [ec_postimpl]).                             *)
(*                                                                      *)
(*   A rule that is FALSE as EasyCrypt implements it is stated anyway,   *)
(*   flagged [!!! WRONG], left [Admitted], and accompanied by a          *)
(*   counterexample that has been machine-checked.  Such a flag is a     *)
(*   report about EasyCrypt, not about this transcription:               *)
(*   [grep '!!! WRONG'] lists them.  The dominant cause is a bound left  *)
(*   unconstrained when a rule's premises all go vacuous -- EasyCrypt's  *)
(*   [bhs_bd] is an unrestricted [real] ([ecAst.ml:270-280]; the smart   *)
(*   constructors at [ecCoreFol.ml:317-325] check only memory tags, and  *)
(*   typing checks only [~expct:treal], [ecTyping.ml:3643-3657]) -- but  *)
(*   [ec_while_variant] fails for a different and more basic reason.     *)
(*                                                                      *)
(* -------------------------------------------------------------------- *)
(*   NAMING CONVENTION -- two kinds of lemma live in this file.          *)
(*                                                                      *)
(*     ec_*    an EasyCrypt RULE.  Exactly one per entry of the          *)
(*             catalogue, and the comment above it gives the section     *)
(*             of RULES-PHL.md it formalizes.  These are the content    *)
(*             of the file.  The definitions [bd_opp], [ec_postimpl]     *)
(*             and [ec_bd_goal] likewise transcribe EasyCrypt tables     *)
(*             ([hoarecmp_opp], the S2.1 orientation table and the       *)
(*             S2.2 [bd_goal_r] table).                                  *)
(*                                                                      *)
(*     aux_*   a HELPER.  Not an EasyCrypt rule; scaffolding the proofs  *)
(*             need, assembled from lemmas that already exist elsewhere  *)
(*             in the development.  All helpers are gathered in the two  *)
(*             blocks below marked "AUXILIARY", one before [Section      *)
(*             Rules] for the distribution-level facts and one inside    *)
(*             it for the pHL-level ones -- with the single exception    *)
(*             of [aux_phl_while_ll], which is stated in S1.8 next to    *)
(*             the loop rules it serves.  Nothing outside this file is   *)
(*             modified to provide them.                                 *)
(*                                                                      *)
(*   So: [grep '^Lemma ec_'] lists the EasyCrypt rules, and              *)
(*       [grep '^Lemma aux_'] lists the helpers.                         *)
(*                                                                      *)
(* -------------------------------------------------------------------- *)
(*   GLOBAL CORRESPONDENCES between EasyCrypt and this formalization.    *)
(*   Referred to below as (G1)..(G5).                                    *)
(*                                                                      *)
(*   (G1) The bound.  EasyCrypt's [bd] is an [ss_inv], i.e. a formula    *)
(*        over the judgement's memory.  Here [d : R] is a *constant*.    *)
(*        Consequently every EasyCrypt premise of the shape             *)
(*        [forall &m, P => ...b...] collapses to a plain side condition  *)
(*        on reals, and the side conditions that exist only to keep the  *)
(*        bound stable become vacuous: [condnm] (S1.2),                 *)
(*        [is_bd_indep]/[pre_bound] (S1.6) and [check_form_indep]        *)
(*        (S5.2).                                                       *)
(*                                                                      *)
(*   (G2) Statements vs procedures.  EasyCrypt has two judgement forms,  *)
(*        [bdHoareS] (a statement) and [bdHoareF] (a procedure).  Here   *)
(*        [call f] is a command, so the procedure form is the statement  *)
(*        form at [c := call f].  No rule is duplicated.                *)
(*                                                                      *)
(*   (G3) Calls with arguments and results.  EasyCrypt's                 *)
(*        [lv <@ f(args)] is [Block bs Do (call f) Return rs] here:      *)
(*        [minit m bs] opens a fresh local frame and binds the formals   *)
(*        to the actuals evaluated in the caller, [mret m m' rs]         *)
(*        restores the caller's local store and assigns the results      *)
(*        from expressions evaluated in the callee's final memory.       *)
(*        Because the rules below quantify over the callee's *whole*     *)
(*        final memory, EasyCrypt's [forall mod(f)] is not needed.       *)
(*                                                                      *)
(*   (G4) Hoare premises.  Several pHL rules have [hoare[c : P ==> Q]]   *)
(*        premises.  By S3.1 that judgement is exactly                   *)
(*        [phl_ ps P c (~ Q) '= 0], which is the [hoare] notation below; *)
(*        by [pr_range] (pwhile/range.v) it is also exactly              *)
(*        [hl_ ps P c Q] of hl/hl_stmt.v.                               *)
(*                                                                      *)
(*   (G5) Modified variables.  EasyCrypt's [forall mod(c)] is            *)
(*        [hl.eqon (predC (hl.mod c))].  Three limits, see S2.3:         *)
(*        [hl.mod_spec] requires [nocall c]; [hl.mod (call n) = pred0];  *)
(*        and [hl.mod]/[hl.eqon] see the *local* store only, so global   *)
(*        assignments are outside their reach.                          *)
(*                                                                      *)
(* ==================================================================== *)

Section ec_phl.

(* -------------------------------------------------------------------- *)
(* S0.2  The opposite comparison, EasyCrypt's [hoarecmp_opp].            *)
(*   <=^op = >=,  >=^op = <=,  =^op = =.                                 *)
(* [hoarecmp_opp], ecCoreFol.ml.  Used by the bound-splitting rules of   *)
(* S3.4 and S3.5 ([t_bdhoare_split_bop], ecPhlBdHoare.ml:55, and         *)
(* [t_bdhoare_split_not], :149).                                         *)

Definition bd_opp (r : bd) : bd :=
  match r with
  | Le => Ge
  | Ge => Le
  | Eq => Eq
  end.

(* -------------------------------------------------------------------- *)
(* Sanity property of [bd_opp]: it swaps the two sides of the relation.  *)
(* Proof: [by case: r].                                                  *)

Lemma aux_bd_oppE (r : bd) (x y : R) : bd_opp r x y = r y x.
Proof. by case: r => //=; rewrite eq_sym. Qed.

(* ==================================================================== *)
(* ===   AUXILIARY (1/2) -- distribution-level helpers, NOT rules   === *)
(* ==================================================================== *)
(* None of the [aux_*] lemmas below is an EasyCrypt rule.  They are     *)
(* scaffolding for the proofs, assembled from lemmas that already exist *)
(* in mathcomp-analysis and in pwhile/; no new construction is          *)
(* introduced and nothing outside this file is modified.                *)

(* -------------------------------------------------------------------- *)
(* [predC] is involutive under [pr].  mathcomp has no [predCK] and no    *)
(* [predC (predC A) =i A] -- checked.  Needed wherever a rule flips      *)
(* [(~ Q)%A] twice: S3.1, S3.5, S2.4.                                    *)

Lemma aux_predCK_pr {T : choiceType} (mu : Distr T) (E : pred T) :
  \P_[mu] (~ ~ E)%A = \P_[mu] E.
Proof. by apply/eq_pr => x; rewrite !inE negbK. Qed.

(* -------------------------------------------------------------------- *)
(* Inclusion-exclusion, restated in the [%A] connectives.  mathcomp's    *)
(* [pr_and] / [pr_or] / [prID] are written with [[predI A & B]] and      *)
(* [[predU A & B]], while [(A /\ B)%A] is [predI A B]: convertible, but  *)
(* not syntactically equal, so the S3.4 and S3.6 rules need the aligned  *)
(* forms.                                                                *)

Lemma aux_pr_andE {T : choiceType} (mu : Distr T) (A B : pred T) :
  \P_[mu] (A /\ B)%A = \P_[mu] A + \P_[mu] B - \P_[mu] (A \/ B)%A.
Proof.
have -> : \P_[mu] (A \/ B)%A = \P_[mu] [predU A & B].
+ by apply/eq_pr => x; rewrite !inE.
have -> : \P_[mu] (A /\ B)%A = \P_[mu] [predI A & B].
+ by apply/eq_pr => x; rewrite !inE.
exact: pr_and.
Qed.

Lemma aux_pr_orE {T : choiceType} (mu : Distr T) (A B : pred T) :
  \P_[mu] (A \/ B)%A = \P_[mu] A + \P_[mu] B - \P_[mu] (A /\ B)%A.
Proof.
have -> : \P_[mu] (A \/ B)%A = \P_[mu] [predU A & B].
+ by apply/eq_pr => x; rewrite !inE.
have -> : \P_[mu] (A /\ B)%A = \P_[mu] [predI A & B].
+ by apply/eq_pr => x; rewrite !inE.
exact: pr_or.
Qed.

(* The case split of S3.6, likewise realigned ([prID]).                  *)

Lemma aux_pr_splitE {T : choiceType} (mu : Distr T) (A B : pred T) :
  \P_[mu] A = \P_[mu] (B /\ A)%A + \P_[mu] (~ B /\ A)%A.
Proof.
rewrite (prID _ B); congr (_ + _); apply/eq_pr => x; rewrite !inE.
+ by rewrite andbC.
+ by rewrite andbC.
Qed.

(* -------------------------------------------------------------------- *)
(* Transport of a probability along a deterministic post-processing.     *)
(* This is [pr_dmargin] modulo the definitional unfolding of [dmargin];  *)
(* proved directly, in the same three steps [pr_dmargin] itself uses.    *)
(* It is what turns [ssem_blockE] into the block rule (S1.9).            *)

Lemma aux_pr_dlet_dunit {T U : choiceType} (mu : Distr T) (g : T -> U) (E : pred U) :
  \P_[\dlet_(x <- mu) dunit (g x)] E = \P_[mu] [pred x | E (g x)].
Proof. by rewrite pr_dlet pr_exp; apply/eq_exp => x _; rewrite pr_dunit. Qed.

(* -------------------------------------------------------------------- *)
(* The probability of a CONSTANT predicate, bounded above by its         *)
(* indicator and (for a lossless distribution) below by it.  This is     *)
(* what the two post-independent [rnd] shapes of S1.6 reduce to once the *)
(* postcondition is known not to mention the sampled variable.           *)

Lemma aux_pr_const {T : choiceType} (nu : Distr T) (b : bool) :
  \P_[nu] [pred _ : T | b] <= (b%:R : R).
Proof.
case: b; first by rewrite mulr1n le1_pr.
rewrite mulr0n -(pr_pred0 nu); apply: le_in_pr => v _.
by rewrite !inE.
Qed.

Lemma aux_pr_const_ge {T : choiceType} (nu : Distr T) (b : bool) :
  \P_[nu] predT = 1 -> (b%:R : R) <= \P_[nu] [pred _ : T | b].
Proof.
move=> hT; case: b; last by rewrite mulr0n ge0_pr.
by rewrite mulr1n -hT; apply: le_in_pr => v _; rewrite !inE.
Qed.

(* -------------------------------------------------------------------- *)
(* Same idea as [aux_espc_ge] below, but for a plain expectation:        *)
(* a lower bound valid only on the support still bounds [\E_[mu]], scaled *)
(* by the weight.  Used by the S1.6 [rnd] rules, where the prefix is     *)
(* lossless so the weight is [1].                                        *)

Lemma aux_exp_ge {T : choiceType} (mu : Distr T) (nu : T -> Distr T)
                 (Qp : pred T) (k : R) :
     (forall x, x \in dinsupp mu -> k <= \P_[nu x] Qp)
  -> \P_[mu] predT * k <= \E_[mu] (fun x => \P_[nu x] Qp).
Proof.
move=> hk; rewrite -exp_cst.
pose F' x := if x \in dinsupp mu then \P_[nu x] Qp else k.
have -> : \E_[mu] (fun x => \P_[nu x] Qp) = \E_[mu] F'.
+ by apply/eq_exp => x hx; rewrite /F' hx.
apply: le_exp.
+ by apply: bounded_has_exp; exists `|k| => x /=; exact: lexx.
+ apply: bounded_has_exp; exists (1 + `|k|) => x; rewrite /F'; case: ifP => _.
  - rewrite ger0_norm ?ge0_pr //; apply: (le_trans (le1_pr _ _)).
    by rewrite lerDl normr_ge0.
  - by rewrite lerDr ler01.
+ by move=> x; rewrite /F'; case: ifP => hx; [exact: hk | exact: lexx].
Qed.

(* -------------------------------------------------------------------- *)
(* Bounds on a conditional expectation whose hypothesis holds only on    *)
(* the support.  [le_exp] demands a pointwise inequality EVERYWHERE, so  *)
(* the integrand is first replaced -- via [eq_exp], which only needs     *)
(* agreement on the support -- by one that is constantly [k] off it.     *)
(* Stated in the product form so that the degenerate case                *)
(* [\P_[mu] A = 0] needs no extra hypothesis.  [F] is any [0,1]-valued   *)
(* observable (in practice a probability, possibly one whose event       *)
(* depends on the point: that is why [F] is left abstract rather than    *)
(* fixed to [fun x => \P_[nu x] Qp]).  Used by S1.6's [ec_rnd_split].    *)

Lemma aux_espc_le {T : choiceType} (mu : Distr T) (F : T -> R) (A : pred T) (k : R) :
     (forall x, 0 <= F x <= 1)
  -> (forall x, x \in dinsupp (drestr A mu) -> F x <= k)
  -> \P_[mu] A * \E_[mu, A] F <= \P_[mu] A * k.
Proof.
move=> hF hk.
have hb : forall eta : Distr T, \E?_[eta] F.
+ move=> eta; apply: bounded_has_exp; exists 1 => y.
  by move: (hF y) => /andP[h0 h1]; rewrite ger0_norm.
case: (\P_[mu] A =P 0) => [->|/eqP nz]; first by rewrite !mul0r.
rewrite espcE; first by apply: hb.
have -> : \P_[mu] A * (\E_[drestr A mu] F / \P_[mu] A) = \E_[drestr A mu] F.
+ by rewrite mulrC (mulfVK nz).
rewrite -mass_drestr -exp_cst.
pose F' y := if y \in dinsupp (drestr A mu) then F y else k.
have -> : \E_[drestr A mu] F = \E_[drestr A mu] F'.
+ by apply/eq_exp => y hy; rewrite /F' hy.
apply: le_exp.
+ apply: bounded_has_exp; exists (1 + `|k|) => y; rewrite /F'; case: ifP => _.
  - move: (hF y) => /andP[h0 h1]; rewrite ger0_norm //.
    by apply: (le_trans h1); rewrite lerDl normr_ge0.
  - by rewrite lerDr ler01.
+ by apply: bounded_has_exp; exists `|k| => y /=; exact: lexx.
+ by move=> y; rewrite /F'; case: ifP => hy; [exact: hk | exact: lexx].
Qed.

Lemma aux_espc_ge {T : choiceType} (mu : Distr T) (F : T -> R) (A : pred T) (k : R) :
     (forall x, 0 <= F x <= 1)
  -> (forall x, x \in dinsupp (drestr A mu) -> k <= F x)
  -> \P_[mu] A * k <= \P_[mu] A * \E_[mu, A] F.
Proof.
move=> hF hk.
have hb : forall eta : Distr T, \E?_[eta] F.
+ move=> eta; apply: bounded_has_exp; exists 1 => y.
  by move: (hF y) => /andP[h0 h1]; rewrite ger0_norm.
case: (\P_[mu] A =P 0) => [->|/eqP nz]; first by rewrite !mul0r.
rewrite espcE; first by apply: hb.
have -> : \P_[mu] A * (\E_[drestr A mu] F / \P_[mu] A) = \E_[drestr A mu] F.
+ by rewrite mulrC (mulfVK nz).
rewrite -mass_drestr -exp_cst.
pose F' y := if y \in dinsupp (drestr A mu) then F y else k.
have -> : \E_[drestr A mu] F = \E_[drestr A mu] F'.
+ by apply/eq_exp => y hy; rewrite /F' hy.
apply: le_exp.
+ by apply: bounded_has_exp; exists `|k| => y /=; exact: lexx.
+ apply: bounded_has_exp; exists (1 + `|k|) => y; rewrite /F'; case: ifP => _.
  - move: (hF y) => /andP[h0 h1]; rewrite ger0_norm //.
    by apply: (le_trans h1); rewrite lerDl normr_ge0.
  - by rewrite lerDr ler01.
+ by move=> y; rewrite /F'; case: ifP => hy; [exact: hk | exact: lexx].
Qed.

Lemma aux_espc_eq {T : choiceType} (mu : Distr T) (F : T -> R) (A : pred T) (k : R) :
     (forall x, 0 <= F x <= 1)
  -> (forall x, x \in dinsupp (drestr A mu) -> F x = k)
  -> \P_[mu] A * \E_[mu, A] F = \P_[mu] A * k.
Proof.
move=> hF hk; apply/le_anti/andP; split.
+ by apply: aux_espc_le => // y hy; rewrite (hk y hy).
+ by apply: aux_espc_ge => // y hy; rewrite (hk y hy).
Qed.

(* -------------------------------------------------------------------- *)
(* Integer step-down, for the variant rule of S1.8(a): a strict decrease *)
(* below [n+1] lands at or below [n].  This is what bounds the number of *)
(* loop unrollings by the variant.                                       *)

Lemma aux_ltzS (x : int) (n : nat) : (x < (n.+1)%:Z)%R -> (x <= n%:Z)%R.
Proof. by rewrite -addn1 PoszD ltzD1. Qed.

(* -------------------------------------------------------------------- *)
(* Lower bound at a [dlim].  Dual of phl.v's [sum_dlim_r_r], but much    *)
(* cheaper: a single index suffices, because [dlim_ub] says every        *)
(* approximant is below the limit.                                       *)

Lemma aux_pr_dlim_ge {T : choiceType} (f : nat -> Distr T) (E : pred T) (r : R) k :
     (forall n m : nat, (n <= m)%N -> forall x : T, f n x <= f m x)
  -> r <= \P_[f k] E
  -> r <= \P_[\dlim_(n) f n] E.
Proof.
move=> hmono h; apply/(le_trans h)/le_mu_pr => x _ _.
exact: (dlim_ub k hmono x).
Qed.

Section Rules.
Context ps.

Notation phl := (phl_ ps).

(* [hoare P c Q] is EasyCrypt's [hoare[ c : P ==> Q ]] -- see (G4).      *)
Notation hoare P c Q := (phl_ ps P%A c%S (~ Q)%A '= 0).

(* ==================================================================== *)
(* ===      AUXILIARY (2/2) -- pHL-level helpers, NOT rules          === *)
(* ==================================================================== *)
(* As above: [aux_*] is scaffolding, not a rule of the catalogue.  These *)
(* three need the procedure environment [ps], so they live inside        *)
(* [Section Rules]; they are the pHL rules phl.v happens to lack         *)
(* (global assignment, a semantic congruence) plus the correctness of    *)
(* pwhile's [inliner].                                                   *)

(* -------------------------------------------------------------------- *)
(* The global-assignment rule, which phl.v lacks ([phl_assgn] covers the *)
(* local store only).  Same proof, with [ssem_gassnE] for [ssem_assnE].  *)

Lemma aux_phl_gassgn {T : IhbType.type} Q (x : vars T) (e : expr T) :
  phl [pred m | Q (m.{x <- `[{e}] m})] (G x <<- e) Q '= 1.
Proof. by move=> m /= Qm; rewrite !ssemE pr_dunit Qm. Qed.

(* -------------------------------------------------------------------- *)
(* The semantic congruence, analogue of [hl_eq] (hl/hl.v:103).  It is    *)
(* the S5 schema, but S1.3 and S1.5 already need it, so it is proved     *)
(* here and re-exported below as [ec_eq].                                *)

Lemma aux_phl_eq P Q c c' r d :
     (forall m, P m -> ssem_ ps c m = ssem_ ps c' m)
  -> phl P c Q r d
  -> phl P c' Q r d.
Proof. by move=> heq h m Pm; rewrite -(heq m Pm); apply: h. Qed.

(* -------------------------------------------------------------------- *)
(* Correctness of pwhile's syntactic inliner ([inliner], psemantic.v),   *)
(* which replaces every [call f] by [ps f].  Needed by [ec_inline]       *)
(* (S5.3).  The induction is the one written four times over in          *)
(* psemantic.v ([inline2_split], [inliner_inliner_ps_ssem], ...); the    *)
(* [call] case is [ssem_call_eq].                                        *)

Lemma aux_ssem_inliner c m : ssem_ ps (inliner c ps) m = ssem_ ps c m.
Proof.
move: m; elim: c => //=.
+ move=> bs c0 ih rs m; rewrite !ssemE.
  by apply: eq_in_dlet; last exact: ih.
+ move=> e c1 ih1 c2 ih2 m; rewrite !ssemE.
  by case: (`[{e}] m); [exact: ih1 | exact: ih2].
+ move=> e c0 ih m; rewrite !ssem_whileE; apply: eq_dlim => k.
  elim: k m => [|k ihk] m /=; first by rewrite !ssemE.
  rewrite !ssemE; case: (`[{e}] m) => //=.
  by apply: eq_in_dlet; [move=> m' _; exact: ihk | exact: ih].
+ move=> c1 ih1 c2 ih2 m; rewrite !ssemE.
  by apply: eq_in_dlet; [move=> m' _; exact: ih2 | exact: ih1].
+ by move=> f m; rewrite ssem_call_eq.
Qed.

(* ==================================================================== *)
(* ===                     1. The core pHL rules                    === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* S1.1  skip.                                                           *)
(* [t_bdhoare_skip_r_low], ecPhlSkip.ml:42 (premises :52-56, [<=]        *)
(* rejected); surface [t_bdhoare_skip_r], :61, [t_skip], :90.            *)
(*                                                                      *)
(*     forall &m, P => (1 <> b)      forall &m, P => Q                   *)
(*   ---------------------------------------------------                *)
(*            |- phoare[ [] : P ==> Q ] <> b                             *)
(*                                                                      *)
(* By (G1) the first premise of the catalogue is the plain [r 1 d].      *)
(* Proof: [phl_skip] gives [phl P skip P '= 1]; conclude with            *)
(* [phl_conseq_*] on [Q] and the bound.                                  *)

Lemma ec_skip P Q r d :
     (forall m, P m -> Q m)
  -> (forall m, P m -> r 1 d)
  -> phl P skip Q r d.
Proof.
move=> hQ hr m Pm; rewrite ssemE pr_dunit.
have -> : (Q m)%:R = 1 :> R by rewrite (hQ m Pm) /= mulr1n.
exact: (hr m Pm).
Qed.

(* -------------------------------------------------------------------- *)
(* S1.2  seq (app) -- the four-bound rule.                               *)
(* [t_bdhoare_seq_r_low], ecPhlSeq.ml:44 (conditions :59-71, premise     *)
(* pruning :84-97); surface [t_bdhoare_seq_r], :103;                     *)
(* [process_phl_bd_info], :167-215; dispatcher arm :258-263.             *)
(*                                                                      *)
(* [S] is the catalogue's case predicate [R] (renamed: [R] is the        *)
(* realType here).  [Phi] is the catalogue's auxiliary assertion [phi].  *)
(* The catalogue's [condnm] premise is vacuous by (G1).                  *)
(*                                                                      *)
(* Proof of [ec_seq_eq]: [phl_seq_eq] of phl.v, after weakening the two  *)
(* second-phase judgements with [phl_conseq_eq] using [Phi].             *)

Lemma ec_seq_eq (Phi S P Q : assn) c1 c2 f1 f2 g1 g2 d :
     (forall m, P m -> f1 * f2 + g1 * g2 = d)
  -> hoare P c1 Phi
  -> phl P c1 S           '= f1
  -> phl (Phi /\ S)%A c2 Q      '= f2
  -> phl P c1 (~ S)%A     '= g1
  -> phl (Phi /\ ~ S)%A c2 Q    '= g2
  -> phl P (c1 ;; c2) Q '= d.
(* NOTE this does NOT reduce to phl.v's [phl_seq_eq]: that rule needs    *)
(* [phl S c2 Q '= f2] and [phl (~ S) c2 Q '= g2], while the catalogue    *)
(* gives only the [Phi]-relativised forms.  Instantiating [phl_seq_eq]   *)
(* at [R := Phi /\ S] fixes three premises but not the fourth, since     *)
(* [~ (Phi /\ S)] covers memories where [Phi] fails.  So the [exp_split] *)
(* argument of [phl_seq_eq] is replayed here, with the [hoare] premise   *)
(* supplying [range Phi] to bridge [S] and [Phi /\ S] on the support.    *)
Proof.
move=> hbd hPhi PR RQ PNR NRQ m Pm /=; rewrite -(hbd m Pm) ssemE pr_dlet.
have hr : range Phi (ssem_ ps c1 m) by apply/pr_range/eqP; exact: (hPhi m Pm).
apply/eqP; rewrite (exp_split S); first by apply: has_esp_pr.
have [/= /eqP-> /eqP->] := (PR _ Pm, PNR _ Pm); congr (_ + _).
- case: (f1 =P 0) => [->|/eqP nz_f1]; first by rewrite !mul0r.
  congr (_ * _); rewrite espcE; first by apply: has_esp_pr.
  rewrite -(@eq_exp _ _ _ (fun=> f2)).
  - move=> m'; rewrite dinsupp_restr => /andP [hm' Sm'].
    have hc : (Phi /\ S)%A m'.
    + by apply/andP; split; [exact: (hr m' hm') | exact: Sm'].
    by apply/esym/eqP; apply: (RQ m' hc).
  by rewrite exp_cst mass_drestr mulrAC divff ?mul1r // (eqP (PR m Pm)).
- case: (g1 =P 0) => [->|/eqP nz_g1]; first by rewrite !mul0r.
  congr (_ * _); rewrite espcE; first by apply: has_esp_pr.
  rewrite -(@eq_exp _ _ _ (fun=> g2)).
  - move=> m'; rewrite dinsupp_restr => /andP [hm' Sm'].
    have hc : (Phi /\ ~ S)%A m'.
    + by apply/andP; split; [exact: (hr m' hm') | exact: Sm'].
    by apply/esym/eqP; apply: (NRQ m' hc).
  by rewrite exp_cst mass_drestr mulrAC divff ?mul1r // (eqP (PNR m Pm)).
Qed.

(* !!! WRONG -- this statement is FALSE as written.  It is missing the   *)
(* non-negativity of the two second-phase bounds, [0 <= f2] and          *)
(* [0 <= g2].  Without them a *negative* second-phase bound makes        *)
(* [f1 * f2] negative while the corresponding probability mass is 0, so  *)
(* the conclusion demands a negative upper bound on a probability.       *)
(* (My drafting note claimed positivity was unnecessary here because     *)
(* [ler_pM]'s side conditions come from [ge0_pr]; that is right only for *)
(* the LEFT factors.  The right factors need their own hypothesis.)      *)
(*                                                                      *)
(* COUNTEREXAMPLE, machine-checked -- instantiate at                     *)
(*     P := predT,  Phi := pred0,  S := predT,  Q := predT,              *)
(*     c1 := abort, c2 := skip,                                          *)
(*     f1 := 1, f2 := -1, g1 := 0, g2 := 0, d := -1.                     *)
(* All six premises hold:                                                *)
(*   1 * (-1) + 0 * 0 = -1 <= -1;                                        *)
(*   hoare predT abort pred0            -- [ssem abort m = dnull];       *)
(*   phl predT abort predT       '<= 1  -- 0 <= 1;                       *)
(*   phl (pred0 /\ predT) skip predT '<= (-1)  -- precondition [pred0],  *)
(*                                               vacuously true;         *)
(*   phl predT abort (~ predT)   '<= 0  -- 0 <= 0;                       *)
(*   phl (pred0 /\ ~ predT) skip predT '<= 0   -- vacuous.               *)
(* But [ssem (abort ;; skip) m = dnull], so the conclusion asserts       *)
(*   \P_[dnull] predT = 0 <= -1,   which is false.                       *)
(*                                                                      *)
(* Adding [0 <= f2] and [0 <= g2] makes it provable by the same argument *)
(* as [ec_seq_ge] below.  Left unproved and unchanged, per the agreed    *)
(* rule that statements are the specification.                           *)
(*                                                                      *)
(* EASYCRYPT WITNESS: phl/easycrypt/ec_seq_le.ec proves [false] in       *)
(* EasyCrypt from this instance ([phi := false] disarms the second-phase *)
(* premises, [s1 := while (true) { }] keeps [cond_phi] satisfiable).     *)

Lemma ec_seq_le (Phi S P Q : assn) c1 c2 f1 f2 g1 g2 d :
     (forall m, P m -> f1 * f2 + g1 * g2 <= d)
  -> hoare P c1 Phi
  -> phl P c1 S           '<= f1
  -> phl (Phi /\ S)%A c2 Q      '<= f2
  -> phl P c1 (~ S)%A     '<= g1
  -> phl (Phi /\ ~ S)%A c2 Q    '<= g2
  -> phl P (c1 ;; c2) Q '<= d.
Proof. Admitted.

(* !!! WRONG -- FALSE as written, and this one is the most serious of     *)
(* the family, because the JUDGEMENT'S OWN BOUND is perfectly ordinary.   *)
(* A product of lower bounds bounds the product from below only when the  *)
(* bounds are non-negative; [ecPhlSeq.ml:44-100] emits no analogue of     *)
(* [rnd]'s [sgoal5], so nothing forces [0 <= f1,f2,g1,g2].  I previously  *)
(* carried those four hypotheses; they are NOT in EasyCrypt and have been *)
(* removed to match the implementation.                                   *)
(*                                                                      *)
(* COUNTEREXAMPLE -- [P := Phi := S := Q := predT], [c1 := abort],        *)
(* [f1 := -1], [f2 := -1], [g1 := 0], [g2 := 0], [d := 1].                *)
(* Then [d <= f1*f2 + g1*g2] is [1 <= 1]; [hoare predT abort predT] holds;*)
(* [phl predT abort predT '>= -1] and [phl _ c2 _ '>= -1] hold because    *)
(* every probability is [>= 0 > -1]; the two [g] premises are [0 <= _].   *)
(* But [ssem (abort ;; c2) m = dnull], so the conclusion asserts          *)
(* [1 <= 0].                                                             *)
(*                                                                      *)
(* Note that a NEGATIVE INTERMEDIATE BOUND is all that is needed here --  *)
(* [phoare[c : P ==> S] >= -1%r] is an ordinary, provable EasyCrypt       *)
(* judgement -- and the conclusion's bound [1%r] is entirely normal.      *)
(*                                                                      *)
(* EASYCRYPT WITNESS: phl/easycrypt/ec_seq_ge.ec proves [false].         *)

Lemma ec_seq_ge (Phi S P Q : assn) c1 c2 f1 f2 g1 g2 d :
     (forall m, P m -> d <= f1 * f2 + g1 * g2)
  -> hoare P c1 Phi
  -> phl P c1 S           '>= f1
  -> phl (Phi /\ S)%A c2 Q      '>= f2
  -> phl P c1 (~ S)%A     '>= g1
  -> phl (Phi /\ ~ S)%A c2 Q    '>= g2
  -> phl P (c1 ;; c2) Q '>= d.
Proof.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.3  if.                                                             *)
(* [t_bdhoare_cond], ecPhlCond.ml:61 (expansion [LowInternal.t_gen_cond], *)
(* :25-44); elaboration [process_cond], ecPhlHiCond.ml:10.               *)
(*                                                                      *)
(*   |- phoare[ s1; tl : P /\ e ==> Q ] <> b                             *)
(*   |- phoare[ s2; tl : P /\ ~e ==> Q ] <> b                            *)
(*   ------------------------------------------------------             *)
(*   |- phoare[ if e then s1 else s2; tl : P ==> Q ] <> b                *)
(*                                                                      *)
(* Both branches keep the *same* bound: the rule is a precondition       *)
(* case-split, sound at a fixed bound because the two preconditions are  *)
(* exclusive and exhaustive.                                             *)
(*                                                                      *)
(* Without a tail this is already phl.v's                                *)
(*   Lemma phl_if P (e : bexpr) c1 c2 Q r d :                            *)
(*        phl (P /\   `[{e}]) c1 Q r d                                   *)
(*     -> phl (P /\ ~ `[{e}]) c2 Q r d                                   *)
(*     -> phl P (If e then c1 else c2) Q r d.                            *)
(* The catalogue's rule carries the tail [tl], so the version with a     *)
(* tail is stated here.  Proof: [if_seq] (psemantic.v:683) turns         *)
(* [(If e then c1 else c2) ;; tl] into                                   *)
(* [If e then (c1 ;; tl) else (c2 ;; tl)], then [phl_if].                *)

Lemma ec_cond P Q (e : bexpr) c1 c2 tl r d :
     phl (P /\   `[{e}])%A (c1 ;; tl) Q r d
  -> phl (P /\ ~ `[{e}])%A (c2 ;; tl) Q r d
  -> phl P ((If e then c1 else c2) ;; tl) Q r d.
Proof.
move=> h1 h2; apply: (aux_phl_eq (c := If e then (c1 ;; tl) else (c2 ;; tl))).
+ by move=> m _; rewrite if_seq.
+ by apply: phl_if.
Qed.

(* -------------------------------------------------------------------- *)
(* S1.4  match -- NOT FORMALIZED.                                        *)
(* [t_bdhoare_match], ecPhlCond.ml:243 (expansion :125-233).             *)
(* [cmd_] (pwhile/pwhile.v:276) has no [match] constructor and the       *)
(* language has no datatypes, so there is no goal of this shape.         *)

(* -------------------------------------------------------------------- *)
(* S1.5  rcondt / rcondf.                                                *)
(* [Low.t_bdhoare_rcond_r], ecPhlRCond.ml:63 (Hoare premise :70);        *)
(* [match] variant [Low.t_bdhoare_rcond_match_r], :250.                  *)
(*                                                                      *)
(*   |- hoare[ hd : P ==> e_b ]    |- phoare[ hd; s_b; tl : P ==> Q ] <> b *)
(*   ------------------------------------------------------------------- *)
(*     |- phoare[ hd; if e then s1 else s2; tl : P ==> Q ] <> b           *)
(*                                                                      *)
(* The first premise is a Hoare goal, not a pHL one -- see (G4).         *)
(* Proof: [ec_eq] (S5) with [ssem_seqE] and [ssem_ifE]: on the support   *)
(* of [ssem_ ps hd m] the guard is determined, so [eq_in_dlet] rewrites  *)
(* the conditional away.                                                 *)

Lemma ec_rcondt P Q (e : bexpr) hd c1 c2 tl r d :
     hoare P hd `[{e}]
  -> phl P (hd ;; (c1 ;; tl)) Q r d
  -> phl P (hd ;; ((If e then c1 else c2) ;; tl)) Q r d.
Proof.
move=> hh h; apply: (aux_phl_eq (c := hd ;; (c1 ;; tl))); last exact: h.
move=> m Pm; rewrite !ssemE; apply: eq_in_dlet; last by [].
move=> m' hm'.
have hr : range `[{e}] (ssem_ ps hd m) by apply/pr_range/eqP; exact: (hh m Pm).
by rewrite !ssemE (hr m' hm').
Qed.

Lemma ec_rcondf P Q (e : bexpr) hd c1 c2 tl r d :
     hoare P hd (~ `[{e}])%A
  -> phl P (hd ;; (c2 ;; tl)) Q r d
  -> phl P (hd ;; ((If e then c1 else c2) ;; tl)) Q r d.
Proof.
move=> hh h; apply: (aux_phl_eq (c := hd ;; (c2 ;; tl))); last exact: h.
move=> m Pm; rewrite !ssemE; apply: eq_in_dlet; last by [].
move=> m' hm'.
have hr : range (~ `[{e}])%A (ssem_ ps hd m).
+ by apply/pr_range/eqP; exact: (hh m Pm).
by rewrite !ssemE (negbTE (hr m' hm')).
Qed.


(* -------------------------------------------------------------------- *)
(* S1.6  rnd, five shapes.                                               *)
(* [t_bdhoare_rnd_r], ecPhlRnd.ml:158.  [mk_event] :198-206,             *)
(* [mk_event_cond] :165-179, [bound]/[pre_bound] :207-214, the five      *)
(* shapes :215-291; [process_rnd] bdHoare arm :649, :664-685.            *)
(*                                                                      *)
(* Throughout, the statement ends with [x <$- e] and [s] is the prefix.   *)
(* [E : pred T] is the catalogue's *event*, a predicate on the sampled   *)
(* value; [mu d E] is [\P_[`[{e}] m] E].  By (G1) the catalogue's        *)
(* [pre_bound] is [true] and [bound] is [d], so the generalisation over  *)
(* a fresh [bd] variable disappears.                                     *)
(*                                                                      *)
(* -------------------------------------------------------------------- *)
(* [mk_event_cond] as a first-class definition, transcribed from         *)
(* [ecPhlRnd.ml:165-179].  It is the only premise that ties the event    *)
(* [E] to the postcondition, through [subst_form_lv]                     *)
(* ([ecLowPhlGoal.ml:597]), i.e. [Q[v/lv]] -- here [Q m.[x <- v]].       *)
(*                                                                      *)
(* !! ORIENTATION -- RESOLVED AGAINST THE IMPLEMENTATION.                *)
(* RULES-PHL.md S1.6 (and EasyCrypt's own in-tree copy of that document) *)
(* tabulates the two one-sided rows as                                   *)
(*      <=  :  forall v, E v -> v \in supp d -> Q[v/lv]                  *)
(*      >=  :  forall v, Q[v/lv] -> v \in supp d -> E v                  *)
(* which is the TRANSPOSE of what the code builds.  [ecPhlRnd.ml:174]    *)
(* defines [f_imps_simpl' fl = f_imps_simpl (List.tl fl) (List.hd fl)]   *)
(* and [f_imps_simpl = List.fold_right f_imp_simpl] ([ecFol.ml:709]), so *)
(* the HEAD of the list is the conclusion and the tail the hypotheses.   *)
(* With [FHle -> [event_v; v_in_supp; post_v]] ([:176]) that reads       *)
(*      <=  :  forall v, v \in supp d -> Q[v/lv] -> E v                  *)
(* and with [FHge -> [post_v; v_in_supp; event_v]] ([:177])              *)
(*      >=  :  forall v, v \in supp d -> E v -> Q[v/lv].                 *)
(* [FHeq] ([:178]) is [v \in supp d -> (E v <-> Q[v/lv])], on which code *)
(* and document agree.  The orientation below is the code's; it is also  *)
(* the only one that gives the rule (at [<=] one needs                   *)
(* [\P_[e] (Q[.]) <= \P_[e] E <= d], hence [Q[v] -> E v]).  So the       *)
(* document's table is wrong, in both copies.  The default event         *)
(* [E := fun v => Q[v/lv]] ([mk_event], [:198-206]) makes both readings  *)
(* coincide, which is why this is invisible unless [E] is supplied       *)
(* explicitly (shapes (c), (d), (d') and (e)).                           *)

Definition ec_evcond {T : IhbType.type} (r : bd) (x : vars T) (e : dexpr T)
                     (E : pred T) (Q : assn) (m : cmem) : Prop :=
  forall v : T, v \in dinsupp (`[{e}] m) ->
    match r with
    | Le => Q m.[x <- v] -> E v
    | Ge => E v -> Q m.[x <- v]
    | Eq => E v = Q m.[x <- v]
    end.

(* (a) [rnd], [<=], post independent of the assigned variable: the       *)
(* sampling is simply dropped.                                           *)
(* Proof: [ssem_seqE]/[ssem_rndE], then [pr_dlet]; the inner probability *)
(* is [Q m' * weight (`[{e}] m')] <= [Q m'] by [le1_pr].                 *)

Lemma ec_rnd_le_indep {T : IhbType.type} P Q (x : vars T) (e : dexpr T) s d :
     (forall (m : cmem) (v : T), Q m.[x <- v] = Q m)
  -> phl P s Q '<= d
  -> phl P (s ;; (x <$- e)) Q '<= d.
Proof.
move=> hQ h m Pm; rewrite ssemE.
have -> : \dlet_(m' <- ssem_ ps s m) ssem_ ps (x <$- e) m'
        = \dlet_(m' <- ssem_ ps s m) (\dlet_(v <- `[{e}] m') dunit m'.[x <- v]).
+ by apply: eq_in_dlet; last by []; move=> m' _; rewrite ssemE.
rewrite pr_dlet; apply: (le_trans _ (h m Pm)).
rewrite [X in _ <= X]pr_exp; apply: le_exp.
+ apply: bounded_has_exp; exists 1 => m'; rewrite aux_pr_dlet_dunit.
  by rewrite ger0_norm ?ge0_pr ?le1_pr.
+ apply: bounded_has_exp; exists 1 => m'; rewrite ger0_norm ?ler0n //.
  by case: (Q m') => /=; rewrite ?mulr1n ?lexx ?ler01.
+ move=> m'; rewrite aux_pr_dlet_dunit.
  have -> : \P_[`[{e}] m'] [pred v | Q m'.[x <- v]]
          = \P_[`[{e}] m'] [pred _ : T | Q m'].
  - by apply/eq_pr => v; rewrite !inE hQ.
  exact: aux_pr_const.
Qed.

(* (b) [rnd], [>=], post independent: a losslessness condition on the    *)
(* sampled distribution is folded into the postcondition.                *)
(*                                                                      *)
(* The catalogue states this shape for [<> in {=, >=}].  Only [>=] is    *)
(* stated here: the [=] instance appears to be unsound as written.       *)
(* Counterexample -- let [s] put mass 1/2 on [m1] and 1/2 on [m2], with  *)
(* [Q m1], [Q m2], [weight (e m1) = 1] and [weight (e m2) = 1/2].  Then  *)
(* the premise holds at [d = 1/2] (only [m1] satisfies [Q /\ ll]) while  *)
(* the conclusion evaluates to [1/2*1 + 1/2*1/2 = 3/4 <> 1/2].  Please   *)
(* check the [=] instance against EasyCrypt before adding it.            *)

Lemma ec_rnd_ge_indep {T : IhbType.type} P Q (x : vars T) (e : dexpr T) s d :
     (forall (m : cmem) (v : T), Q m.[x <- v] = Q m)
  -> phl P s [pred m | Q m && (\P_[`[{e}] m] predT == 1)] '>= d
  -> phl P (s ;; (x <$- e)) Q '>= d.
Proof.
move=> hQ h m Pm; rewrite ssemE.
have -> : \dlet_(m' <- ssem_ ps s m) ssem_ ps (x <$- e) m'
        = \dlet_(m' <- ssem_ ps s m) (\dlet_(v <- `[{e}] m') dunit m'.[x <- v]).
+ by apply: eq_in_dlet; last by []; move=> m' _; rewrite ssemE.
rewrite pr_dlet; apply: (le_trans (h m Pm)).
rewrite [X in X <= _]pr_exp; apply: le_exp.
+ apply: bounded_has_exp; exists 1 => m'; rewrite ger0_norm ?ler0n //.
  by rewrite /=; case: (_ && _) => /=; rewrite ?mulr1n ?mulr0n ?lexx ?ler01.
+ apply: bounded_has_exp; exists 1 => m'; rewrite aux_pr_dlet_dunit.
  by rewrite ger0_norm ?ge0_pr ?le1_pr.
+ move=> m'; rewrite aux_pr_dlet_dunit.
  have -> : \P_[`[{e}] m'] [pred v | Q m'.[x <- v]]
          = \P_[`[{e}] m'] [pred _ : T | Q m'].
  - by apply/eq_pr => v; rewrite !inE hQ.
  rewrite /=; case/boolP: (Q m') => hq /=; last by rewrite mulr0n ge0_pr.
  case/boolP: (\P_[`[{e}] m'] predT == 1) => /= hll; last by rewrite mulr0n ge0_pr.
  rewrite ?mulr1n -(eqP hll); apply: le_in_pr => v _.
  by rewrite !inE.
Qed.

(* (c) [rnd E], [<=] -- [PSingleRndParam], [ecPhlRnd.ml:248-256].  The   *)
(* residual is a *Hoare* goal ([f_hoareS], [:254]) -- see (G4).          *)
(*                                                                      *)
(* !!! WRONG -- FALSE as written; missing [0 <= d].  Third instance of   *)
(* the same defect as [ec_seq_le] and [ec_call_seq_le]: the only premise *)
(* is a *Hoare* judgement, which is vacuously true when the prefix       *)
(* diverges, so nothing forces the bound to be a possible probability.   *)
(* On the support one gets [F m' <= d], hence                            *)
(* [\E_[mu] F <= \P_[mu] predT * d], and [<= d] needs [0 <= d].          *)
(* COUNTEREXAMPLE, machine-checked -- [P := predT], [Q := predT],        *)
(* [E := predT], [s := abort], [d := -1].  The premise holds because     *)
(* [ssem abort m = dnull] makes [\P_[dnull] (~ wp) = 0]; but             *)
(* [ssem (abort ;; (x <$- e)) m = dnull], so the conclusion asserts      *)
(* [0 <= -1].                                                            *)
(* Note that [ec_rnd_le_indep] above is NOT affected: its premise is a   *)
(* pHL judgement [phl P s Q '<= d], which at [s := abort] already yields *)
(* [0 <= d].                                                             *)
(*                                                                      *)
(* EASYCRYPT WITNESS: phl/easycrypt/ec_rnd_le.ec proves [false].         *)

Lemma ec_rnd_le {T : IhbType.type} P Q (x : vars T) (e : dexpr T) (E : pred T) s d :
     hoare P s [pred m | (\P_[`[{e}] m] E <= d)
                         && `[< ec_evcond Le x e E Q m >]]
  -> phl P (s ;; (x <$- e)) Q '<= d.
Proof. Admitted.

(* (d) [rnd E], [>=] -- [PSingleRndParam], [ecPhlRnd.ml:257-264].  The   *)
(* residual judgement is forced to [FHeq 1%r] ([:262]).                  *)

Lemma ec_rnd_ge {T : IhbType.type} P Q (x : vars T) (e : dexpr T) (E : pred T) s d :
     phl P s [pred m | (d <= \P_[`[{e}] m] E)
                       && `[< ec_evcond Ge x e E Q m >]] '= 1
  -> phl P (s ;; (x <$- e)) Q '>= d.
(* Sound, unlike (c): the residual is forced to [= 1], so the prefix is  *)
(* lossless and [\P_[mu] predT = 1] absorbs the weight factor.           *)
Proof.
move=> h m Pm; rewrite ssemE.
have -> : \dlet_(m' <- ssem_ ps s m) ssem_ ps (x <$- e) m'
        = \dlet_(m' <- ssem_ ps s m) (\dlet_(v <- `[{e}] m') dunit m'.[x <- v]).
+ by apply: eq_in_dlet; last by []; move=> m' _; rewrite ssemE.
rewrite pr_dlet.
set W := [pred m | (d <= \P_[`[{e}] m] E)
                   && `[< ec_evcond Ge x e E Q m >]].
have hW : \P_[ssem_ ps s m] W = 1 by apply/eqP; exact: (h m Pm).
have hT : \P_[ssem_ ps s m] predT = 1.
+ by apply/le_anti; rewrite le1_pr /= -hW; apply: subset_pr.
have hr : range W (ssem_ ps s m).
+ by apply/pr_range/eqP; rewrite pr_predC hT hW subrr.
have key : \P_[ssem_ ps s m] predT * d
        <= \E_[ssem_ ps s m]
             (fun m' => \P_[\dlet_(v <- `[{e}] m') dunit m'.[x <- v]] Q).
+ apply: aux_exp_ge => m' hm'; move: (hr m' hm') => /andP [hd /asboolP hE].
  rewrite aux_pr_dlet_dunit; apply: (le_trans hd).
  by apply: le_in_pr => v hv; rewrite ?inE; exact: (hE v hv).
by apply: (le_trans _ key); rewrite hT mul1r lexx.
Qed.

(* (d') [rnd E], [=] -- the [FHeq] instance of the same branch           *)
(* ([ecPhlRnd.ml:257-264]).  This is the row on which the code and the   *)
(* document agree: on the support, [E] and [Q[./lv]] must agree.         *)

Lemma ec_rnd_eq {T : IhbType.type} P Q (x : vars T) (e : dexpr T) (E : pred T) s d :
     phl P s [pred m | (\P_[`[{e}] m] E == d)
                       && `[< ec_evcond Eq x e E Q m >]] '= 1
  -> phl P (s ;; (x <$- e)) Q '= d.
Proof.
move=> h m Pm; rewrite ssemE.
have -> : \dlet_(m' <- ssem_ ps s m) ssem_ ps (x <$- e) m'
        = \dlet_(m' <- ssem_ ps s m) (\dlet_(v <- `[{e}] m') dunit m'.[x <- v]).
+ by apply: eq_in_dlet; last by []; move=> m' _; rewrite ssemE.
rewrite pr_dlet.
set W := [pred m | (\P_[`[{e}] m] E == d)
                   && `[< ec_evcond Eq x e E Q m >]].
have hW : \P_[ssem_ ps s m] W = 1 by apply/eqP; exact: (h m Pm).
have hT : \P_[ssem_ ps s m] predT = 1.
+ by apply/le_anti; rewrite le1_pr /= -hW; apply: subset_pr.
have hr : range W (ssem_ ps s m).
+ by apply/pr_range/eqP; rewrite pr_predC hT hW subrr.
rewrite -(@eq_exp _ _ _ (fun=> d)).
+ move=> m' hm'; move: (hr m' hm') => /andP [hd /asboolP hE].
  rewrite aux_pr_dlet_dunit; apply/esym.
  have -> : \P_[`[{e}] m'] [pred v | Q m'.[x <- v]] = \P_[`[{e}] m'] E.
  - by apply/eq_in_pr => v hv; rewrite !inE; apply/esym; exact: (hE v hv).
  by apply/eqP.
have -> : \E_[ssem_ ps s m] (fun _ : cmem => d) = d.
+ by rewrite exp_cst hT mul1r.
by apply/eqP.
Qed.

(* (e) [rnd phi d1 d2 d3 d4 [E]] -- [PMultRndParams], six premises, in   *)
(* the order EasyCrypt emits them ([ecPhlRnd.ml:265-289]:                *)
(* [bd_sgoal; sgoal1; sgoal2; sgoal3; sgoal4; sgoal5]).                  *)
(* [Phi] is EasyCrypt's [phi].                                           *)
(*                                                                      *)
(* CORRECTED against the implementation.  This lemma previously carried  *)
(* an opaque [Ev : assn] as a stand-in for the event condition, tied to  *)
(* neither [E] nor [Q] nor the sampled variable, which made it vacuous   *)
(* and false.  That was my error, not EasyCrypt's: [ecPhlRnd.ml:274,280] *)
(* build [sgoal2]/[sgoal4] as                                            *)
(*   forall &m, phi => ((mu d E <> d_i) /\ mk_event_cond E)              *)
(* and [mk_event_cond] ties [E] to [Q[lv := v]] through [subst_form_lv]  *)
(* ([ecLowPhlGoal.ml:597]).  [ec_evcond] above is that condition.        *)
(*                                                                      *)
(* Note [bd_sgoal] is NOT guarded by the precondition here               *)
(* ([ecPhlRnd.ml:270] has no [f_imp (bhs_pr bhs)]), unlike [seq]'s       *)
(* [condbd] ([ecPhlSeq.ml:71]) -- so this premise stays unguarded.       *)

Lemma ec_rnd_split {T : IhbType.type} P Q (Phi : assn)
                   (x : vars T) (e : dexpr T) (E : pred T) s r
                   d d1 d2 d3 d4 :
     r (d1 * d2 + d3 * d4) d
  -> phl P s Phi        r d1
  -> (forall m, Phi m -> r (\P_[`[{e}] m] E) d2 /\ ec_evcond r x e E Q m)
  -> phl P s (~ Phi)%A  r d3
  -> (forall m, ~~ Phi m -> r (\P_[`[{e}] m] E) d4 /\ ec_evcond r x e E Q m)
  -> (0 <= d1 <= 1) && (0 <= d2 <= 1) && (0 <= d3 <= 1) && (0 <= d4 <= 1)
  -> phl P (s ;; (x <$- e)) Q r d.
(* TRUE, and proved.  [sgoal5]'s [0 <= d_i <= 1] is what makes the two   *)
(* one-sided cases go through: [ler_wpM2r] needs [0 <= d2] and [0 <= d4] *)
(* to turn the bounds on [\P_[mu] Phi] and [\P_[mu] (~ Phi)] into bounds *)
(* on the products.  The [=] case needs no bound at all.                 *)
(* Proof: split the expectation over [Phi] ([exp_split]), then bound     *)
(* each conditional expectation on the support ([aux_espc_*]), where the *)
(* event condition turns [\P_[e m'] (Q[./x])] into [\P_[e m'] E].        *)
Proof.
move=> hbd h1 h2 h3 h4.
move=> /andP[/andP[/andP[_ /andP[hd20 _]] _] /andP[hd40 _]].
move=> m Pm; rewrite ssemE.
have -> : \dlet_(m' <- ssem_ ps s m) ssem_ ps (x <$- e) m'
        = \dlet_(m' <- ssem_ ps s m) (\dlet_(v <- `[{e}] m') dunit m'.[x <- v]).
+ by apply: eq_in_dlet; last by []; move=> m' _; rewrite ssemE.
rewrite pr_dlet.
have -> : \E_[ssem_ ps s m]
            (fun m' => \P_[\dlet_(v <- `[{e}] m') dunit m'.[x <- v]] Q)
        = \E_[ssem_ ps s m] (fun m' => \P_[`[{e}] m'] [pred v : T | Q m'.[x <- v]]).
+ by apply/eq_exp => m' _; rewrite aux_pr_dlet_dunit.
set mu := ssem_ ps s m.
(* [Gp], not [G]: [G _ <<- _] is the global-assignment notation.         *)
set Gp := (fun m' => \P_[`[{e}] m'] [pred v : T | Q m'.[x <- v]]).
have hG : forall m2 : cmem, (0 <= Gp m2 <= 1)%R.
+ by move=> m2; rewrite ge0_pr le1_pr.
have hE : \E?_[mu] Gp.
+ by apply: bounded_has_exp; exists 1 => m'; rewrite ger0_norm ?ge0_pr ?le1_pr.
rewrite (exp_split Phi hE).
move: (h1 m Pm) (h3 m Pm) hbd => {h1 h3 Pm}.
case: r h2 h4 => h2 h4 h1 h3 hbd /=.
(* Le *)
+ apply: (le_trans _ hbd); apply: lerD.
  - apply: (@le_trans _ _ (\P_[mu] Phi * d2)); last by rewrite ler_wpM2r.
    apply: aux_espc_le; first exact: hG.
    move=> m' hm'; move: hm'; rewrite dinsupp_restr => /andP[_ /h2[hd2 hev]].
    apply: (le_trans _ hd2); apply: le_in_pr => v hv.
    by rewrite !inE; exact: (hev v hv).
  - apply: (@le_trans _ _ (\P_[mu] (~ Phi)%A * d4)); last by rewrite ler_wpM2r.
    apply: aux_espc_le; first exact: hG.
    move=> m' hm'; move: hm'; rewrite dinsupp_restr => /andP[_ /h4[hd4 hev]].
    apply: (le_trans _ hd4); apply: le_in_pr => v hv.
    by rewrite !inE; exact: (hev v hv).
(* Ge *)
+ apply: (le_trans hbd); apply: lerD.
  - apply: (@le_trans _ _ (\P_[mu] Phi * d2)); first by rewrite ler_wpM2r.
    apply: aux_espc_ge; first exact: hG.
    move=> m' hm'; move: hm'; rewrite dinsupp_restr => /andP[_ /h2[hd2 hev]].
    apply: (le_trans hd2); apply: le_in_pr => v hv.
    by rewrite !inE => hEv; exact: (hev v hv hEv).
  - apply: (@le_trans _ _ (\P_[mu] (~ Phi)%A * d4)); first by rewrite ler_wpM2r.
    apply: aux_espc_ge; first exact: hG.
    move=> m' hm'; move: hm'; rewrite dinsupp_restr => /andP[_ /h4[hd4 hev]].
    apply: (le_trans hd4); apply: le_in_pr => v hv.
    by rewrite !inE => hEv; exact: (hev v hv hEv).
(* Eq *)
+ apply/eqP; rewrite -(eqP hbd); congr (_ + _).
  - rewrite (@aux_espc_eq _ mu Gp Phi d2) ?(eqP h1) //.
    move=> m' hm'; move: hm'; rewrite dinsupp_restr => /andP[_ /h2[hd2 hev]].
    rewrite /Gp -(eqP hd2); apply/eq_in_pr => v hv.
    by rewrite !inE; exact/esym/(hev v hv).
  - rewrite (@aux_espc_eq _ mu Gp (~ Phi)%A d4) ?(eqP h3) //.
    move=> m' hm'; move: hm'; rewrite dinsupp_restr => /andP[_ /h4[hd4 hev]].
    rewrite /Gp -(eqP hd4); apply/eq_in_pr => v hv.
    by rewrite !inE; exact/esym/(hev v hv).
Qed.

(* -------------------------------------------------------------------- *)
(* S1.7  rndsem -- NOT FORMALIZED.                                       *)
(* [Core.t_bdhoare_rndsem_r], ecPhlRnd.ml:424; [process_rndsem], :723.   *)
(* [Core.t_bdhoare_rndsem_r] replaces a trailing block of samplings by   *)
(* one *semantic* sampling.  [cmd_] has no semantic-sampling             *)
(* constructor, so the rule has no counterpart here.                     *)


(* -------------------------------------------------------------------- *)
(* S1.8  while -- three rules, [ecPhlWhile.ml].                          *)
(*   (a) [t_bdhoare_while_r]          [:127-153]  any comparison         *)
(*   (b) [t_bdhoare_while_rev_r]      [:157-200]  [<=] only ([:161])     *)
(*   (c) [t_bdhoare_while_rev_geq_r]  [:205-306]  [>=]/[=] only ([:210]) *)
(* [process_while] ([:548-587]) picks between them on the presence of a  *)
(* variant and of the [k eps] bounds.                                    *)
(*                                                                      *)
(* The variant is [vrnt : cmem -> int], matching EasyCrypt's use of      *)
(* [vrnt <= 0] as the termination threshold.                            *)
(* phl.v has NO loop rule at all, so all three are new here.             *)
(*                                                                      *)
(* (a) and (b) apply to a statement [s ; while e do c] and act on the    *)
(* trailing loop ([tc1_last_while], [:130] and [:170]); the prefix [s]   *)
(* is therefore part of the statement below.  (c) instead requires the   *)
(* loop to be the WHOLE statement ([check_single_stmt], [:230],          *)
(* definition [:92-94]), so it has no prefix.                            *)
(*                                                                      *)
(* THE ABSTRACT STATEMENT of (b) and (c).  [body_concl] in both reverse  *)
(* rules is discharged in a context carrying a fresh abstract statement  *)
(* [w] ([xmutate1_hyps], [:200] and [:300]), constrained by             *)
(* [while_info] ([:22, :173, :285]) to the loop's reads, writes and      *)
(* calls.  Since the conclusion does not mention [w], soundness needs    *)
(* the premise to hold for EVERY instantiation, so it is rendered here   *)
(* as [forall w : cmd, ... -> ...].  pwhile's [cmd] carries no           *)
(* read/write annotation and [hl.mod] cannot supply one without         *)
(* [nocall] (G5), so the [while_info] restriction is dropped: [w] ranges *)
(* over ALL commands.  That STRENGTHENS the premise and hence weakens    *)
(* the rules below, so it is sound and is never the source of a          *)
(* [!!! WRONG] flag -- see [ec_while_rev_eq] for why that matters.       *)

(* ==================================================================== *)
(* ===  AUXILIARY -- the semantic core of the S1.8(a) variant rule  === *)
(* ==================================================================== *)
(* NOT an EasyCrypt rule.  This is what the variant premises actually    *)
(* buy: from an [I]-state the loop terminates almost surely, in an       *)
(* [I /\ ~e] state.  It is the loop-only, [= 1] specialisation of        *)
(* [t_bdhoare_while_r]; both [ec_while_variant] (in its sound [>=]       *)
(* instance) and [ec_ll_while] (S4.5) rest on it.                        *)
(*                                                                      *)
(* Proof: [ssem_whileE] then [range]/[pr] on [whilen e c n], by strong   *)
(* induction on [vrnt m]; the body being [= 1] makes each unrolling      *)
(* mass-preserving and [homo_whilen] gives the limit.                    *)

Lemma aux_phl_while_ll (I : assn) (vrnt : cmem -> int) (e : bexpr) c :
     (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            (I /\ [pred m | vrnt m < z])%A '= 1)
  -> (forall m, I m -> vrnt m <= 0 -> ~~ `[{e}] m)
  -> phl I (While e Do c) (I /\ ~ `[{e}])%A '= 1.
Proof.
move=> hbody hterm.
have hwn : forall k, whilen e c k.+1
                   = If e then (c ;; whilen e c k) else skip by [].
(* [n+1] unrollings suffice from any state whose variant is at most [n]. *)
have key : forall n : nat, forall m, I m -> (vrnt m <= n%:Z)%R ->
             \P_[ssem_ ps (whilen e c n.+1) m] (I /\ ~ `[{e}])%A = 1.
+ elim=> [|n ihn] m Im hv.
  { have hne := hterm m Im hv.
    rewrite hwn ssem_ifE (negbTE hne) ssem_skipE pr_dunit.
    by rewrite /= Im (negbTE hne) /= mulr1n. }
  rewrite hwn ssem_ifE; case: ifPn => hem; last first.
  { rewrite ssem_skipE pr_dunit.
    by rewrite /= Im (negbTE hem) /= mulr1n. }
  have hb : \P_[ssem_ ps c m] (I /\ [pred m0 | vrnt m0 < vrnt m])%A = 1.
  { by apply/eqP; apply: (hbody (vrnt m) m); rewrite /= Im hem eqxx. }
  have hwT : \P_[ssem_ ps c m] predT = 1.
  { by apply/le_anti; rewrite le1_pr /= -hb; apply: subset_pr. }
  have hrng : range (I /\ [pred m0 | vrnt m0 < vrnt m])%A (ssem_ ps c m).
  { by apply/pr_range/eqP; rewrite pr_predC hwT hb subrr. }
  rewrite ssem_seqE pr_dlet; apply/le_anti/andP; split.
  { apply: exp_le_bd; first exact: ler01.
    by move=> m'; rewrite ger0_norm ?ge0_pr ?le1_pr. }
  have hge : \P_[ssem_ ps c m] predT * 1
          <= \E_[ssem_ ps c m]
               (fun m0 => \P_[ssem_ ps (whilen e c n.+1) m0] (I /\ ~ `[{e}])%A).
  { apply: aux_exp_ge => m' hm'; move: (hrng m' hm') => /andP [Im' hlt].
    have hv' : (vrnt m' <= n%:Z)%R.
    { by apply: aux_ltzS; apply: (lt_le_trans hlt hv). }
    by rewrite (ihn m' Im' hv'); apply: lexx. }
  by move: hge; rewrite hwT mul1r.
move=> m Im; rewrite ssemE; apply/eqP/le_anti/andP; split; first exact: le1_pr.
apply: (aux_pr_dlim_ge (k := (`|vrnt m|%N).+1)).
+ by move=> n p le_np x; apply: homo_whilen.
rewrite (key `|vrnt m|%N m Im) ?lexx //.
by rewrite abszE; exact: ler_norm.
Qed.

(* ==================================================================== *)
(* ===                back to the EasyCrypt rules                   === *)
(* ==================================================================== *)

(* (a) Variant rule ([while (inv) (vrnt)], [t_bdhoare_while_r],          *)
(* [ecPhlWhile.ml:127-153]).  [process_while] ([:567-572]) dispatches    *)
(* here for ANY comparison, so the rule is stated at a general [r].      *)
(*                                                                      *)
(* EasyCrypt's goal is [bdHoareS P (s; while e do c) Q ⋈ b], with [s]    *)
(* the prefix returned by [tc1_last_while] ([:130]).  It emits exactly   *)
(* two subgoals, [b_concl] and [concl] ([:153]):                         *)
(*   [b_concl] ([:134-141]) is the body premise, at [FHeq 1%r], with the *)
(*     variant frozen at a fresh integer [z];                            *)
(*   [concl] ([:142-151]) is [bdHoareS P s post ⋈ b] where               *)
(*     [post = inv /\ forall mod(c). (term_condition /\ post')],         *)
(*     [term_condition = inv => vrnt <= 0 => ~e]  ([:145-146]),          *)
(*     [post' = ~e => inv => Q]                   ([:143-144]).          *)
(* (Both are built with [f_imps_simpl'], head = conclusion; see the      *)
(* orientation note in S1.6.)                                            *)
(* Per (G5) the [forall mod(c)] parts are stated over ALL memories,      *)
(* which splits [concl] into [phl P s I r d] plus the two side           *)
(* conditions.  That is strictly stronger, so it cannot be the source of *)
(* the failure below.                                                    *)

(* !!! WRONG -- FALSE as written at [<=] and at [=]; sound only at [>=]. *)
(* This one is not about the bound: it is the rule itself.  Nothing in   *)
(* [t_bdhoare_while_r] relates the postcondition to the states in which  *)
(* [inv] FAILS after [s].  Semantically                                  *)
(*   \P_[s;while] Q = \E_[s] (fun m' => \P_[while@m'] Q)                 *)
(* and the premises pin [\P_[while@m'] Q = 1] only for [I]-states [m'],  *)
(* leaving [\P_[while@m'] Q] arbitrary in [[0,1]] elsewhere.  Hence      *)
(* [\P_[s;while] Q >= \P_[s] I], and only the [>=] direction transfers.  *)
(* Note there is NO [P => inv] subgoal: the tactic emits two subgoals    *)
(* ([:153]) and neither is one.                                          *)
(*                                                                      *)
(* COUNTEREXAMPLE, machine-checked -- take the invariant IDENTICALLY     *)
(* FALSE and the guard identically false:                                *)
(*   [P := Q := predT], [I := pred0], [vrnt := fun _ => 0],              *)
(*   [e := false%:S], [s := skip], [c := skip], [r := Le], [d := 0].     *)
(* The body premise, the termination premise and the exit premise all    *)
(* have [I] in their hypotheses, hence are vacuous; the residual is      *)
(* [phl predT skip pred0 '<= 0], i.e. [0 <= 0].  But                     *)
(* [ssem (skip ;; While false%:S Do skip) m = dunit m] by [ssem_while0], *)
(* so the conclusion asserts [1 <= 0].                                   *)
(* The same instance at [r := Eq] and [d := 0] refutes the [=] case.     *)
(* Note the bound [0] is perfectly ordinary here -- unlike the S1.2 and  *)
(* S1.6 findings, this failure needs no exotic bound at all.             *)
(*                                                                      *)
(* At [>=] the rule IS sound, and follows from [aux_phl_while_ll] above  *)
(* by [ec_seq_ge]-style reasoning.                                       *)
(*                                                                      *)
(* EASYCRYPT WITNESS: phl/easycrypt/ec_while_variant.ec proves [false].  *)
(* It is the one witness whose bound ([0%r]) is entirely ordinary.       *)

Lemma ec_while_variant P Q (I : assn) (vrnt : cmem -> int) (e : bexpr)
                       s c r d :
     (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            (I /\ [pred m | vrnt m < z])%A '= 1)
  -> (forall m, I m -> vrnt m <= 0 -> ~~ `[{e}] m)
  -> (forall m, ~~ `[{e}] m -> I m -> Q m)
  -> phl P s I r d
  -> phl P (s ;; While e Do c) Q r d.
Proof. Admitted.

(* (b) Reverse rule ([while (inv)], [t_bdhoare_while_rev_r],             *)
(* [ecPhlWhile.ml:157-200]).  Upper bounds only: [:161-162] rejects any  *)
(* comparison other than [FHle].                                        *)
(*                                                                      *)
(* Two subgoals ([:200]):                                                *)
(*   [body_concl] ([:178-186]) introduces an ABSTRACT STATEMENT [w]      *)
(*     standing for the rest of the loop ([i_abstract w], [:179]) and    *)
(*     asks for one unfolding step.  Here that is a genuine              *)
(*     quantification over commands.                                     *)
(*   [rem_concl] ([:189-198]) is a *Hoare* goal ([f_hoareS], [:197]) on  *)
(*     the prefix [rem_s]:                                               *)
(*       hoare[ rem_s : P ==> inv /\ forall mod(body).                    *)
(*                              ((inv /\ ~e /\ Q) => bound = 1%r) ]      *)
(*     -- note [f_eq bound f_r1] at [:193]: an EQUALITY [d = 1], not     *)
(*     [1 <= d].  Per (G5) the [forall mod] part is stated below over    *)
(*     ALL memories, which splits [rem_concl] into [hoare P s I] plus a  *)
(*     side condition.                                                   *)

(* !!! WRONG -- FALSE as written; missing [0 <= d].  Fourth instance of  *)
(* the unconstrained-bound defect, after [ec_seq_le], [ec_seq_ge] and    *)
(* [ec_rnd_le] (see also [ec_call_seq_le]).  An earlier                  *)
(* version of this lemma carried [0 <= d] and [1 <= d] premises and was  *)
(* provable; NEITHER is in [t_bdhoare_while_rev_r], and [:193]'s         *)
(* [bound = 1%r] is only ever triggered at exit states satisfying [Q].   *)
(* When no reachable exit state satisfies [Q], and the guard is false so *)
(* the body premise is vacuous, nothing constrains [d] at all.           *)
(*                                                                      *)
(* COUNTEREXAMPLE, machine-checked --                                    *)
(*   [P := I := predT], [Q := pred0], [e := false%:S],                   *)
(*   [s := skip], [c := skip], [d := -1].                                *)
(* The body premise has precondition [I /\ `[{e}]] = [pred0], hence is   *)
(* vacuous; the bound premise has [Q m] = [false] in its hypotheses,     *)
(* hence is vacuous; [hoare predT skip predT] holds.  But                *)
(* [ssem (skip ;; While false%:S Do skip) m = dunit m] and               *)
(* [\P_[dunit m] pred0 = 0], so the conclusion asserts [0 <= -1].        *)
(*                                                                      *)
(* Adding [0 <= d] repairs it, and [1 <= d] (weaker than [d = 1]) then   *)
(* makes the proof below go through:                                     *)
(*   [ssem_whileE] + [sum_dlim_r_r]; induct on [n], instantiating the    *)
(*   body premise at [w := whilen e c n]; the base case [whilen e c 0 =  *)
(*   abort] needs [0 <= d] and the [skip] branch needs [1 <= d].         *)
(*                                                                      *)
(* EASYCRYPT WITNESS: phl/easycrypt/ec_while_rev.ec proves [false].      *)

Lemma ec_while_rev P Q (I : assn) (e : bexpr) s c d :
     (forall w : cmd, phl I w Q '<= d -> phl (I /\ `[{e}])%A (c ;; w) Q '<= d)
  -> hoare P s I
  -> (forall m, I m -> ~~ `[{e}] m -> Q m -> d = 1)
  -> phl P (s ;; While e Do c) Q '<= d.
Proof. Admitted.

(* (c) Reverse rule with a rate ([while (inv) (vrnt) k eps],             *)
(* [t_bdhoare_while_rev_geq_r], [ecPhlWhile.ml:205-306]), lower and      *)
(* exact bounds only ([:210-211] rejects [FHle]).  [eps] is the          *)
(* per-iteration lower bound on the probability that the variant         *)
(* decreases and [k] its upper bound; together they make the loop        *)
(* almost surely terminating at a rate.  The loop must be the whole      *)
(* statement ([check_single_stmt], [:230]), which is automatic below.    *)
(*                                                                      *)
(* DEVIATION: [pre_bound_concl] ([:248]) and [inv_term_concl] ([:257])   *)
(* are guarded by [generalize_mod_ss_inv env modi], i.e. EasyCrypt's     *)
(* [forall mod(body)].  They are stated here over *all* memories, which  *)
(* is a strictly stronger premise and therefore a sound (but less        *)
(* applicable) rule.  Stating them with (G5) would drag in a [nocall c]  *)
(* hypothesis; see S2.3.                                                 *)
(*                                                                      *)
(* Premises are in the order EasyCrypt emits them ([:300-306]):          *)
(* [pre_inv_concl] ([:237]), [pre_bound_concl] ([:240-250]),             *)
(* [inv_term_concl] ([:253-258]), [body_concl] ([:289-298]),             *)
(* [inv_concl] ([:280-282]), [vrnt_concl] ([:261-277], itself a          *)
(* conjunction, split into the last two premises here).  Note            *)
(* [body_concl] is stated with the PRECONDITION [P], not with [inv]      *)
(* ([:293-295] uses [b_pre]).                                            *)

(* !!! WRONG -- FALSE as written; missing [d <= 1].  EasyCrypt's         *)
(* [pre_bound_concl] at [>=] ([:245]) is [P => ~e => (~Q => b = 0)],     *)
(* constrains the bound only on the [~Q] branch.  When [Q] DOES hold at  *)
(* an exit state the rule still claims [b <= \P_[.] Q <= 1], but nothing *)
(* anywhere forces [b <= 1].                                             *)
(*                                                                      *)
(* COUNTEREXAMPLE, machine-checked -- take the guard identically false,  *)
(*   [P := Q := I := predT], [e := false%:S], [vrnt := fun _ => 0],      *)
(*   [k := 0], [eps := 1], [d := 2%:R].                                  *)
(* Premises: [P => I] is trivial; [pre-bound] is vacuous ([~ Q] is       *)
(* false); [term-invariant] is [(0 <= 0) && (0 <= 0 ==> true)]; the      *)
(* [body], [out-invariant] and [vrnt] premises all have a precondition   *)
(* containing [`[{e}]], hence [false], so they are vacuous; and          *)
(* [0 < eps].  But [ssem_while0] gives [ssem (While e Do c) m = dunit m],*)
(* so the conclusion asserts [2 <= \P_[dunit m] predT = 1].              *)
(*                                                                      *)
(*                                                                      *)
(* EASYCRYPT WITNESS: phl/easycrypt/ec_while_rev_geq.ec proves [false].  *)
(* Note the [~ Q] antecedent of [pre_bound_concl] is what a [Q := true]  *)
(* instance disarms; see the [=] sibling below, which does NOT have      *)
(* that escape.                                                          *)
Lemma ec_while_rev_geq P Q (I : assn) (vrnt : cmem -> int) (e : bexpr)
                       c d (k : int) (eps : R) :
     (forall m, P m -> I m)
  -> (forall m, P m -> ~~ `[{e}] m -> ~~ Q m -> d = 0)
  -> (forall m, I m -> (vrnt m <= k) && (vrnt m <= 0 ==> ~~ `[{e}] m))
  -> (forall w : cmd, phl P w Q '>= d -> phl (P /\ `[{e}])%A (c ;; w) Q '>= d)
  -> phl (I /\ `[{e}])%A c I '= 1
  -> (forall m, I m -> 0 < eps)
  -> (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            [pred m | vrnt m < z] '>= eps)
  -> phl P (While e Do c) Q '>= d.
Proof. Admitted.

(* !!! WRONG -- FALSE as written; missing [d <= 1], exactly as in       *)
(* [ec_while_rev_geq] above ([ecPhlWhile.ml:243-244] is the [FHeq] row   *)
(* of the same [pre_bound_concl]).  The [=] shape does NOT escape it:    *)
(* the pre-bound premise [P => ~e => b = (Q ? 1 : 0)] pins [b] only at   *)
(* states where the guard is ALREADY false, so it is vacuous whenever    *)
(* every [P]-state satisfies [e] -- which is the normal situation for a  *)
(* loop that actually runs.  [b] is then unconstrained while the         *)
(* conclusion asserts [\P_[.] Q = b] with the left-hand side in [0,1].   *)
(*                                                                      *)
(* COUNTEREXAMPLE, machine-checked -- one [nat] variable [g], and        *)
(*   [P := E], [e := prp_ E] with [E := [pred m | m.[g] = 1]],           *)
(*   [I := predT], [Q := predT], [c := g <<- 0],                         *)
(*   [vrnt := fun m => if m.[g] == 1 then 1 else 0], [k := 1],           *)
(*   [eps := 1], [d := 2%:R].                                            *)
(* Every [P]-state satisfies [e], so pre-bound is vacuous; [P => I] and  *)
(* term-invariant are immediate; the body premise is vacuous because     *)
(* [phl P w Q '= 2%:R] contradicts [le1_pr] at any [P]-state; the        *)
(* out-invariant and vrnt premises hold because the body sets [g] to 0,  *)
(* which makes the variant drop from 1 to 0.  But the loop then runs     *)
(* exactly one iteration and stops, so [ssem (While e Do c) m] is a      *)
(* [dunit] and the conclusion asserts [1 = 2].                           *)
(*                                                                      *)
(* NO EASYCRYPT WITNESS -- and the reason is instructive.  Unlike its    *)
(* [>=] sibling, this defect is NOT reachable from the surface, so       *)
(* phl/easycrypt/ has no script for it.  Both routes are blocked:        *)
(*                                                                      *)
(*  (i) guard false at entry (the [>=] instance).  At [FHeq],            *)
(*      [pre_bound_concl] ([ecPhlWhile.ml:243-244]) is                   *)
(*      [P => ~e => b = (Q ? 1 : 0)] with NO [~ Q] antecedent to         *)
(*      disarm, so [~ e] holds and [b] is pinned to the true value.      *)
(*      Machine-checked: at [b := 2%r], [Q := true] the premise comes    *)
(*      out as [2%r = b2r true], i.e. [2 = 1] -- unprovable.             *)
(*                                                                      *)
(* (ii) guard true at entry.  Then [generalize_mod_ss_inv] ([:248])      *)
(*      quantifies the loop's written variables, and [pre_bound_concl]   *)
(*      does become vacuous ([x = 1 => x <> 1 => ...]).  But now         *)
(*      [body_concl] ([:289-298]) is live:                               *)
(*        phoare[ w : P ==> Q ] = b                                      *)
(*        => phoare[ body; w : P /\ e ==> Q ] = b                        *)
(*      and it cannot be discharged.  The hypothesis speaks of [w] from  *)
(*      [P], but [body] must falsify [e] for the loop to terminate, and  *)
(*      [P => e] (which is what made (i)'s premise vacuous) then means   *)
(*      [P] fails after [body].  Machine-checked: after [sp 1] the goal's*)
(*      precondition is [B.x = 0] while the hypothesis needs [B.x = 1].  *)
(*      Nor can the absurd hypothesis ([= 2%r], above 1) be turned into  *)
(*      [false]: [w] is an ABSTRACT STATEMENT ([LD_abs_st], [:287]), so  *)
(*      there is no [Pr[...]] to instantiate it at.                      *)
(*                                                                      *)
(*      The other five premises of (ii) all discharge; only              *)
(*      [body_concl] blocks.                                             *)
(*                                                                      *)
(* THE STATEMENT BELOW NEVERTHELESS MATCHES THE TACTIC, premise for      *)
(* premise.  An earlier version of this note claimed the Coq statement   *)
(* was "weaker than the tactic" because [forall w : cmd, ...] lets a     *)
(* Coq proof exploit an absurd hypothesis.  That was wrong, in two ways. *)
(*                                                                      *)
(* First, the direction is backwards.  EasyCrypt's [w] is constrained by *)
(* [while_info] ([ecPhlWhile.ml:22, :285]) to the loop's reads, writes   *)
(* and calls, so it ranges over FEWER statements than [w : cmd] does.    *)
(* Quantifying over all commands is the STRONGER premise, hence the      *)
(* WEAKER lemma -- so it cannot be what makes the lemma false.  (Not     *)
(* modelling that restriction is a (G5)-style deviation: pwhile's [cmd]  *)
(* carries no read/write annotation, and [hl.mod] cannot supply one      *)
(* without [nocall]; being a strengthening of a premise, it is sound.)   *)
(*                                                                      *)
(* Second, and more importantly: the vacuity is in the RULE, not in the  *)
(* encoding.  [xmutate1_hyps] ([:300]) discharges [body_concl] in a      *)
(* context where [w] is a free abstract-statement variable, so what the  *)
(* tactic's soundness needs is that the implication hold for EVERY       *)
(* instantiation of [w] -- exactly [forall w, H w -> C w].  At [b := 2]  *)
(* with [P] satisfiable, [H w] is false for every [w], so that premise   *)
(* is vacuously true and the conclusion is false.  The RULE IS UNSOUND.  *)
(*                                                                      *)
(* What stops EasyCrypt is not soundness but INCOMPLETENESS: its logic   *)
(* has no way to derive [false] from [phoare[w : P ==> Q] = 2%r] for an  *)
(* abstract [w], because there is no [Pr[...]] to instantiate it at.  So *)
(* the [!!! WRONG] flag stands and the lemma is genuinely false; there   *)
(* is simply no [.ec] script exhibiting it.  This is the one finding in  *)
(* the file of the form "unsound rule, unexploitable in practice".       *)
(*                                                                      *)
(* Adding [0 <= d <= 1] would rule the counterexample out, and is what   *)
(* the tactic's proof obligations enforce de facto -- but it is NOT a    *)
(* premise of [t_bdhoare_while_rev_geq_r], so it is deliberately not     *)
(* added here.  Per the agreed rule, the statement follows the           *)
(* implementation and the divergence is reported rather than patched.    *)
Lemma ec_while_rev_eq P Q (I : assn) (vrnt : cmem -> int) (e : bexpr)
                      c d (k : int) (eps : R) :
     (forall m, P m -> I m)
  -> (forall m, P m -> ~~ `[{e}] m -> d = (if Q m then 1 else 0))
  -> (forall m, I m -> (vrnt m <= k) && (vrnt m <= 0 ==> ~~ `[{e}] m))
  -> (forall w : cmd, phl P w Q '= d -> phl (P /\ `[{e}])%A (c ;; w) Q '= d)
  -> phl (I /\ `[{e}])%A c I '= 1
  -> (forall m, I m -> 0 < eps)
  -> (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            [pred m | vrnt m < z] '>= eps)
  -> phl P (While e Do c) Q '= d.
Proof. Admitted.


(* -------------------------------------------------------------------- *)
(* S1.9  call.                                                           *)
(* [t_bdhoare_call], ecPhlCall.ml:304 ([bdhoare_call_spec] :291-301, wp *)
(* orientation :326-336, residual table :344-359, emission :361);        *)
(* dispatcher [t_call] bdHoare arms :432, :449-453, :471-477.            *)
(*                                                                      *)
(* By (G3), EasyCrypt's [lv <@ f(args)] is                               *)
(*   [Block bs Do (call f) Return rs].                                   *)
(* The rule is reached in three steps.                                   *)

(* Step 1 -- the block rule, missing from phl.v ([hl_block] and          *)
(* [ehl_block] exist).  It is an equality, not an inequality, because    *)
(*   ssem (Block bs Do c Return rs) m                                    *)
(*     = \dlet_(m' <- ssem c (minit m bs)) dunit (mret m m' rs)          *)
(* is a [dmargin], and [pr_dmargin] transports the probability exactly:  *)
(*   \P_[ssem (Block bs Do c Return rs) m] Q                             *)
(*     = \P_[ssem c (minit m bs)] [pred m' | Q (mret m m' rs)].          *)
(* Shape taken from [hl_block] (hl/hl.v:173).                            *)

Lemma ec_block P Q (bs rs : seq (@binding _ cmem)) c r d :
     (forall m, P m ->
        phl [pred m0 | m0 == minit m bs] c [pred m' | Q (mret m m' rs)] r d)
  -> phl P (Block bs Do c Return rs) Q r d.
Proof.
move=> h m Pm; rewrite ssemE aux_pr_dlet_dunit.
by apply: (h m Pm); rewrite /= eqxx.
Qed.

(* Step 2 -- the callee spec, oriented by the comparison.  The three     *)
(* orientations are exactly the catalogue's [wp] table                   *)
(* ([ecPhlCall.ml:326-336]): [post => Q'] at [<=], [Q' => post] at       *)
(* [>=], and an equivalence at [=].  No [forall res, forall mod(f)] is   *)
(* needed: the premise quantifies over the callee's whole final memory   *)
(* [m'] (G3).                                                            *)

Lemma ec_call_le P Q (Pf Qf : assn) (f : ident) (bs rs : seq (@binding _ cmem)) d :
     (forall m, P m -> Pf (minit m bs))
  -> (forall m m', P m -> Q (mret m m' rs) -> Qf m')
  -> phl Pf (call f) Qf '<= d
  -> phl P (Block bs Do (call f) Return rs) Q '<= d.
Proof.
move=> hpre hpost h; apply: ec_block => m Pm m0 /eqP ->.
apply: (le_trans _ (h _ (hpre m Pm))); apply: le_in_pr => m' _.
by rewrite ?inE; exact: (hpost m m' Pm).
Qed.

Lemma ec_call_ge P Q (Pf Qf : assn) (f : ident) (bs rs : seq (@binding _ cmem)) d :
     (forall m, P m -> Pf (minit m bs))
  -> (forall m m', P m -> Qf m' -> Q (mret m m' rs))
  -> phl Pf (call f) Qf '>= d
  -> phl P (Block bs Do (call f) Return rs) Q '>= d.
Proof.
move=> hpre hpost h; apply: ec_block => m Pm m0 /eqP ->.
apply: (le_trans (h _ (hpre m Pm))); apply: le_in_pr => m' _.
by rewrite ?inE; exact: (hpost m m' Pm).
Qed.

Lemma ec_call_eq P Q (Pf Qf : assn) (f : ident) (bs rs : seq (@binding _ cmem)) d :
     (forall m, P m -> Pf (minit m bs))
  -> (forall m m', P m -> Q (mret m m' rs) = Qf m')
  -> phl Pf (call f) Qf '= d
  -> phl P (Block bs Do (call f) Return rs) Q '= d.
Proof.
move=> hpre hpost h; apply: ec_block => m Pm m0 /eqP ->.
have -> : \P_[ssem_ ps (call f) (minit m bs)] [pred m' | Q (mret m m' rs)]
        = \P_[ssem_ ps (call f) (minit m bs)] Qf.
+ by apply/eq_pr => m'; rewrite ?inE; exact: (hpost m m' Pm).
exact: (h _ (hpre m Pm)).
Qed.

(* Step 3 -- with a prefix [s].  [t_bdhoare_call], [ecPhlCall.ml:304-361]*)
(* CORRECTED against the implementation.  [:361] emits EXACTLY TWO       *)
(* subgoals, [f_concl] (the callee spec, [:315-316] via                  *)
(* [bdhoare_call_spec], [:291-301]) and [concl] (the residual on the     *)
(* prefix, [:344-359]).  There is NO separate almost-surely premise:     *)
(* earlier versions of the [>=] and [=] lemmas below carried an extra    *)
(* [hoare P s wp] premise "discharged inside the seq application", which *)
(* is not in the tactic.  It has been removed; the [=] row was PROVED    *)
(* using it and is now false (see its flag).                             *)
(*                                                                      *)
(* The residual table ([:346-358]), with [opt_bd] the optional bound:    *)
(*   [FHle], [None]     -> [hoareS P s wp]              (a Hoare goal)   *)
(*   [FHeq], [Some d']  -> [bdHoareS P s wp FHeq (d/d')]                 *)
(*   [FHeq], [None]     -> [bdHoareS P s wp FHeq 1]                      *)
(*   [FHge], [Some d']  -> [bdHoareS P s wp FHge (d/d')]                 *)
(*   [FHge], [None]     -> [bdHoareS P s wp **FHeq** 1]  <- note the     *)
(*                          comparison SWITCHES to [FHeq] at [:357]      *)
(*   [FHle], [Some _]   -> rejected ([:296])                             *)
(* The [Some d'] rows are stated below.  They are DEAD FROM THE SURFACE: *)
(* every caller passes [None] ([ecPhlCall.ml:453], [ecPhlHiAuto.ml:68]), *)
(* so the reachable [>=] and [=] rows are the [None] ones, whose         *)
(* residual is [phl P s wp '= 1] -- i.e. the [d' := d] instance of the   *)
(* lemmas below, with the residual comparison replaced by [=].           *)
(*                                                                      *)
(* Note also that [:351] and [:355] build the division [d / d'] with no  *)
(* [d' <> 0] side condition anywhere; earlier versions of these lemmas   *)
(* carried [d' != 0] as a premise.  It has been removed too (in Coq as   *)
(* in EasyCrypt, [d / 0 = 0]).                                          *)

(* !!! WRONG -- FALSE as written; missing [0 <= d].  Same defect as      *)
(* [ec_seq_le]: on the support the prefix gives [F m' <= d], so          *)
(* [\E_[mu] F <= \P_[mu] predT * d], and that is [<= d] only when        *)
(* [0 <= d], since the sub-distribution weight is [<= 1], not [= 1].     *)
(* COUNTEREXAMPLE, machine-checked -- [P := predT], [s := abort],        *)
(* [Pf := pred0], [Qf := predT], [Q := predT], [bs = rs = [::]],         *)
(* [d := -1].  The [hoare] premise holds because [ssem abort m = dnull]; *)
(* the contract premise is vacuous ([Pf = pred0]); but                   *)
(* [ssem (abort ;; _) m = dnull], so the conclusion asserts [0 <= -1].   *)
(*                                                                      *)
(* EASYCRYPT WITNESS: phl/easycrypt/ec_call_seq_le.ec proves [false].    *)
Lemma ec_call_seq_le P Q (Pf Qf : assn) (f : ident)
                     (bs rs : seq (@binding _ cmem)) s d :
     hoare P s [pred m | Pf (minit m bs)
                         && `[< forall m', Q (mret m m' rs) -> Qf m' >]]
  -> phl Pf (call f) Qf '<= d
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q '<= d.
Proof. Admitted.

(* !!! WRONG -- FALSE as written; missing [0 < d'].  A negative callee   *)
(* bound is satisfied by every probability, so it constrains nothing,    *)
(* while [d / d'] flips sign and makes the prefix premise vacuous too.   *)
(* COUNTEREXAMPLE, machine-checked -- [P := predT], [s := abort],        *)
(* [Pf := pred0], [Qf := predT], [Q := predT], [bs = rs = [::]],         *)
(* [d := 1], [d' := -1].  Then [d / d' = -1 <= 0 = \P_[dnull] _] gives   *)
(* the prefix premise and the contract premise is vacuous.  But          *)
(* [ssem (abort ;; _) m = dnull], so the conclusion asserts [1 <= 0].    *)
(*                                                                      *)
(* NO EASYCRYPT WITNESS -- this row is DEAD CODE.  It is the             *)
(* [(FHge, Some bd)] arm ([ecPhlCall.ml:354-355]), and [opt_bd] is       *)
(* [None] at BOTH call sites of [t_bdhoare_call] ([ecPhlCall.ml:453] in  *)
(* [t_call], [ecPhlHiAuto.ml:68] in the losslessness strategy).  No      *)
(* surface syntax reaches it, so no [.ec] script can exist.  The         *)
(* reachable [(FHge, None)] arm ([:356-357]) switches the residual       *)
(* comparison to [FHeq 1%r], which forces the prefix to be lossless and  *)
(* is sound.  The finding here is therefore "EasyCrypt contains unsound  *)
(* dead code", not "EasyCrypt proves false".                             *)
Lemma ec_call_seq_ge P Q (Pf Qf : assn) (f : ident)
                     (bs rs : seq (@binding _ cmem)) s d d' :
     phl P s [pred m | Pf (minit m bs)
                       && `[< forall m', Qf m' -> Q (mret m m' rs) >]] '>= (d / d')
  -> phl Pf (call f) Qf '>= d'
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q '>= d.
Proof. Admitted.

(* !!! WRONG -- FALSE once the invented almost-surely premise is gone.   *)
(* This lemma WAS proved, using an extra                                 *)
(*   [hoare P s [pred m | Pf (minit m bs) && ...]]                       *)
(* premise, which let the proof turn [\P_[mu] predT] into [\P_[mu] wp]   *)
(* and conclude [\E_[mu] F = \P_[mu] wp * d' = (d/d') * d' = d].         *)
(* [t_bdhoare_call] emits no such premise ([ecPhlCall.ml:361]), and      *)
(* without it the memories OFF the [wp] contribute unconstrained mass:   *)
(* the contract pins [F m' = d'] only where [Pf (minit m' bs)] holds.    *)
(*                                                                      *)
(* COUNTEREXAMPLE, machine-checked -- every procedure body [skip], and   *)
(*   [P := Q := Qf := predT], [Pf := pred0], [s := skip],                *)
(*   [bs = rs = [::]], [d := 0], [d' := 1].                              *)
(* The prefix premise is [phl predT skip pred0 '= 0/1], i.e. [0 = 0];    *)
(* the contract premise [phl pred0 (call f) predT '= 1] is vacuous.  But *)
(* [ssem (skip ;; Block [::] Do (call f) Return [::]) m] is a [dunit],   *)
(* so the conclusion asserts [1 = 0].                                    *)
(*                                                                      *)
(* This is the one place where the reconciliation trades a proof for     *)
(* fidelity.  The reachable ([None]) row of the table has residual       *)
(* [phl P s wp '= 1], which forces the prefix to be lossless AND to land *)
(* in [wp] almost surely -- that instance is sound, and is what the old  *)
(* [hoare] premise was silently reconstructing.                          *)
(*                                                                      *)
(* NO EASYCRYPT WITNESS -- dead code, exactly as for [ec_call_seq_ge]    *)
(* above.  This is the [(FHeq, Some bd)] arm ([ecPhlCall.ml:350-351]),   *)
(* and [opt_bd] is [None] at both call sites.  The reachable             *)
(* [(FHeq, None)] arm ([:352-353]) has residual [FHeq 1%r] and is sound. *)
Lemma ec_call_seq_eq P Q (Pf Qf : assn) (f : ident)
                     (bs rs : seq (@binding _ cmem)) s d d' :
     phl P s [pred m | Pf (minit m bs)
                       && `[< forall m', Q (mret m m' rs) = Qf m' >]] '= (d / d')
  -> phl Pf (call f) Qf '= d'
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q '= d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.10 / S1.12  proc, and fun-to-code.                                 *)
(* [t_bdhoareF_fun_def_r], ecPhlFun.ml:104 (the bound is substituted too, *)
(* :115); [t_fun_to_code_bdhoare_r], :480.                               *)
(*                                                                      *)
(*   |- phoare[ body(f) : P ==> Q ] <> b                                 *)
(*   ------------------------------------                                *)
(*        |- phoare[ f : P ==> Q ] <> b                                  *)
(*                                                                      *)
(* EasyCrypt substitutes the arguments for the parameters; by (G3) that  *)
(* substitution is the [Block] of S1.9, so the rule proper is just the   *)
(* unfolding of the call.  Both S1.10 and S1.12 collapse to this.        *)
(* Proof: [ssem_call_eq] (psemantic.v:1019).                             *)

Lemma ec_proc P Q (f : ident) r d :
  phl P (ps f) Q r d <-> phl P (call f) Q r d.
Proof. by split=> h m Pm; move: (h m Pm); rewrite ssem_call_eq. Qed.

(* -------------------------------------------------------------------- *)
(* S1.11  proc * (abstract procedures) -- NOT FORMALIZED.                *)
(* [t_bdhoareF_abs_ge_r], ecPhlFun.ml:263 ([bdhoareF_abs_spec] :179-189); *)
(* derived [t_bdhoareF_abs_r], :277; [process_fun_abs], :644.            *)
(* [t_bdhoareF_abs_ge_r] quantifies over the oracle set [O] of an        *)
(* abstract module [f] and checks [PV.check_depend] / [check_oracle_use] *)
(* against [f]'s top-level module state.  There is no module system and  *)
(* no notion of an abstract procedure with an oracle set here, so the    *)
(* rule cannot be stated.                                                *)

(* -------------------------------------------------------------------- *)
(* S1.13  elim* and exists* -- quantifiers in the precondition.          *)
(* [t_hr_exists_elim_r], ecPhlExists.ml:39; [t_hr_exists_intro_r], :49   *)
(* (body :92-107), [t_hr_exists_intro], :111.                            *)
(*                                                                      *)
(*   |- forall x, phoare[ c : P' ==> Q ] <> b                            *)
(*   -----------------------------------------                           *)
(*   |- phoare[ c : exists x, P' ==> Q ] <> b                            *)

Lemma ec_exists_elim {T : Type} (P : T -> assn) Q c r d :
     (forall t : T, phl (P t) c Q r d)
  -> phl [pred m | `[< exists t : T, P t m >]] c Q r d.
Proof. by move=> h m /= /asboolP [t Pt]; apply: (h t). Qed.

(* The converse, EasyCrypt's [exists* f]: the value of [f] is named by a *)
(* fresh existential in the precondition.                                *)

Lemma ec_exists_intro {T : eqType} (f : cmem -> T) P Q c r d :
     phl [pred m | `[< exists t : T, (t == f m) && P m >]] c Q r d
  -> phl P c Q r d.
Proof.
move=> h m Pm; apply: h => /=; apply/asboolP; exists (f m).
by rewrite eqxx Pm.
Qed.

(* -------------------------------------------------------------------- *)
(* S1.14  ecall -- apply a procedure contract given as a lemma.          *)
(* [process_ecall_bdhoare], ecPhlExists.ml:583, via                      *)
(* [t_ecall_bdhoare_bwd], ecPhlCall.ml:518-521.                          *)
(*                                                                      *)
(* Backward direction only, and the contract must be lossless ([= 1]);   *)
(* the goal's own bound must satisfy [1 <> b], which is the [condbd]     *)
(* premise of the underlying seq split.                                  *)
(* Derived, exactly as EasyCrypt derives it: [ec_seq_eq] at the trivial  *)
(* split ([S := predT], [f1 = f2 = 1], [g1 = g2 = 0]) composed with      *)
(* [ec_call_eq] against the contract.                                    *)

Lemma ec_ecall P Q (Pf Qf : assn) (f : ident)
               (bs rs : seq (@binding _ cmem)) s r d :
     r 1 d
  -> phl Pf (call f) Qf '= 1
  -> phl P s [pred m | Pf (minit m bs)
                       && `[< forall m', Qf m' -> Q (mret m m' rs) >]] '= 1
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q r d.
(* Sound at every comparison, because the [= 1] premises pin both the    *)
(* prefix and the callee exactly: the prefix is lossless and establishes *)
(* the [wp] almost surely, and the lossless contract forces              *)
(* [\P_[Block] Q = 1] on the support.  So the whole probability is [1]   *)
(* and the only obligation left on the bound is the catalogue's          *)
(* [condbd], here just [r 1 d].                                          *)
Proof.
move=> hrd hcall hwp m Pm; rewrite ssemE pr_dlet.
set W := [pred m | Pf (minit m bs)
                   && `[< forall m', Qf m' -> Q (mret m m' rs) >]].
have hW : \P_[ssem_ ps s m] W = 1 by apply/eqP; exact: (hwp m Pm).
have hT : \P_[ssem_ ps s m] predT = 1.
+ by apply/le_anti; rewrite le1_pr /= -hW; apply: subset_pr.
have hr : range W (ssem_ ps s m).
+ by apply/pr_range/eqP; rewrite pr_predC hT hW subrr.
have hF : forall m', m' \in dinsupp (ssem_ ps s m) ->
            \P_[ssem_ ps (Block bs Do (call f) Return rs) m'] Q = 1.
+ move=> m' hm'; move: (hr m' hm') => /andP [hPf /asboolP hQ].
  rewrite ssemE aux_pr_dlet_dunit.
  have h1 : \P_[ssem_ ps (call f) (minit m' bs)] Qf = 1.
  - by apply/eqP; exact: (hcall _ hPf).
  apply/le_anti; rewrite le1_pr /= -h1.
  by apply: le_in_pr => x _; rewrite ?inE; exact: hQ.
rewrite -(@eq_exp _ _ _ (fun=> 1)).
+ by move=> m' hm'; apply/esym; exact: (hF m' hm').
by rewrite exp_cst hT mul1r.
Qed.

(* -------------------------------------------------------------------- *)
(* S1.15  case.  Sound -- unlike a *postcondition* split -- because both *)
(* branches keep the same bound and the preconditions are exclusive.     *)
(* [t_bdhoare_case_r], ecPhlCase.ml:34; surface [t_hl_case] :66, :72     *)
(* ([Inv_ts] rejected :81).                                              *)

Lemma ec_case P (Phi : assn) c Q r d :
     phl (P /\ Phi)%A   c Q r d
  -> phl (P /\ ~ Phi)%A c Q r d
  -> phl P c Q r d.
Proof.
move=> hA hNA m Pm; case/boolP: (Phi m) => [Am | NAm].
+ by apply/hA; rewrite -(rwP andP).
+ by apply/hNA; rewrite -(rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
(* S1.16  exfalso -- the [false] precondition axiom.                     *)
(* [t_core_exfalso_r], ecPhlTAuto.ml:43 (ZERO premises); surface         *)
(* [t_exfalso_r], ecPhlAuto.ml:16-25, [t_exfalso], :27.                  *)
(* The core rule has zero premises; the surface tactic also applies when *)
(* the precondition is merely *equivalent* to [false].                   *)
(* Note the catalogue's remark: there is no "phoare[_ ==> true] closes"  *)
(* axiom, because the bound still has to be discharged; [prbounded]      *)
(* (S4.3) plays that role.                                               *)

Lemma ec_exfalso c Q r d : phl pred0 c Q r d.
Proof. by []. Qed.

Lemma ec_exfalso_conseq P c Q r d :
  (forall m, ~~ P m) -> phl P c Q r d.
Proof. by move=> h m; rewrite (negbTE (h m)). Qed.


(* ==================================================================== *)
(* ===                     2. The conseq family                     === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* The two tables the conseq rules are built from, transcribed.          *)

(* S2.1, postcondition premise, oriented by the comparison               *)
(* ([bdHoare_conseq_conds], ecPhlConseq.ml:218-231).  At an upper bound  *)
(* one may only *weaken* the postcondition, at a lower bound only        *)
(* *strengthen* it, and at an exact bound it must be equivalent.         *)
(* Stated pointwise so that S2.3 can quantify it over reachable          *)
(* memories only.                                                        *)
(*                                                                      *)
(* CAUTION -- EasyCrypt's own prose disagrees with its code here.        *)
(* [ecPhlConseq.ml:215-217] documents [bdHoare_conseq_conds] as          *)
(*   FHle: Q => Q'   FHeq: Q <=> Q'   FHge: Q' => Q                      *)
(* which is what the code at [:226-230] builds ([f_imp po new_po] at     *)
(* [:227], i.e. old post implies new post).  But the block comment at    *)
(* [:241-242], sitting directly above [t_bdHoareF_conseq], states the    *)
(* TRANSPOSE:                                                            *)
(*   FHle (<=): Q' => Q   FHeq (=): Q' <=> Q   FHge (>=): Q => Q'        *)
(* [ec_postimpl] follows the code.  (This is the second place where the  *)
(* EasyCrypt prose is wrong; the first is the [mk_event_cond] table of   *)
(* RULES-PHL.md S1.6 -- see the orientation note there.)                 *)

Definition ec_postimpl (r : bd) (Q Q' : assn) (m : cmem) : Prop :=
  match r with
  | Le => Q m -> Q' m
  | Ge => Q' m -> Q m
  | Eq => Q m = Q' m
  end.

(* S2.2, the admissible bound-and-comparison changes ([bd_goal_r],       *)
(* ecPhlConseq.ml:95-106).  [bd_goal_r] is a *partial* function of       *)
(* [(<>, <>')]; the rows it does not define are user errors in           *)
(* EasyCrypt, and [False] here.                                          *)
(*                                                                      *)
(*    goal <>  |  new <>'   |  premise                                   *)
(*    ---------+------------+---------------------                       *)
(*      <=     |  <= or =   |  d' <= d                                   *)
(*      >=     |  >= or =   |  d <= d'                                   *)
(*      =      |  =         |  d' = d                                    *)
(*      =      |  >=        |  d = 1 /\ d' = 1                           *)
(*      =      |  <=        |  d = 0 /\ d' = 0                           *)
(*    otherwise|            |  (error)                                   *)

Definition ec_bd_goal (r r' : bd) (d d' : R) : Prop :=
  match r, r' with
  | Le, Le | Le, Eq => d' <= d
  | Ge, Ge | Ge, Eq => d <= d'
  | Eq, Eq         => d' = d
  | Eq, Ge         => d = 1 /\ d' = 1
  | Eq, Le         => d = 0 /\ d' = 0
  | _ , _          => False
  end.

(* -------------------------------------------------------------------- *)
(* S2.1  Consequence (pre/post).                                         *)
(* [t_bdHoareS_conseq], ecPhlConseq.ml:259 ([t_bdHoareF_conseq] :243);   *)
(* the postcondition-orientation table is :95-106.                       *)
(*                                                                      *)
(* phl.v already proves the three instances -- [phl_conseq_le],          *)
(* [phl_conseq_ge] and [phl_conseq_eq] -- and their orientations match   *)
(* the table above exactly ([phl_conseq_eq] changes the precondition     *)
(* only, which is the [=] row read as an equivalence).  Only the         *)
(* comparison-generic packaging is new.                                  *)

Lemma ec_conseq P P' Q Q' c r d :
     (forall m, P m -> P' m)
  -> (forall m, ec_postimpl r Q Q' m)
  -> phl P' c Q' r d
  -> phl P  c Q  r d.
Proof.
case: r => hP hQ h m Pm; move: (h m (hP m Pm)) => /=.
+ move=> hle; apply: (le_trans _ hle); apply: le_in_pr => x _.
  by rewrite ?inE; exact: hQ.
+ move=> hge; apply: (le_trans hge); apply: le_in_pr => x _.
  by rewrite ?inE; exact: hQ.
+ by move=> /eqP <-; apply/eqP/eq_pr => x; rewrite ?inE; exact: hQ.
Qed.

(* -------------------------------------------------------------------- *)
(* S2.2  Bound and comparison change.  One lemma for the whole table:    *)
(* the seven admissible rows are the seven cases of [ec_bd_goal] that    *)
(* are not [False].                                                      *)
(* [t_bdHoareS_conseq_bd], ecPhlConseq.ml:293 ([t_bdHoareF_conseq_bd]    *)
(* :279); the [bd_goal_r] table is :95-106, [bd_goal] (user error)       *)
(* :108-122; the side conditions are [bdHoare_conseq_conds], :218-231.   *)
(*                                                                      *)
(* This is the workhorse EasyCrypt uses internally to normalise a bound  *)
(* before applying the real rule -- in [skip] (S1.1), [proc *] (S1.11),  *)
(* [hoare] (S3.2), [phoare split] (S3.4-S3.5) and [islossless] (S4.5).   *)
(* By (G1) its premise is a plain condition on reals.                    *)
(*                                                                      *)
(* The [Eq, Ge] and [Eq, Le] rows go through [phl_le1] and [phl_ge0].    *)

Lemma ec_conseq_bd P Q c r r' d d' :
     (forall m, P m -> ec_bd_goal r r' d d')
  -> phl P c Q r' d'
  -> phl P c Q r  d.
Proof.
rewrite /ec_bd_goal; case: r; case: r' => hbd h m Pm.
+ by apply: (le_trans (h m Pm) (hbd m Pm)).
+ by case: (hbd m Pm).
+ by move: (h m Pm) => /= /eqP ->; exact: (hbd m Pm).
+ by case: (hbd m Pm).
+ by apply: (le_trans (hbd m Pm) (h m Pm)).
+ by move: (h m Pm) => /= /eqP ->; exact: (hbd m Pm).
+ move: (hbd m Pm) => [hd hd']; move: (h m Pm) => /= hle.
  rewrite hd; apply/eqP/le_anti/andP; split; last exact: ge0_pr.
  by rewrite -hd'.
+ move: (hbd m Pm) => [hd hd']; move: (h m Pm) => /= hge.
  rewrite hd; apply/eqP/le_anti/andP; split; first exact: le1_pr.
  by rewrite -hd'.
+ by move: (h m Pm) => /= /eqP ->; rewrite (hbd m Pm).
Qed.

(* -------------------------------------------------------------------- *)
(* S2.3  Not-modified variants.                                          *)
(* [t_bdHoareS_notmod], ecPhlConseq.ml:623 ([t_bdHoareF_notmod] :607);   *)
(* derived [t_bdHoareS_conseq_nm], :652.                                 *)
(*                                                                      *)
(* Same as S2.1, but the postcondition premise need only hold on the     *)
(* memories reachable from [m] by running [c] -- those that agree with   *)
(* [m] off [hl.mod c].  See (G5) for the three limits: [nocall c] is     *)
(* required by [hl.mod_spec]; [hl.mod (call n) = pred0], which is why;   *)
(* and [hl.mod]/[hl.eqon] see the local store only, so EasyCrypt's       *)
(* coverage of global assignments is not reproduced.                     *)
(*                                                                      *)
(* Proof: [hl.mod_spec] gives                                            *)
(*   range [pred m' | `[< hl.eqon (predC (hl.mod c)) m m' >]]            *)
(*         (ssem_ ps c m),                                              *)
(* then [le_in_pr] at [<=]/[>=] and [eq_in_pr] at [=].                   *)

Lemma ec_conseq_notmod P Q Q' c r d :
     nocall c
  -> (forall m, P m -> forall m',
        hl.eqon (predC (hl.mod c)) m m' -> ec_postimpl r Q Q' m')
  -> phl P c Q' r d
  -> phl P c Q  r d.
Proof.
move=> hnc himp h m Pm.
have hr : forall x, x \in dinsupp (ssem_ ps c m) ->
                    hl.eqon (predC (hl.mod c)) m x.
+ by move=> x hx; move: (@hl.mod_spec c m ps hnc m (eqxx m) x hx) => /= /asboolP.
move: himp h; case: r => himp h; move: (h m Pm) => /=.
+ move=> hle; apply: (le_trans _ hle); apply: le_in_pr => x hx.
  by rewrite ?inE; exact: (himp m Pm x (hr x hx)).
+ move=> hge; apply: (le_trans hge); apply: le_in_pr => x hx.
  by rewrite ?inE; exact: (himp m Pm x (hr x hx)).
+ move=> /eqP <-; apply/eqP/eq_in_pr => x hx; rewrite ?inE.
  exact: (himp m Pm x (hr x hx)).
Qed.

(* The derived [conseq_nm]: change pre *and* post in the not-modified    *)
(* style ([gen_conseq_nm], ecPhlConseq.ml:633-645).                      *)

Lemma ec_conseq_nm P P' Q Q' c r d :
     nocall c
  -> (forall m, P m -> P' m)
  -> (forall m, P m -> forall m',
        hl.eqon (predC (hl.mod c)) m m' -> ec_postimpl r Q Q' m')
  -> phl P' c Q' r d
  -> phl P  c Q  r d.
Proof.
move=> hnc hP himp h; apply: (ec_conseq_notmod hnc himp) => m Pm.
exact: (h m (hP m Pm)).
Qed.

(* -------------------------------------------------------------------- *)
(* S2.4  Postcondition conjunction split.                                *)
(* [t_bdHoareS_conseq_conj], ecPhlConseq.ml:992                          *)
(* ([t_bdHoareF_conseq_conj] :1013).                                     *)
(*                                                                      *)
(* Splits a conjunct off the postcondition into a *Hoare* side condition *)
(* -- sound because the Hoare part is certain and therefore consumes no  *)
(* probability mass.  Two directions, EasyCrypt's [~add:false] and       *)
(* [~add:true].                                                          *)
(*                                                                      *)
(* Proof: [pr_range] turns the [hoare] premise into                      *)
(* [range Q (ssem_ ps c m)], and then [eq_in_pr] identifies              *)
(* [\P_[.] (Q' /\ Q)] with [\P_[.] Q'].                                  *)

Lemma ec_conseq_conj_rem P Q Q' c r d :
     hoare P c Q
  -> phl P c (Q' /\ Q)%A r d
  -> phl P c Q' r d.
Proof.
move=> hh h m Pm; move: (h m Pm).
have hr : range Q (ssem_ ps c m) by apply/pr_range/eqP; exact: (hh m Pm).
have -> : \P_[ssem_ ps c m] (Q' /\ Q)%A = \P_[ssem_ ps c m] Q'.
+ by apply/eq_in_pr => x hx; rewrite !inE (hr x hx) andbT.
by [].
Qed.

Lemma ec_conseq_conj_add P Q Q' c r d :
     hoare P c Q
  -> phl P c Q' r d
  -> phl P c (Q' /\ Q)%A r d.
Proof.
move=> hh h m Pm; move: (h m Pm).
have hr : range Q (ssem_ ps c m) by apply/pr_range/eqP; exact: (hh m Pm).
have -> : \P_[ssem_ ps c m] (Q' /\ Q)%A = \P_[ssem_ ps c m] Q'.
+ by apply/eq_in_pr => x hx; rewrite !inE (hr x hx) andbT.
by [].
Qed.

(* -------------------------------------------------------------------- *)
(* S2.5  Transitivity via an equivalence.                                *)
(* [t_bdHoareF_conseq_equiv], ecPhlConseq.ml:1233 (4 premises).          *)
(*                                                                      *)
(* Proves a pHL judgement about [c1] from a coupling with [c2] plus a    *)
(* pHL judgement about [c2].  The relational judgement is [prhl_] of     *)
(* prhl/prhl.v; the probability is transported by [prhl.prhl_lepr] at    *)
(* [<=] and [>=] and by [prhl.prhl_eqpr] at [=].                         *)
(*                                                                      *)
(* The catalogue's [cond1] also carries [b1 = b2[&m2]]; that is vacuous  *)
(* by (G1) -- the bound is a constant, and the same [d] is used on both  *)
(* sides.  The catalogue's [cond2] is folded into the coupling's         *)
(* postcondition, which is where [prhl_lepr] needs it.                   *)

Lemma ec_conseq_equiv_le P1 P2 Q1 Q2 (PR : rassn) c1 c2 d :
     (forall m1, P1 m1 -> exists m2, PR (m1, m2) && P2 m2)
  -> prhl.prhl_ ps PR c1 c2 [pred m : rmem | Q1 m.1 ==> Q2 m.2]
  -> phl P2 c2 Q2 '<= d
  -> phl P1 c1 Q1 '<= d.
Proof.
move=> hw hc h m1 P1m; case: (hw m1 P1m) => m2 /andP [hPR hP2].
apply: (le_trans _ (h m2 hP2)).
exact: (prhl.prhl_lepr (P := PR) (m := (m1, m2)) hPR hc).
Qed.

Lemma ec_conseq_equiv_ge P1 P2 Q1 Q2 (PR : rassn) c1 c2 d :
     (forall m1, P1 m1 -> exists m2, PR (m1, m2) && P2 m2)
  -> prhl.prhl_ ps PR c1 c2 [pred m : rmem | Q2 m.2 ==> Q1 m.1]
  -> phl P2 c2 Q2 '>= d
  -> phl P1 c1 Q1 '>= d.
(* [prhl_lepr] always concludes [\P_[c1] E1 <= \P_[c2] E2], so at [>=]   *)
(* the coupling is first flipped with [prhl_swap] and read at the        *)
(* swapped memory [(m2, m1)].                                            *)
Proof.
move=> hw hc h m1 P1m; case: (hw m1 P1m) => m2 /andP [hPR hP2].
apply: (le_trans (h m2 hP2)).
apply: (prhl.prhl_lepr (P := pswap PR) (m := (m2, m1))) => //.
exact: (iffLR (prhl.prhl_swap _ _ _ _) hc).
Qed.

Lemma ec_conseq_equiv_eq P1 P2 Q1 Q2 (PR : rassn) c1 c2 d :
     (forall m1, P1 m1 -> exists m2, PR (m1, m2) && P2 m2)
  -> prhl.prhl_ ps PR c1 c2 [pred m : rmem | Q1 m.1 == Q2 m.2]
  -> phl P2 c2 Q2 '= d
  -> phl P1 c1 Q1 '= d.
Proof.
move=> hw hc h m1 P1m; case: (hw m1 P1m) => m2 /andP [hPR hP2].
have -> : \P_[ssem_ ps c1 m1] Q1 = \P_[ssem_ ps c2 m2] Q2.
+ exact: (prhl.prhl_eqpr (P := PR) (m := (m1, m2)) hPR hc).
exact: (h m2 hP2).
Qed.

(* -------------------------------------------------------------------- *)
(* S2.6  The surface conseq -- the composite the user actually sees:     *)
(* S2.2 to change the bound, then S2.3 in not-modified style.            *)
(* [t_hi_conseq_bdHoareS], ecPhlConseq.ml:1543-1559                      *)
(* ([t_hi_conseq_bdHoareF] :1635-1651); accepted argument shapes         *)
(* :1536-1541 and :1627-1633; [t_hi_trivial] :1301.                      *)
(* [conseq (: P' ==> Q')] with an unchanged bound instantiates           *)
(* [r' := r], [d' := d], where [ec_bd_goal] is reflexivity and the       *)
(* premise vanishes.                                                     *)

Lemma ec_conseq_full P P' Q Q' c r r' d d' :
     nocall c
  -> (forall m, P m -> P' m)
  -> (forall m, P m -> forall m',
        hl.eqon (predC (hl.mod c)) m m' -> ec_postimpl r Q Q' m')
  -> (forall m, P m -> ec_bd_goal r r' d d')
  -> phl P' c Q' r' d'
  -> phl P  c Q  r  d.
Proof.
move=> hnc hP himp hbd h; apply: (ec_conseq_notmod hnc himp).
by apply: (ec_conseq_bd hbd) => m Pm; exact: (h m (hP m Pm)).
Qed.


(* ==================================================================== *)
(* ===                3. Views and bound splitting                  === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* S3.1  hoare -- the [= 0] view, both directions.                       *)
(* [t_hoare_of_bdhoareS_r] / [t_bdhoare_of_hoareS_r], ecPhlCoreView.ml:9, *)
(* :11, :24, :26.                                                        *)
(*                                                                      *)
(*   |- hoare[ c : P ==> ~Q ]            |- phoare[ c : P ==> ~Q ] = 0   *)
(*   ------------------------            ---------------------------    *)
(*   |- phoare[ c : P ==> Q ] = 0        |- hoare[ c : P ==> Q ]         *)
(*                                                                      *)
(* The two logics coincide at bound 0: [phoare[c : P ==> Q] = 0] says    *)
(* that [Q] is almost never established, i.e. [hoare[c : P ==> ~Q]].     *)
(* This is what makes the [hoare] notation of (G4) legitimate; note      *)
(* that [hoare P c (~ Q)] unfolds to [phl P c (~ ~ Q) '= 0], which is    *)
(* [\P_[.] Q = 0] up to [predCK].                                        *)

Lemma ec_view0 P Q c : phl P c Q '= 0 <-> hoare P c (~ Q)%A.
Proof. by split=> h m Pm; move: (h m Pm); rewrite aux_predCK_pr. Qed.

(* The [range] form of the same fact, i.e. the (G4) claim that the       *)
(* [hoare] notation is [hl_ ps] of hl/hl_stmt.v.  Proof: [pr_range]      *)
(* (pwhile/range.v:69).                                                  *)

Lemma ec_hoare_range P Q c :
  hoare P c Q <-> (forall m, P m -> range Q (ssem_ ps c m)).
Proof.
split=> h m Pm.
+ by apply/pr_range/eqP; apply: (h m Pm).
+ by apply/eqP/pr_range; apply: (h m Pm).
Qed.

(* -------------------------------------------------------------------- *)
(* S3.2  hoare -- the surface tactic.  By (G1) the catalogue's           *)
(* [forall &m, P => (0 <> b)] premise is the plain [r 0 d].              *)
(* Instantiating: [<= d] gives [0 <= d]; [>= d] gives [d <= 0];          *)
(* [= d] gives [d = 0].                                                  *)
(* [t_hoare_bd_hoare], ecPhlBdHoare.ml:16; the [= 0] short circuit is    *)
(* :21-22 and :30-31, the general path :24-27 and :33-36.                *)

Lemma ec_hoare_bd P Q c r d :
  r 0 d -> hoare P c (~ Q)%A -> phl P c Q r d.
Proof.
by move=> hr h m Pm; move: (h m Pm); rewrite aux_predCK_pr => /eqP ->.
Qed.

(* -------------------------------------------------------------------- *)
(* S3.3  hoare from pHL at bound 1.                                      *)
(* ecPhlConseq.ml:904, :916 (one premise; statement form exported).      *)
(*                                                                      *)
(*   |- phoare[ c : P ==> Q ] = 1                                        *)
(*   ---------------------------                                         *)
(*     |- hoare[ c : P ==> Q ]                                           *)
(*                                                                      *)
(* Proof: [\P_[mu] Q = 1] and [\P_[mu] Q <= \P_[mu] predT <= 1] force    *)
(* [\P_[mu] predT = 1], whence [\P_[mu] (~ Q) = 0] by [pr_predC].        *)

Lemma ec_hoare_of_ll P Q c : phl P c Q '= 1 -> hoare P c Q.
Proof.
move=> h m Pm; move: (h m Pm) => /= /eqP hQ.
have hT : \P_[ssem_ ps c m] predT = 1.
+ by apply/le_anti; rewrite le1_pr /= -hQ; apply: subset_pr.
by rewrite pr_predC hT hQ subrr.
Qed.

(* -------------------------------------------------------------------- *)
(* S3.4  phoare split on a conjunctive or disjunctive postcondition.     *)
(* [t_bdhoare_split_bop], ecPhlBdHoare.ml:55; surface                    *)
(* [t_bdhoare_split_bop_conseq], :69 ([b3] defaults to [0%r],            *)
(* ecPhlHiBdHoare.ml:38).                                                *)
(*                                                                      *)
(* Inclusion-exclusion: Pr[A /\ B] = Pr[A] + Pr[B] - Pr[A \/ B].  Note   *)
(* the *dual* connective and the *opposite* comparison in the third      *)
(* premise -- this is what the catalogue's transcript of the EasyCrypt   *)
(* output shows:                                                         *)
(*                                                                      *)
(*   for  phoare[ c : true ==> A /\ B ] = 1/4  with                      *)
(*        phoare split (1/2) (1/2) (3/4)  EasyCrypt emits                *)
(*     forall _, 1/2 + 1/2 - 3/4 = 1/4                                   *)
(*     phoare[ c : true ==> A ]      = 1/2                               *)
(*     phoare[ c : true ==> B ]      = 1/2                               *)
(*     phoare[ c : true ==> A \/ B ] = 3/4                               *)
(*                                                                      *)
(* Proof: [pr_and] resp. [pr_or] (counting_distr.v:1729, :1719).         *)
(* Caveat for the proof pass: those are stated with [[predI A & B]] /    *)
(* [[predU A & B]] while [%A] gives [predI A B]; convertible, but        *)
(* [eq_pr] may be needed to line the two up syntactically.               *)

Lemma ec_split_and P (A B : assn) c r d d1 d2 d3 :
     (forall m, P m -> r (d1 + d2 - d3) d)
  -> phl P c A r d1
  -> phl P c B r d2
  -> phl P c (A \/ B)%A (bd_opp r) d3
  -> phl P c (A /\ B)%A r d.
Proof.
move=> hbd hA hB hAB m Pm; rewrite aux_pr_andE.
move: hbd hA hB hAB; case: r => /= hbd hA hB hAB;
  move: (hA m Pm) (hB m Pm) (hAB m Pm) => /= k1 k2 k3.
+ by apply: (le_trans _ (hbd m Pm)); apply: lerB; [apply: lerD | exact: k3].
+ by apply: (le_trans (hbd m Pm)); apply: lerB; [apply: lerD | exact: k3].
+ by move: k1 k2 k3 => /eqP -> /eqP -> /eqP ->; exact: (hbd m Pm).
Qed.

Lemma ec_split_or P (A B : assn) c r d d1 d2 d3 :
     (forall m, P m -> r (d1 + d2 - d3) d)
  -> phl P c A r d1
  -> phl P c B r d2
  -> phl P c (A /\ B)%A (bd_opp r) d3
  -> phl P c (A \/ B)%A r d.
Proof.
move=> hbd hA hB hAB m Pm; rewrite aux_pr_orE.
move: hbd hA hB hAB; case: r => /= hbd hA hB hAB;
  move: (hA m Pm) (hB m Pm) (hAB m Pm) => /= k1 k2 k3.
+ by apply: (le_trans _ (hbd m Pm)); apply: lerB; [apply: lerD | exact: k3].
+ by apply: (le_trans (hbd m Pm)); apply: lerB; [apply: lerD | exact: k3].
+ by move: k1 k2 k3 => /eqP -> /eqP -> /eqP ->; exact: (hbd m Pm).
Qed.

(* -------------------------------------------------------------------- *)
(* S3.5  phoare split ! on a negation.  Pr[Q] = Pr[true] - Pr[~Q].       *)
(* [t_bdhoare_split_not], ecPhlBdHoare.ml:149; surface                   *)
(* [t_bdhoare_split_not_conseq], :158.                                   *)
(*                                                                      *)
(* [\P_[.] predT] is the sub-distribution *weight*, not [1] -- which is  *)
(* exactly why the catalogue's first premise is                          *)
(* [phoare[ c : P ==> true ] <> b1] and not a constant.                  *)
(*                                                                      *)
(* Catalogue transcript: for [phoare[ c : true ==> Q ] <= 1/2] with      *)
(* [phoare split ! 1 (1/2)] EasyCrypt emits                              *)
(*     forall _, true => 1 - 1/2 <= 1/2                                  *)
(*     phoare[ c : true ==> true ] <= 1                                  *)
(*     phoare[ c : true ==> !Q ]   >= 1/2                                *)
(*                                                                      *)
(* Proof: [pr_predC] (counting_distr.v:1741).                            *)

Lemma ec_split_not P Q c r d d1 d2 :
     (forall m, P m -> r (d1 - d2) d)
  -> phl P c predT r d1
  -> phl P c (~ Q)%A (bd_opp r) d2
  -> phl P c Q r d.
Proof.
move=> hbd h1 h2 m Pm.
have hX : \P_[ssem_ ps c m] Q
        = \P_[ssem_ ps c m] predT - \P_[ssem_ ps c m] (~ Q)%A.
+ by rewrite pr_predC subKr.
rewrite hX; move: hbd h1 h2; case: r => /= hbd h1 h2;
  move: (h1 m Pm) (h2 m Pm) => /= k1 k2.
+ by apply: (le_trans _ (hbd m Pm)); apply: lerB.
+ by apply: (le_trans (hbd m Pm)); apply: lerB.
+ by move: k1 k2 => /eqP -> /eqP ->; exact: (hbd m Pm).
Qed.

(* -------------------------------------------------------------------- *)
(* S3.6  phoare split, case form: split the postcondition on an          *)
(* arbitrary [Phi].  Proof: [prID] (counting_distr.v:1654).              *)
(* [BDH_split_or_case], ecPhlHiBdHoare.ml:42-72; entry :13.              *)

Lemma ec_split_case P Q (Phi : assn) c r d d1 d2 :
     (forall m, P m -> r (d1 + d2) d)
  -> phl P c (Phi /\ Q)%A   r d1
  -> phl P c (~ Phi /\ Q)%A r d2
  -> phl P c Q r d.
Proof.
move=> hbd h1 h2 m Pm; rewrite (aux_pr_splitE (ssem_ ps c m) Q Phi).
move: hbd h1 h2; case: r => /= hbd h1 h2;
  move: (h1 m Pm) (h2 m Pm) => /= k1 k2.
+ by apply: (le_trans _ (hbd m Pm)); apply: lerD.
+ by apply: (le_trans (hbd m Pm)); apply: lerD.
+ by move: k1 k2 => /eqP -> /eqP ->; exact: (hbd m Pm).
Qed.

(* -------------------------------------------------------------------- *)
(* S3.7  phoare equiv -- equiv collapses to pHL when the other side is   *)
(* empty.  [t_equivS_conseq_bd], ecPhlConseq.ml:1115.                    *)
(*                                                                      *)
(*   |- phoare[ c : P ==> Q ] = 1                                        *)
(*   -----------------------------------                                 *)
(*   |- equiv[ c ~ [] : P<1> ==> Q<1> ]                                  *)
(*                                                                      *)
(* [skip] plays EasyCrypt's empty statement.  The [= 1] is               *)
(* load-bearing, and is exactly why EasyCrypt demands it: it is what     *)
(* forces [dweight (ssem_ ps c m.1) = 1], without which no coupling      *)
(* against [dunit m.2] exists.                                           *)
(*                                                                      *)
(* Proof: [\P_[mu] Q = 1] gives both [dweight mu = 1] and [range Q mu]   *)
(* (via [pr_predC] then [pr_range]).  Take                               *)
(*   nu := \dlet_(m1 <- mu) dunit (m1, m.2);                             *)
(* [dfst nu = mu] by [dmargin_dlet] + [dmargin_dunit], and               *)
(* [dsnd nu = dunit m.2] by the [-[RHS]mul1r -<weight> -dletC] step of   *)
(* [prhl_rndL] (prhl.v:276-278); the range side by [range_dlet] and      *)
(* [range_dunit].                                                        *)

Lemma ec_phoare_equivL P Q c :
     phl P c Q '= 1
  -> prhl.prhl_ ps [pred m : rmem | P m.1] c skip [pred m : rmem | Q m.1].
Proof.
move=> h m /= Pm.
have hQ : \P_[ssem_ ps c m.1] Q = 1 by apply/eqP; exact: (h m.1 Pm).
have hT : \P_[ssem_ ps c m.1] predT = 1.
+ by apply/le_anti; rewrite le1_pr /= -hQ; apply: subset_pr.
have hrg : range Q (ssem_ ps c m.1).
+ by apply/pr_range/eqP; rewrite pr_predC hT hQ subrr.
exists (\dlet_(m1 <- ssem_ ps c m.1) dunit (m1, m.2)); last first.
+ by apply: (range_dlet hrg) => m1 hQ1; apply: range_dunit.
rewrite ssemE; apply/(prhl.iscoupling_eq _ _ (prhl.iscoupling_prod _)).
+ apply/distr_eqP; rewrite dmargin_dlet -[RHS]dlet_dunit_id.
  by apply/eq_in_dlet => // v _; rewrite dmargin_dunit.
+ move=> x; rewrite dmargin_dlet -[RHS]mul1r -hT -dletC.
  apply/distr_eqP: x; apply/eq_in_dlet => // v _.
  by rewrite dmargin_dunit.
Qed.

Lemma ec_phoare_equivR P Q c :
     phl P c Q '= 1
  -> prhl.prhl_ ps [pred m : rmem | P m.2] skip c [pred m : rmem | Q m.2].
Proof.
move=> h m /= Pm.
have hQ : \P_[ssem_ ps c m.2] Q = 1 by apply/eqP; exact: (h m.2 Pm).
have hT : \P_[ssem_ ps c m.2] predT = 1.
+ by apply/le_anti; rewrite le1_pr /= -hQ; apply: subset_pr.
have hrg : range Q (ssem_ ps c m.2).
+ by apply/pr_range/eqP; rewrite pr_predC hT hQ subrr.
exists (\dlet_(m2 <- ssem_ ps c m.2) dunit (m.1, m2)); last first.
+ by apply: (range_dlet hrg) => m2 hQ2; apply: range_dunit.
rewrite ssemE; apply/(prhl.iscoupling_eq _ _ (prhl.iscoupling_prod _)).
+ move=> x; rewrite dmargin_dlet -[RHS]mul1r -hT -dletC.
  apply/distr_eqP: x; apply/eq_in_dlet => // v _.
  by rewrite dmargin_dunit.
+ apply/distr_eqP; rewrite dmargin_dlet -[RHS]dlet_dunit_id.
  by apply/eq_in_dlet => // v _; rewrite dmargin_dunit.
Qed.


(* ==================================================================== *)
(* ===                    4. Probability bridges                    === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* S4.1 / S4.2  byphoare and bypr.                                       *)
(*                                                                      *)
(* In EasyCrypt these connect the pHL judgement to the [Pr[...]]         *)
(* language of the ambient logic.  Here that language *is* the           *)
(* definition of [phl_]: EasyCrypt's [Pr[ c @ &m : Q ]] is               *)
(* [\P_[ssem_ ps c m] Q].  So [bypr] is the unfolding of [phl_],         *)
(* definitionally true, and recorded only for the correspondence.        *)

Lemma ec_bypr P Q c r d :
  phl P c Q r d <-> (forall m, P m -> r (\P_[ssem_ ps c m] Q) d).
Proof. by []. Qed.

(* [byphoare] additionally relates the probability's event [ev] to the   *)
(* judgement's postcondition [Q].  The comparison is read off the goal   *)
(* shape ([ecPhlDeno.ml:41-56]): [Pr[.] <= b] gives [ev => Q],           *)
(* [b <= Pr[.]] gives [Q => ev], [Pr[.] = b] gives [ev <=> Q] -- which   *)
(* is exactly [ec_postimpl r ev Q].                                      *)

Lemma ec_byphoare P Q (ev : assn) c r d m :
     phl P c Q r d
  -> P m
  -> (forall m', ec_postimpl r ev Q m')
  -> r (\P_[ssem_ ps c m] ev) d.
Proof.
case: r => h Pm himp; move: (h m Pm) => /=.
+ by move=> hle; apply: (le_trans _ hle); apply: le_in_pr => x _;
     rewrite ?inE; exact: himp.
+ by move=> hge; apply: (le_trans hge); apply: le_in_pr => x _;
     rewrite ?inE; exact: himp.
+ by move=> /eqP <-; apply/eqP/eq_pr => x; rewrite ?inE; exact: himp.
Qed.

(* -------------------------------------------------------------------- *)
(* S4.3  prbounded -- closes a pHL goal whose bound is trivially         *)
(* satisfied.  This is the pHL analogue of [t_hoare_true], and the only  *)
(* rule of the catalogue that is *exclusively* pHL.                      *)
(* [t_prbounded_r], ecPhlPr.ml:99; the case list is :114-124.            *)
(*                                                                      *)
(* The first two rows are already phl.v's [phl_le1] and [phl_ge0]:       *)
(*   Lemma phl_le1 P c Q : phl P c Q '<= 1.                              *)
(*   Lemma phl_ge0 P c Q : phl P c Q '>= 0.                              *)
(* Only the third row and the two [conseq] catch-alls are new.           *)

Lemma ec_prbounded_false P c r : phl P c pred0 r 0.
Proof. by move=> m _; rewrite pr_pred0; case: r => /=; rewrite ?lexx ?eqxx. Qed.

Lemma ec_prbounded_le P Q c d : 1 <= d -> phl P c Q '<= d.
Proof. by move=> h m _; apply: (le_trans (le1_pr _ _) h). Qed.

Lemma ec_prbounded_ge P Q c d : d <= 0 -> phl P c Q '>= d.
Proof. by move=> h m _; apply: (le_trans h (ge0_pr _ _)). Qed.

(* -------------------------------------------------------------------- *)
(* S4.4  fel -- the failure-event lemma -- NOT FORMALIZED.               *)
(* [t_failure_event_r], ecPhlFel.ml:117, emission :250.                  *)
(* [t_failure_event_r] is driven by a counter, a query bound, per-oracle *)
(* preconditions over the oracle set of an abstract module, and a        *)
(* [PV.indep] check that the failure event, counter and invariant are    *)
(* modified only inside oracles.  None of oracle sets, per-oracle specs  *)
(* or [PV.indep] exists here (see S1.11), so the rule cannot be stated.  *)
(* Its only pHL premise, [not_F_to_F], is an ordinary pHL judgement.     *)

(* -------------------------------------------------------------------- *)
(* S4.5  islossless.                                                     *)
(* [t_lossless], ecPhlHiAuto.ml:123.                                     *)
(*                                                                      *)
(* [islossless f] is notation for [phoare[ f : true ==> true ] = 1].     *)
(* The tactic itself is a syntax-directed strategy                       *)
(* ([ll_strategy_of_stmt]); what is formalized here is its *content*,    *)
(* one rule per instruction shape.  The [conseq] steps the tactic wraps  *)
(* around them are S2.1 and S2.2.                                        *)

Lemma ec_ll_skip : phl predT skip predT '= 1.
Proof. exact: phl_skip. Qed.

Lemma ec_ll_assgn {T : IhbType.type} (x : vars T) (e : expr T) :
  phl predT (x <<- e) predT '= 1.
Proof. by move=> m _; rewrite !ssemE pr_dunit /= mulr1n. Qed.

Lemma ec_ll_gassgn {T : IhbType.type} (x : vars T) (e : expr T) :
  phl predT (G x <<- e) predT '= 1.
Proof. by move=> m _; rewrite !ssemE pr_dunit /= mulr1n. Qed.

(* The hypothesis is the losslessness of the sampled distribution; it is *)
(* load-bearing (a sub-distribution of weight < 1 loses mass).           *)

Lemma ec_ll_rnd {T : IhbType.type} (x : vars T) (e : dexpr T) :
     (forall m, \P_[`[{e}] m] predT = 1)
  -> phl predT (x <$- e) predT '= 1.
Proof.
move=> h m _; rewrite !ssemE aux_pr_dlet_dunit; apply/eqP.
have -> : \P_[`[{e}] m] [pred v | predT m.[x <- v]] = \P_[`[{e}] m] predT.
+ by apply/eq_pr => v; rewrite !inE.
exact: h.
Qed.

Lemma ec_ll_seq c1 c2 :
     phl predT c1 predT '= 1
  -> phl predT c2 predT '= 1
  -> phl predT (c1 ;; c2) predT '= 1.
Proof.
move=> h1 h2 m _; rewrite !ssemE pr_dlet.
rewrite -(@eq_exp _ _ _ (fun=> 1)).
+ by move=> m' _; apply/esym/eqP; apply: (h2 m').
by rewrite exp_cst mulr1; apply: (h1 m).
Qed.

Lemma ec_ll_if (e : bexpr) c1 c2 :
     phl `[{e}] c1 predT '= 1
  -> phl (~ `[{e}])%A c2 predT '= 1
  -> phl predT (If e then c1 else c2) predT '= 1.
Proof.
move=> h1 h2; apply: phl_if.
+ by move=> m /andP [_ he]; apply: h1.
+ by move=> m /andP [_ he]; apply: h2.
Qed.

Lemma ec_ll_block (bs rs : seq (@binding _ cmem)) c :
     (forall m, phl [pred m0 | m0 == minit m bs] c predT '= 1)
  -> phl predT (Block bs Do c Return rs) predT '= 1.
Proof.
move=> h; apply: ec_block => m _ m0 hm0.
have -> : \P_[ssem_ ps c m0] [pred m' | predT (mret m m' rs)]
        = \P_[ssem_ ps c m0] predT by apply/eq_pr => m'; rewrite !inE.
exact: (h m m0 hm0).
Qed.

Lemma ec_ll_call (f : ident) :
  phl predT (ps f) predT '= 1 -> phl predT (call f) predT '= 1.
Proof. by move=> h m Pm; move: (h m Pm); rewrite ssem_call_eq. Qed.

(* The loop case is [aux_phl_while_ll] (the semantic core of the S1.8(a) *)
(* variant rule) weakened to [Q := predT].                               *)

Lemma ec_ll_while (I : assn) (vrnt : cmem -> int) (e : bexpr) c :
     (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            (I /\ [pred m | vrnt m < z])%A '= 1)
  -> (forall m, I m -> vrnt m <= 0 -> ~~ `[{e}] m)
  -> phl I (While e Do c) predT '= 1.
Proof.
move=> h1 h2 m Im.
move: (@aux_phl_while_ll I vrnt e c h1 h2 m Im) => /= /eqP hq.
by apply/eqP/le_anti; rewrite le1_pr /= -hq; apply: subset_pr.
Qed.

(* -------------------------------------------------------------------- *)
(* S4.6  auto, trivial, exfalso -- NOT RULES.                            *)
(* These are the automation entry points (ecPhlAuto.ml, ecPhlHiAuto.ml); *)
(* none introduces a rule of its                                         *)
(* own, they only try the ones above.  Of the lemmas [t_auto] chains,    *)
(* the two that can close a pHL goal are [t_core_exfalso]                *)
(* (ecPhlTAuto.ml:43; S1.16, [ec_exfalso]) and [t_prbounded]             *)
(* (ecPhlPr.ml:99; S4.3).  A [Hint Resolve ... :                         *)
(* ec_phl] database is deliberately NOT declared while the lemmas of     *)
(* this file are [Admitted]: it would let [eauto] close goals on         *)
(* nothing.  Add it in the proof pass.                                   *)

(* -------------------------------------------------------------------- *)
(* S4.7  rewrite Pr[...] -- NOT FORMALIZED.                              *)
(* The [Pr[...]] entry points live in ecPhlPr.ml:21 ([bypr]) and in     *)
(* ecPhlDeno.ml:37 ([byphoare]); the rewrite is not a pHL rule.         *)
(* An ambient rewriting tactic over [Pr[...]] terms, not an inference    *)
(* rule.  It appears in the catalogue only because one lemma it can      *)
(* instantiate, [pr_mu1_le_eq_mu1], carries a pHL losslessness           *)
(* hypothesis -- i.e. an instance of S4.5.                               *)

(* -------------------------------------------------------------------- *)
(* S4.8  one-sided call from an equiv goal -- NOT FORMALIZED.            *)
(* [t_equiv_call], ecPhlCall.ml:364, and the one-sided arms after it.   *)
(* [t_equiv_call1] is an *equiv* primitive whose callee obligation is a  *)
(* pHL losslessness spec.  Stating it means proving a [prhl_] rule for   *)
(* [Block ... (call f) ...], and prhl.v has no rule for [block] or       *)
(* [call] to build it on -- that is new prhl development, not a pHL      *)
(* rule.  Its pHL side condition is just S4.5.                           *)

(* ==================================================================== *)
(* ===                      5. Code transforms                      === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* Every rule of this group obeys one schema: transform the statement,   *)
(* rewrap the *same* judgement -- pre, post, comparison and bound are    *)
(* carried through untouched.  The schema itself is the following        *)
(* congruence, the analogue of [hl_eq] (hl/hl.v:103); each rule below is *)
(* this lemma applied to an [ssem] equation that pwhile already proves.  *)

Lemma ec_eq P Q c c' r d :
     (forall m, P m -> ssem_ ps c m = ssem_ ps c' m)
  -> phl P c Q r d
  -> phl P c' Q r d.
Proof. exact: aux_phl_eq. Qed.

(* The [Proper] packaging, mirroring [hl_m] (hl/hl.v:111).  The proof    *)
(* pass should re-declare this as a [Global Instance].                   *)

Lemma ec_m :
  Proper (eq ==> eqcmd ps ==> eq ==> eq ==> eq ==> iff) (phl_ ps).
Proof.
move=> ? ? -> c1 c2 heq ? ? -> ? ? -> ? ? ->.
by split=> h m Pm; move: (h m Pm); rewrite heq.
Qed.

(* -------------------------------------------------------------------- *)
(* S5.1  wp.                                                             *)
(* [TacInternal.t_bdhoare_wp], ecPhlWp.ml:221 (the instruction whitelist *)
(* is [wp_instr] / [wp_stmt] in the same file).                          *)
(*                                                                      *)
(*   |- phoare[ s_hd : P ==> wp(s_wp, Q) ] <> b                          *)
(*   ------------------------------------------                          *)
(*     |- phoare[ s_hd; s_wp : P ==> Q ] <> b                            *)
(*                                                                      *)
(* wp is deliberately restricted for pHL: [wp_instr] handles only        *)
(* [Sasgn], [Sif] and [Smatch], and raises [No_wp] on everything else --  *)
(* in particular on [Srnd] and [Scall].  ecPhlWp.mli:10-13 states the    *)
(* reason: "WP only operates over assignments and conditional            *)
(* statements.  Any weakening of this restriction may break the          *)
(* soundness of the bounded hoare logic."                                *)
(*                                                                      *)
(* Stated per instruction, so that no [wp] fixpoint has to be defined.   *)
(* The assignment cases are exact: [ssem (x <<- e) m = dunit m.[x <- e]] *)
(* so [pr_dunit] transports the postcondition verbatim.                  *)

Lemma ec_wp_asgn {T : IhbType.type} P Q (x : vars T) (e : expr T) s r d :
     phl P s [pred m | Q m.[x <- `[{e}] m]] r d
  -> phl P (s ;; (x <<- e)) Q r d.
Proof.
move=> h m Pm; rewrite ssemE.
have -> : \dlet_(m' <- ssem_ ps s m) ssem_ ps (x <<- e) m'
        = \dlet_(m' <- ssem_ ps s m) dunit (m'.[x <- `[{e}] m']).
+ by apply: eq_in_dlet; last by []; move=> m' _; rewrite ssemE.
by rewrite aux_pr_dlet_dunit; apply: h.
Qed.

Lemma ec_wp_gassgn {T : IhbType.type} P Q (x : vars T) (e : expr T) s r d :
     phl P s [pred m | Q (m.{x <- `[{e}] m}) ] r d
  -> phl P (s ;; (G x <<- e)) Q r d.
Proof.
move=> h m Pm; rewrite ssemE.
have -> : \dlet_(m' <- ssem_ ps s m) ssem_ ps (G x <<- e) m'
        = \dlet_(m' <- ssem_ ps s m) dunit (m'.{x <- `[{e}] m'}).
+ by apply: eq_in_dlet; last by []; move=> m' _; rewrite ssemE.
by rewrite aux_pr_dlet_dunit; apply: h.
Qed.

(* The [Sif] case of [wp_instr] is NOT stated: [wp] of a conditional     *)
(* recurses into both branches, so writing it requires either a [wp]     *)
(* fixpoint over the assignment/conditional fragment or a determinism    *)
(* predicate on the branches -- an additional construction either way,   *)
(* which this file's scope rule excludes.  Note that the *operational*   *)
(* content of a leading conditional is already available as [ec_cond]    *)
(* (S1.3), which handles a conditional followed by a tail without any    *)
(* [wp] computation.                                                     *)

(* -------------------------------------------------------------------- *)
(* S5.2  sp -- the dual of wp, pushing the precondition forward.         *)
(* [t_sp_side] [FbdHoareS] arm, ecPhlSp.ml:259-267 ([check_form_indep]). *)
(*                                                                      *)
(* The catalogue's extra side condition [check_form_indep] ("the bound   *)
(* should not be modified by the statement targeted by sp") has no       *)
(* counterpart here and is vacuous by (G1); it exists in EasyCrypt       *)
(* precisely because the bound is a formula over the same memory.        *)

Lemma ec_sp_asgn {T : IhbType.type} P Q (x : vars T) (e : expr T) c r d :
     phl [pred m | `[< exists m0, P m0 /\ m = m0.[x <- `[{e}] m0] >]] c Q r d
  -> phl P ((x <<- e) ;; c) Q r d.
Proof.
move=> h m Pm; rewrite !ssemE dlet_unit.
by apply: h => /=; apply/asboolP; exists m.
Qed.

Lemma ec_sp_gassgn {T : IhbType.type} P Q (x : vars T) (e : expr T) c r d :
     phl [pred m | `[< exists m0, P m0 /\ m = m0.{x <- `[{e}] m0} >]] c Q r d
  -> phl P ((G x <<- e) ;; c) Q r d.
Proof.
move=> h m Pm; rewrite !ssemE dlet_unit.
by apply: h => /=; apply/asboolP; exists m.
Qed.

(* -------------------------------------------------------------------- *)
(* S5.3  inline.                                                         *)
(* [t_inline_bdhoare_r], ecPhlInline.ml:187.                             *)
(*                                                                      *)
(* The call-site case is S1.10 ([ec_proc]).  For the positional form,    *)
(* pwhile already has the syntactic transformation, [inliner]            *)
(* (psemantic.v:1079), which replaces every [call f] by [ps f]; its      *)
(* semantic correctness is the helper [aux_ssem_inliner] above.  No new  *)
(* definition is introduced.                                             *)

Lemma ec_inline P Q c r d :
  phl P (inliner c ps) Q r d -> phl P c Q r d.
Proof. by move=> h m Pm; rewrite -aux_ssem_inliner; apply: h. Qed.

(* -------------------------------------------------------------------- *)
(* S5.4  unroll, splitwhile, simplify if, and the structural rewrites.   *)
(* [EcLowPhlGoal.t_code_transform] [FbdHoareS] arm,                      *)
(* ecLowPhlGoal.ml:816-821; [t_unroll_r], ecPhlLoopTx.ml:183;            *)
(* [t_splitwhile_r], :200; [t_transform_if_r], ecPhlCodeTx.ml:642.       *)
(*                                                                      *)
(* All are [ec_eq] applied to an equation pwhile already proves:         *)
(*   [unroll_while]  (psemantic.v:465)                                   *)
(*   [split_while]   (psemantic.v:515)                                   *)
(*   [if_same]       (psemantic.v:678)                                   *)
(*   [seqA], [seq_skip_l], [seq_skip_r]  (psemantic.v:544-553)           *)

Lemma ec_unroll P Q (e : bexpr) c r d :
     phl P (IfT e then (c ;; While e Do c)) Q r d
  -> phl P (While e Do c) Q r d.
Proof. by move=> h m Pm; rewrite unroll_while_in; apply: h. Qed.

Lemma ec_splitwhile P Q (e1 e2 : bexpr) c r d :
     phl P (While (e1 && e2) Do c ;; While e1 Do c) Q r d
  -> phl P (While e1 Do c) Q r d.
Proof. by move=> h m Pm; rewrite (split_while e1 e2); apply: h. Qed.

Lemma ec_if_same P Q (e : bexpr) c r d :
  phl P c Q r d -> phl P (If e then c else c) Q r d.
Proof. by move=> h m Pm; rewrite if_same; apply: h. Qed.

Lemma ec_seqA P Q c1 c2 c3 r d :
  phl P (c1 ;; c2 ;; c3) Q r d -> phl P (c1 ;; (c2 ;; c3)) Q r d.
Proof. by move=> h m Pm; rewrite seqA; apply: h. Qed.

Lemma ec_skip_l P Q c r d : phl P c Q r d -> phl P (skip ;; c) Q r d.
Proof. by move=> h m Pm; rewrite seq_skip_l; apply: h. Qed.

Lemma ec_skip_r P Q c r d : phl P c Q r d -> phl P (c ;; skip) Q r d.
Proof. by move=> h m Pm; rewrite seq_skip_r; apply: h. Qed.

(* -------------------------------------------------------------------- *)
(* S5.4 (rest)  kill, alias, set, set match, cfold, fission, fusion --   *)
(* NOT FORMALIZED.                                                       *)
(* Same rule as S5.4, ecLowPhlGoal.ml:816-821; entry points [t_kill_r],  *)
(* ecPhlCodeTx.ml:22 (losslessness premise :76), [t_alias_r] :109,       *)
(* [t_set_r] :137, [t_set_match_r] :182, [t_cfold] :418,                 *)
(* [t_fission_r] ecPhlLoopTx.ml:115, [t_fusion_r] :170.                  *)
(* Each needs a *read*-set analysis: [kill] checks that the removed      *)
(* block writes nothing the postcondition or an enclosing block reads,   *)
(* [alias]/[set]/[cfold] need fresh-variable and substitution machinery, *)
(* [fission]/[fusion] need index reasoning on loops.  [hl.mod] gives     *)
(* *written* variables only; there is no [reads], and [hl.eaccess]       *)
(* handles bare variables only and is used nowhere.                      *)
(* Note that [kill] would also emit a pHL losslessness premise           *)
(* [phoare[ ks : true ==> true ] = 1], i.e. an instance of S4.5.         *)

(* -------------------------------------------------------------------- *)
(* S5.5  swap / interleave -- NOT FORMALIZED.                            *)
(* [t_swap_r], ecPhlSwap.ml:100.                                         *)
(* Needs read/write independence between the swapped fragments, hence    *)
(* the same missing [reads] analysis as above.                           *)

(* -------------------------------------------------------------------- *)
(* S5.6  weakmem, proc case, proc rewrite / proc change, change stmt --  *)
(* four rules reached through an explicit [kinds] list, e.g.             *)
(* [t_change_stmt] in ecPhlCodeTx.ml:642; see RULES-PHL.md S5.6 for the  *)
(* per-tactic file:line table.                                           *)
(* NOT FORMALIZED.                                                       *)
(* These act on EasyCrypt's goal representation (memory environments,    *)
(* [kinds] lists, [hl_set_stmt]) rather than on the judgement, and have  *)
(* no counterpart in a semantic formalization.                           *)

(* ==================================================================== *)
(* ===             6. Not applicable to pHL (catalogue S6)          === *)
(* ==================================================================== *)
(*                                                                      *)
(* Catalogue S6 lists the tactics that have no bdHoare arm at all:       *)
(* [upto], [eqobs-in]/[sim], [trans]/[repl], [sym], [rwequiv],           *)
(* [outline], [eager] (equiv or eager only); [rwprgm] (hoare only);      *)
(* [circuit]/[bdep] (circuits, not program logics); [hoare split]        *)
(* (unsound for pHL by design -- its pHL counterpart is S3.4, which      *)
(* pays for the split with inclusion-exclusion); [concave] and           *)
(* [call concave] (ehoare only); [t_hoare_true] / [t_ehoare_zero] (no    *)
(* pHL arm -- S4.3 plays that role); and [rnd f g] ([PTwoRndParams],     *)
(* equiv only).  Nothing to state.                                       *)

End Rules.
End ec_phl.
