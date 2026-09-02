From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp           Require finmap.
From xhl                Require Import misc rsum.
From xhl.pwhile         Require Import notations inhabited pwhile psemantic passn range.
From xhl.prhl           Require Import prhl.
From xhl.ehl            Require Import ehl_stmt.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope sem_scope.
Local Open Scope classical_set_scope.

Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Local Notation cmd := (@cmd_ ident cmem ident).

Lemma esumEFinE {T : choiceType} (f : T -> R) :
  esummable [set: T] (EFin \o f) ->
  esum [set: T] (EFin \o f) = (rsum f)%:E.
Proof. by move=> sf; rewrite /rsum fineK// (esummable_esum_fin_num sf). Qed.

Lemma dweightE {T : choiceType} (d : Distr T) : dweight d = rsum d.
Proof. by rewrite prE_rsum; apply: eq_rsum => x /=; rewrite mul1r. Qed.

(* ==================================================================== *)
(* Star-extension of a sub-distribution                                  *)
(*                                                                      *)
(*   d^*(Some a) = d a       d^*(None) = 1 - |d|                        *)
(*                                                                      *)
(* [None] plays the role of the paper's distinguished element [*].       *)
(* ==================================================================== *)
Section DStar.
Context {A : choiceType}.

Implicit Types (d : Distr A).

Definition dstar_fun d (o : option A) : R :=
  if o is Some a then d a else 1 - rsum d.

Lemma ge0_dstar_fun d o : 0 <= dstar_fun d o.
Proof. by case: o => [a|] /=; [exact: ge0_mu | rewrite subr_ge0 le1_rsum]. Qed.

Lemma summable_dstar_fun d : esummable [set: option A] (EFin \o dstar_fun d).
Proof. by apply: esummable_optionT; exact: (summable_mu d). Qed.

Lemma esum_dstar_fun d : esum [set: option A] (EFin \o dstar_fun d) = 1%E.
Proof.
rewrite (esum_option (summable_dstar_fun d)).
have -> : (EFin \o dstar_fun d) \o some = EFin \o d by [].
by rewrite (esumEFinE d (summable_mu d)) /= -EFinD addrC subrK.
Qed.

Lemma le1_dstar_fun d : (esum [set: option A] (EFin \o dstar_fun d) <= 1)%E.
Proof. by rewrite esum_dstar_fun. Qed.

HB.instance Definition _ d :=
  @isDistribution.Build R (option A) (dstar_fun d)
    (ge0_dstar_fun d) (summable_dstar_fun d) (le1_dstar_fun d).

Definition dstar d := @locked (Distr (option A)) (dstar_fun d).

Lemma dstarE d o : dstar d o = dstar_fun d o.
Proof. by unlock dstar. Qed.

Lemma dstar_someE d a : dstar d (Some a) = d a.
Proof. by rewrite dstarE. Qed.

Lemma dstar_noneE d : dstar d None = 1 - dweight d.
Proof. by rewrite dstarE dweightE. Qed.

(* A star-extension is always a full distribution -- this is what lets   *)
(* eRHL relate programs with different termination probabilities.        *)
Lemma dweight_dstar d : dweight (dstar d) = 1.
Proof.
rewrite dweightE /rsum.
have -> : \esum_(o in [set: option A]) ((dstar d) o)%:E
        = esum [set: option A] (EFin \o dstar_fun d).
+ by apply: eq_esum => o _; rewrite dstarE.
by rewrite esum_dstar_fun.
Qed.

(* Lemma 3.4: on full distributions, [dstar] is the identity.            *)
Lemma dstar_full d : dweight d = 1 -> dstar d None = 0.
Proof. by move=> h; rewrite dstar_noneE h subrr. Qed.

End DStar.

Lemma eq_dstar {T : choiceType} {d d' : Distr T} : d =1 d' -> dstar d = dstar d'.
Proof.
move=> e; apply/distr_eqP => -[a|]; rewrite !dstarE /=; first exact: e.
by rewrite (eq_rsum e).
Qed.

(* ==================================================================== *)
(* Star-couplings (Definition 3.3)                                       *)
(*                                                                      *)
(* Contrast with [prhl.iscoupling]: a star-coupling is a *full*          *)
(* distribution on [option A * option B] whose marginals are the         *)
(* star-extensions, so the two programs need not terminate with the      *)
(* same probability.                                                     *)
(* ==================================================================== *)
Section SCoupling.
Context {A B : choiceType}.

Definition scoupling (d1 : Distr A) (d2 : Distr B)
    (nu : Distr (option A * option B)%type) :=
  dfst nu = dstar d1 /\ dsnd nu = dstar d2.

Lemma scoupling_eq (d1 d1' : Distr A) (d2 d2' : Distr B) nu :
  d1 =1 d1' -> d2 =1 d2' -> scoupling d1 d2 nu -> scoupling d1' d2' nu.
Proof.
by move=> e1 e2 [h1 h2]; split; [rewrite h1 (eq_dstar e1) | rewrite h2 (eq_dstar e2)].
Qed.

(* Every pair of sub-distributions admits a star-coupling: the product   *)
(* of the two star-extensions.  Used for Lemma 4.6 and to show that      *)
(* validity is never vacuous.                                           *)
Definition dprod {T U : choiceType} (m1 : Distr T) (m2 : Distr U) :=
  \dlet_(x <- m1) (\dlet_(y <- m2) dunit (x, y)).

Lemma dfst_dprod {T U : choiceType} (m1 : Distr T) (m2 : Distr U) :
  dweight m2 = 1 -> dfst (dprod m1 m2) = m1.
Proof.
move=> w2.
have inner : forall y : T, dmargin fst (\dlet_(t <- m2) dunit (y, t)) = dunit y.
+ move=> y; rewrite dmargin_dlet.
  have -> : \dlet_(t <- m2) dmargin fst (dunit (y, t)) = \dlet_(_ <- m2) dunit y.
  - by apply: eq_in_dlet => // t _; rewrite dmargin_dunit.
  by apply/distr_eqP => z; rewrite dletC w2 mul1r.
rewrite /dprod dmargin_dlet.
have -> : \dlet_(y <- m1) dmargin fst (\dlet_(t <- m2) dunit (y, t))
        = \dlet_(y <- m1) dunit y.
+ by apply: eq_in_dlet => // y _; exact: inner.
by rewrite dlet_dunit_id.
Qed.

Lemma dsnd_dprod {T U : choiceType} (m1 : Distr T) (m2 : Distr U) :
  dweight m1 = 1 -> dsnd (dprod m1 m2) = m2.
Proof.
move=> w1.
have inner : forall y : T, dmargin snd (\dlet_(t <- m2) dunit (y, t)) = m2.
+ move=> y; rewrite dmargin_dlet.
  have -> : \dlet_(t <- m2) dmargin snd (dunit (y, t)) = \dlet_(t <- m2) dunit t.
  - by apply: eq_in_dlet => // t _; rewrite dmargin_dunit.
  by rewrite dlet_dunit_id.
rewrite /dprod dmargin_dlet.
have -> : \dlet_(y <- m1) dmargin snd (\dlet_(t <- m2) dunit (y, t))
        = \dlet_(_ <- m1) m2.
+ by apply: eq_in_dlet => // y _; exact: inner.
by apply/distr_eqP => y; rewrite dletC w1 mul1r.
Qed.

Lemma scoupling_prod (d1 : Distr A) (d2 : Distr B) :
  scoupling d1 d2 (dprod (dstar d1) (dstar d2)).
Proof.
by split; [apply: dfst_dprod | apply: dsnd_dprod]; exact: dweight_dstar.
Qed.

Lemma exists_scoupling (d1 : Distr A) (d2 : Distr B) :
  exists nu, scoupling d1 d2 nu.
Proof. by exists (dprod (dstar d1) (dstar d2)); exact: scoupling_prod. Qed.

End SCoupling.

(* ==================================================================== *)
(* Relational pre- and post-expectations                                 *)
(* ==================================================================== *)
Section RCond.

(* Assertions are quantitative: [rmem = cmem * cmem -> \bar R].  The     *)
(* paper's [E<1>] / [E<2>] are pwhile's [e#'1] / [e#'2].                 *)
Definition rcond  := rmem -> \bar pwhile.R.

(* The "generic" post-expectation also reads the *initial* pair of       *)
(* memories.  This replaces the paper's type [Z] of logical variables    *)
(* (cf. [hl_stmt.assn2] and [ehl_stmt.cond2]).                          *)
Definition rcond2 := rmem -> rmem -> \bar pwhile.R.

(* [psi*]: the 0-extension of a post-expectation to starred memories.    *)
Definition rstar (g : rcond) (p : option cmem * option cmem) : \bar pwhile.R :=
  if p is (Some m1, Some m2) then g (m1, m2) else 0%E.

Lemma ge0_rstar g p : (forall m, (0 <= g m)%E) -> (0 <= rstar g p)%E.
Proof. by move=> h; rewrite /rstar; case: p => -[m1|] [m2|] //=; exact: h. Qed.

Lemma rstar_eq g g' : g =1 g' -> rstar g =1 rstar g'.
Proof. by move=> h; rewrite /rstar => -[[m1|] [m2|]] //=; rewrite h. Qed.

(* Symmetric assertion: [chi~ z (m1, m2) = chi z (m2, m1)]. *)
Definition rswap (f : rcond) : rcond := fun m => f (m.2, m.1).
Definition rswap2 (g : rcond2) : rcond2 :=
  fun m0 m => g (m0.2, m0.1) (m.2, m.1).

Lemma rswapK f : rswap (rswap f) =1 f.
Proof. by move=> [m1 m2]. Qed.

Lemma rswap2K g : forall m0 m, rswap2 (rswap2 g) m0 m = g m0 m.
Proof. by move=> [??] [??]. Qed.

(* Guard operator [P | phi] of the paper, at the relational type.        *)
Notation rlift := (@ehl_stmt.lift rident rmem).

(* Image of a set of memories under a relation, the paper's [R(M)].      *)
Definition rimage (Rl : rel cmem) (M : pred cmem) : pred cmem :=
  [pred m2 | `[< exists m1, M m1 && Rl m1 m2 >]].

End RCond.

Notation rlift := (@ehl_stmt.lift rident rmem).

(* ==================================================================== *)
(* Validity                                                              *)
(* ==================================================================== *)
Section Validity.

Definition psi := ident -> (@cmd_ ident cmem ident).

Implicit Types (f g : rcond) (c d : cmd) (ps : psi).

(* Definition 4.1: validity witnessed by a star-coupling. *)
Definition erhl_ ps f c d g :=
  forall m : rmem, exists2 nu,
      scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
    & (espe nu (rstar g) <= f m)%E.

(* Generic (Z-free) judgment: the post may read the initial memories. *)
Definition kerhl_ ps f c d (g : rcond2) :=
  forall m : rmem, exists2 nu,
      scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
    & (espe nu (rstar (g m)) <= f m)%E.

(* Lemma 4.2: the same, phrased with the infimum [psi#]. *)
Definition scouplings (d1 d2 : Distr cmem) :
    set (Distr (option cmem * option cmem)%type) :=
  [set nu | scoupling d1 d2 nu].

Definition psharp g (d1 d2 : Distr cmem) : \bar pwhile.R :=
  ereal_inf [set espe nu (rstar g) | nu in scouplings d1 d2].

Definition ierhl_ ps f c d g :=
  forall m : rmem, (psharp g (ssem_ ps c m.1) (ssem_ ps d m.2) <= f m)%E.

(* -------------------------------------------------------------------- *)
Lemma erhl_kerhl ps f c d g : kerhl_ ps f c d (fun _ => g) <-> erhl_ ps f c d g.
Proof. by split=> h m; case: (h m) => nu ??; exists nu. Qed.

Lemma kerhl_erhl ps f c d (g : rcond2) :
  kerhl_ ps f c d g <-> (forall s0, erhl_ ps (bound f s0) c d (g s0)).
Proof.
rewrite /bound; split.
+ move=> h s0 m; case: (h m) => nu hnu hle; exists nu => //.
  by case: ifP => [/eqP <-|_]; [exact: hle | exact: leey].
+ move=> h m; case: (h m m) => nu hnu; rewrite eqxx => hle.
  by exists nu.
Qed.

(* Lemma 4.2.                                                            *)
(*                                                                       *)
(* [->] is immediate: [psharp] is by definition a lower bound of the set  *)
(* it is the infimum of, so [ereal_inf_lbound] (analysis/ereal.v) and     *)
(* transitivity suffice.  Beware the renamings in this version of         *)
(* mathcomp-analysis: [ereal_inf_lb] is now [ereal_inf_lbound],           *)
(* [lb_ereal_inf] is [le_ereal_inf_tmp] (its alias is commented out), and *)
(* [ereal_inf_le] is [ge_ereal_inf].                                      *)
(*                                                                       *)
(* [<-] is a different matter: it *is* the statement that the infimum is  *)
(* attained, i.e. an optimal-transport existence theorem.  Compare        *)
(* [ereal_inf_leP] (analysis/ereal.v), which takes [S (ereal_inf S)] as   *)
(* an explicit hypothesis -- the library too treats attainment as the     *)
(* missing input.  Contrary to what an earlier version of this comment    *)
(* claimed, strassen/strassen.v cannot simply be invoked here.  Four      *)
(* independent obstacles:                                                 *)
(*                                                                       *)
(* (1) The [R] parameter.  strassen/elift.v declares its own              *)
(*     [Parameter R : realType], which strassen.v inherits, and pwhile.v  *)
(*     declares a second one.  No file under strassen/ requires           *)
(*     xhl.pwhile, and a [Parameter] cannot be instantiated after the     *)
(*     fact, so every strassen result is about a *different* [{distr _ /  *)
(*     _}].  Reuse means first making elift.v/strassen.v R-polymorphic,   *)
(*     i.e. [Context {R : realType}] in place of the [Parameter].         *)
(*                                                                       *)
(* (2) Countability.  [strcvg] / [strcvg2] (strassen.v) -- the Cantor     *)
(*     diagonal extraction of a pointwise-convergent subsequence, which   *)
(*     is the compactness one would want -- require a [countType].        *)
(*     [cmem] is not one and cannot be: [coremem] is                      *)
(*     [forall T : IhbType.type, ident -> T] (pwhile.v), a dependent      *)
(*     function type, and it carries only [gen_choiceMixin].  The way     *)
(*     round is to work inside [dinsupp (dstar d1) * dinsupp (dstar d2)], *)
(*     in which every competitor is supported; but "summable => countable *)
(*     support" is not available in mathcomp-analysis either.             *)
(*                                                                       *)
(* (3) No Fatou / lower semicontinuity for [esum].  [esum_dlim_r]         *)
(*     (analysis/probability_theory/counting_distr.v) has exactly the     *)
(*     right shape -- [espe (dlim f) E <= r] out of                       *)
(*     [forall n, espe (f n) E <= r] -- but is gated on [nd f], and a     *)
(*     minimising sequence is not monotone.  [prhl.iscoupling_dlim] is    *)
(*     restricted the same way ([nu n <=1 nu m]), so passing the          *)
(*     marginals to a merely convergent limit needs dominated             *)
(*     convergence; cf. the [DCT_swap] argument in strassen.v.            *)
(*                                                                       *)
(* (4) strassen.v is not axiom-free anyway: it assumes [Axiom DCT].       *)
(*                                                                       *)
(* Positivity.  As stated, this lemma puts no sign condition on [g].      *)
(* But [esum] is a signed Jordan-decomposition difference                 *)
(* (analysis/esum.v) and every lemma the [<-] direction needs             *)
(* ([ge0_esum], [esum_ge], [esum_dlim_r], [eexp_dlet]) assumes [0 <= f].  *)
(* So the statement will very likely have to gain                         *)
(* [forall m, (0 <= g m)%E], together with a matching side condition on   *)
(* [H_Consequence] / [H_adapt] in erhl.v -- the way ehl.v carries         *)
(* [forall m, 0 <= g m] on [H_Seq] / [H_While] / [H_Block].               *)
(*                                                                       *)
(* Escape hatch.  [<-] is only ever used to prove soundness of            *)
(* [H_Consequence] / [H_adapt], the sole clients of [psharp].  Restating  *)
(* those two rules with the *existential* side condition that ehl.v's     *)
(* [H_adapt] already uses removes the need for [<-] entirely, leaving     *)
(* only the easy, provable [->] direction.                                *)
Lemma erhl_ierhl ps f c d g : erhl_ ps f c d g <-> ierhl_ ps f c d g.
Proof. Admitted.

End Validity.

(* ==================================================================== *)
(* Relational procedure contracts                                        *)
(*                                                                      *)
(* A contract relates a *pair* of procedures; one-sided calls relate a   *)
(* procedure to [skip].  Indexing by [option ident] covers both, with    *)
(* [None] standing for [skip].                                          *)
(* ==================================================================== *)
Section RContract.

Definition ocmd (o : option ident) : cmd :=
  if o is Some f then call f else skip.

Definition obody (ps : psi) (o : option ident) : cmd :=
  if o is Some f then ps f else skip.

Definition rclause : Type := rcond * rcond2.

Definition get_pre (an : rclause) := let: (pre, _) := an in pre.
Definition get_post (an : rclause) := let: (_, post) := an in post.

Definition rphi : Type := option ident -> option ident -> rclause.

(** Empty procedure contract **)

Definition empty_rprecondition  : rcond  := (fun _ => +oo)%E.
Definition empty_rpostcondition : rcond2 := (fun _ _ => 0)%E.

Definition empty_rclause : rclause :=
  (empty_rprecondition, empty_rpostcondition).

Definition rcl_empty : rphi := fun _ _ => empty_rclause.

(** Well-formedness of contracts.  Note that [ehl_stmt]'s [post_mono]    *)
(*  and [cond2_independent] are not needed here: [rcond2] carries no     *)
(*  distribution argument, so independence holds by construction.        *)

Definition rcl_pre_pos (cl : rphi) :=
  forall o1 o2 m, (0 <= get_pre (cl o1 o2) m)%E.

Definition rcl_post_pos (cl : rphi) :=
  forall o1 o2 m0 m, (0 <= get_post (cl o1 o2) m0 m)%E.

End RContract.

HB.mixin Record isRPhi (cl : rphi) := {
  rpre_pos  : rcl_pre_pos  cl;
  rpost_pos : rcl_post_pos cl;
}.

HB.structure Definition RPhi := {f of isRPhi f}.

Lemma rpre_pos_rcl_empty : rcl_pre_pos rcl_empty.
Proof. by move=> ???; exact: leey. Qed.

Lemma rpost_pos_rcl_empty : rcl_post_pos rcl_empty.
Proof. by []. Qed.

HB.instance Definition _ :=
  isRPhi.Build rcl_empty rpre_pos_rcl_empty rpost_pos_rcl_empty.
