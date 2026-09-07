(* -------------------------------------------------------------------- *)
From mathcomp Require Import boot order algebra finmap.
From mathcomp.classical Require Import boolp classical_sets fsbigop.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import counting_distr ereal esum.
From mathcomp.analysis Require Import sequences exp.

From xhl Require Import misc rsum.
From xhl.strassen Require Import elift strassen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

(* ==================================================================== *)
(* Strassen's theorem with deficiency, in *coupling* form.               *)
(*                                                                      *)
(* [strassen.Strassen] delivers an [elift], the Barthe-et-al. pair of    *)
(* witnesses, which looks weaker than a coupling with deficiency.  At    *)
(* [ε = 0] it is not: [elift_bnd] gives a witness pair additionally      *)
(* satisfying                                                           *)
(*                                                                      *)
(*   η.2 (Some a, b) <= η.1 (a, Some b) <= Ω 0 * η.2 (Some a, b)         *)
(*                                                                      *)
(* and [Ω 0 = 1] pinches those two bounds into an equality.  So both     *)
(* witnesses carry the *same* sub-distribution [θ] on [A * A], supported *)
(* on the relation; what is left over on each side is a residual, and    *)
(* because both [D1] and [D2] have weight 1 the two residuals have the   *)
(* *same* mass [r].  [edist] bounds [r] by [delta], and pairing the two  *)
(* residuals off against each other completes [θ] to a genuine coupling  *)
(* that misses the relation with probability at most [r <= delta].       *)
(*                                                                      *)
(* This is the only place where the sensitivity transform is pinned      *)
(* down: [Ω := expR].  Everything in elift.v / strassen.v stays generic. *)
(* ==================================================================== *)
Section Deficiency.
Context {R : realType}.

Local Notation distr T := {distr T%type / R}.
Local Notation Om := (@expR R).

Context {A : choiceType}.
Context (D1 D2 : distr A) (Rl : rel A) (delta : R).

Hypothesis w1 : dweight D1 = 1.
Hypothesis w2 : dweight D2 = 1.
Hypothesis ge0_delta : 0 <= delta.
(* The image is spelled exactly as [strassen.imS] so that no conversion   *)
(* is needed here.                                                        *)
Hypothesis hM : forall M : pred A,
  \P_[D1] M <= \P_[D2] [pred y | `[< exists2 x, x \in M & Rl x y >]] + delta.

Let Sp : pred (A * A)%type := [pred p | Rl p.1 p.2].

(* -------------------------------------------------------------------- *)
(* [Strassen] at [ε := 0], [Ω := expR].                                  *)
Local Lemma mono_Sp X : \P_[D1] X <= Om 0 * \P_[D2] (imS Sp X) + delta.
Proof. by rewrite expR0 mul1r; exact: hM. Qed.

(* [Ω := expR]: the four hypotheses, discharged once and for all. *)
Local Lemma OmD : {morph Om : x y / x + y >-> x * y}.
Proof. exact: expRD. Qed.

Local Lemma Om0 : Om 0 = 1.
Proof. exact: expR0. Qed.

Local Lemma mono_Om : {mono Om : x y / x <= y >-> x <= y}.
Proof. exact: ler_expR. Qed.

Local Lemma gt0_Om : forall x, 0 < Om x.
Proof. exact: expR_gt0. Qed.

Local Lemma hlift : elift Om 0 delta D1 D2 Sp.
Proof. exact: (Strassen OmD Om0 mono_Om gt0_Om (lexx 0) ge0_delta mono_Sp). Qed.

Let eta := elift_bnd Om0 mono_Om gt0_Om (lexx 0) hlift.

Let hL : distr (A * option A)%type := (tag eta).1.
Let hR : distr (option A * A)%type := (tag eta).2.

(* [θ] is the common value of the two witnesses on [Some] x [Some].       *)
Let th (p : A * A) : R := hL (p.1, Some p.2).

Local Lemma thE a b : th (a, b) = hR (Some a, b).
Proof.
apply/eqP; rewrite eq_le /th /=; apply/andP; split.
+ by rewrite -[X in _ <= X]mul1r -expR0; exact: (exlift_leLR eta).
exact: (exlift_leRL eta).
Qed.

Let r1 a : R := hL (a, None).
Let r2 b : R := hR (None, b).

Local Lemma ge0_th p : 0 <= th p.        Proof. exact: ge0_mu. Qed.
Local Lemma ge0_r1 a : 0 <= r1 a.        Proof. exact: ge0_mu. Qed.
Local Lemma ge0_r2 b : 0 <= r2 b.        Proof. exact: ge0_mu. Qed.

(* -------------------------------------------------------------------- *)
(* Both witnesses are full distributions.                                *)
Local Lemma dfst_hL : dfst hL = D1.
Proof. by apply/distr_eqP => a; exact: (exlift_dfstL eta). Qed.

Local Lemma dsnd_hR : dsnd hR = D2.
Proof. by apply/distr_eqP => b; exact: (exlift_dsndR eta). Qed.

Local Lemma w_hL : dweight hL = 1.
Proof. by rewrite -dweight_dfst dfst_hL. Qed.

Local Lemma w_hR : dweight hR = 1.
Proof. by rewrite -dweight_dsnd dsnd_hR. Qed.

(* -------------------------------------------------------------------- *)
(* The two residuals have the same mass: both equal [1 - |θ|].           *)
Local Lemma mass_r1 : rsum (fun b => rsum (fun a => th (a, b))) + rsum r1 = 1.
Proof.
have -> : rsum r1 = dsnd hL None.
+ by rewrite dsndE_rsum; apply: eq_rsum => a.
have e b : rsum (fun a => th (a, b)) = dsnd hL (Some b).
+ by rewrite dsndE_rsum; apply: eq_rsum => a.
rewrite (eq_rsum e) -(rsum_option (summable_mu (dsnd hL))).
by rewrite -dweightE dweight_dsnd w_hL.
Qed.

Local Lemma mass_r2 : rsum (fun a => rsum (fun b => th (a, b))) + rsum r2 = 1.
Proof.
have -> : rsum r2 = dfst hR None.
+ by rewrite dfstE_rsum; apply: eq_rsum => b.
have e a : rsum (fun b => th (a, b)) = dfst hR (Some a).
+ by rewrite dfstE_rsum; apply: eq_rsum => b; rewrite thE.
rewrite (eq_rsum e) -(rsum_option (summable_mu (dfst hR))).
by rewrite -dweightE dweight_dfst w_hR.
Qed.

Local Lemma sum_r12 : rsum r1 = rsum r2.
Proof.
have sth (a : A) : esummable [set: A] (EFin \o (fun b => th (a, b))).
+ by apply: (esummable_option (S := EFin \o (fun y => hL (a, y))));
     exact: (summable_fst hL a).
have sth' (b : A) : esummable [set: A] (EFin \o (fun a => th (a, b))).
+ apply: (le_esummable (g := EFin \o (fun a => hR (Some a, b)))); last first.
  - by apply: (esummable_option (S := EFin \o (fun x => hR (x, b))));
       exact: (summable_snd hR b).
  move=> a _ /=; apply/andP; split; first by rewrite lee_fin ge0_th.
  by rewrite lee_fin thE.
have h1 := mass_r1; rewrite -(rsum_pair_swap ge0_th sth') in h1.
have h2 := mass_r2; rewrite -(rsum_pair ge0_th sth) in h2.
by apply: (addrI (rsum th)); rewrite h1 h2.
Qed.

(* -------------------------------------------------------------------- *)
(* The residual mass is at most [delta]: [deliftL hL] puts mass [r] on   *)
(* the slice [_ x {None}] while [deliftR hR], whose second component is  *)
(* always [Some], puts none there.                                      *)
Let rr := rsum r1.

Local Lemma ge0_rr : 0 <= rr.
Proof. by apply: ge0_rsum => a; exact: ge0_r1. Qed.

Local Lemma r1E : rsum r1 = dsnd hL None.
Proof. by rewrite dsndE_rsum; apply: eq_rsum => a. Qed.

Local Lemma rr_le : rr <= delta.
Proof.
have hrefl := @edist_le R Om gt0_Om _ 0 delta (deliftL hL) (deliftR hR) (lexx 0).
move/hrefl: (exlift_edist eta) => h.
pose Sn : pred (option A * option A)%type := [pred p | p.2 == None].
have e2 : \P_[deliftR hR] Sn = 0.
+ rewrite /deliftR pr_dmargin; apply: eq0_pr => q _.
  by rewrite !inE.
have := h Sn; rewrite e2 mulr0 add0r /deliftL pr_dmargin => hle.
rewrite /rr r1E (pr_pred1 (dsnd hL) None) pr_dmargin.
by apply: (le_trans _ hle); apply: le_in_pr => q _; rewrite !inE.
Qed.

(* -------------------------------------------------------------------- *)
(* The normalised right residual.  When [rr = 0] the convention          *)
(* [0^-1 = 0] makes [nu2] the null distribution, which is harmless: the  *)
(* [None] branch then has no mass ([eq_in_dlet] below).                  *)
Let n2 (b : A) : R := rr^-1 * r2 b.

Local Lemma isd_n2 : isdistr n2.
Proof.
split=> [b|J uJ]; first by rewrite mulr_ge0 // invr_ge0 ge0_rr.
rewrite /n2 -mulr_sumr; case: (eqVneq rr 0) => [->|rn0].
+ by rewrite invr0 mul0r.
have hs : \sum_(j <- J) r2 j <= rr.
+ rewrite /rr sum_r12; apply: gerfinseq_rsum => //.
  exact: (summable_fst hR None).
rewrite -[X in _ <= X](@mulVf _ rr) //.
by rewrite ler_wpM2l // invr_ge0 ge0_rr.
Qed.

Let nu2 : distr A := mkdistr isd_n2.

Local Lemma nu2E b : nu2 b = rr^-1 * r2 b.
Proof. by []. Qed.

Local Lemma w_nu2 : rr != 0 -> dweight nu2 = 1.
Proof.
move=> rn0; rewrite dweightE (eq_rsum nu2E) rsumZ.
+ by move=> b; exact: ge0_r2.
by rewrite -sum_r12 -/rr mulVf.
Qed.

(* -------------------------------------------------------------------- *)
(* The coupling: follow [hL]; where it matched, keep the pair; where it  *)
(* gave up ([None]), draw independently from the normalised residual.    *)
Let kf (q : A * option A) : distr (A * A)%type :=
  if q.2 is Some b then dunit (q.1, b) else dmargin (fun b => (q.1, b)) nu2.

Let kappa : distr (A * A)%type := \dlet_(q <- hL) kf q.

(* On the support of [hL], a [None] second component forces [rr <> 0].  *)
Local Lemma supp_rn0 a : (a, None) \in dinsupp hL -> rr != 0.
Proof.
move=> hq; apply/eqP => r0.
have h0 : hL (a, None) = 0.
+ apply: (rsum_eq0 (f := r1)).
  - by move=> b; exact: ge0_r1.
  - exact: (summable_snd hL None).
  exact: r0.
by move: hq; rewrite in_dinsupp h0 eqxx.
Qed.

(* On the support of [hL], both branches push forward to [dunit q.1] --   *)
(* for the [None] branch because [nu2] then has weight 1 ([supp_rn0]).    *)
Local Lemma dfst_kf q : q \in dinsupp hL -> dmargin fst (kf q) = dunit q.1.
Proof.
case: q => a [b|] hq; rewrite /kf /=.
+ by apply/distr_eqP => z; exact: (dmargin_dunit _ _ _ z).
rewrite dmargin_comp (eq_dmargin (k' := fun=> a)) // dmarginE.
by apply/distr_eqP => y; rewrite dletC (w_nu2 (supp_rn0 hq)) mul1r.
Qed.

Local Lemma dsnd_kf q : dmargin snd (kf q) =
  (if q.2 is Some b then dunit b else nu2).
Proof.
case: q => a [b|]; rewrite /kf /=.
+ by apply/distr_eqP => z; exact: (dmargin_dunit _ _ _ z).
by rewrite dmargin_comp (eq_dmargin (k' := idfun)) // dmargin_id.
Qed.

Local Lemma dfst_kappa : dfst kappa = D1.
Proof.
rewrite -dfst_hL dmarginE; apply/distr_eqP => z.
rewrite /kappa (dmargin_dlet hL fst kf).
apply: eq_in_dlet => // q hq y.
by rewrite (dfst_kf hq).
Qed.

Local Lemma dsnd_kappa : dsnd kappa = D2.
Proof.
have step b' : dsnd kappa b'
             = (\dlet_(y <- dsnd hL) (if y is Some b then dunit b else nu2)) b'.
+ rewrite /kappa (dmargin_dlet hL snd kf)
    (dlet_dmargin hL snd (fun y => if y is Some b then dunit b else nu2)).
  apply: eq_in_dlet; last by [].
  by move=> q _ y; rewrite dsnd_kf.
apply/distr_eqP => b'; rewrite step dletE_rsum.
have sm : esummable [set: option A]
  (EFin \o (fun y => dsnd hL y * (if y is Some b then dunit b else nu2) b')).
+ apply: (le_esummable (g := EFin \o dsnd hL)); last first.
  - exact: (summable_mu (dsnd hL)).
  move=> y _ /=; apply/andP; split; first by rewrite lee_fin mulr_ge0 ?ge0_mu.
  rewrite lee_fin -[X in _ <= X]mulr1 ler_wpM2l ?ge0_mu //.
  by case: y => [b|];
    [exact: (le1_mu1 (dunit b) b') | exact: (le1_mu1 nu2 b')].
rewrite (rsum_option sm) /=.
have -> : rsum (fun b => dsnd hL (Some b) * dunit b b') = dsnd hL (Some b').
+ rewrite (rsum_finseq (r := [:: b'])) //=.
  - by move=> b; rewrite mulr_ge0 ?ge0_mu.
  - move=> b; rewrite dunit1E; case: (eqVneq b b') => [->|_].
    + by rewrite inE eqxx.
    by rewrite mulr0 eqxx.
  by rewrite big_seq1 dunit_id mulr1.
have -> : dsnd hL (Some b') = rsum (fun a => th (a, b')).
+ by rewrite dsndE_rsum; apply: eq_rsum => a.
have hD2 : D2 b' = rsum (fun a => th (a, b')) + r2 b'.
+ rewrite -{1}dsnd_hR dsndE_rsum (rsum_option (summable_snd hR b')).
  by congr (_ + _); apply: eq_rsum => a; rewrite thE.
rewrite hD2; congr (_ + _); rewrite -r1E -/rr mulrA.
case: (eqVneq rr 0) => [r0|rn0]; last by rewrite mulfV // mul1r.
have -> : r2 b' = 0.
+ apply: (rsum_eq0 (f := r2)).
  - by move=> b; exact: ge0_r2.
  - exact: (summable_fst hR None).
  by rewrite -sum_r12; exact: r0.
by rewrite !mulr0.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma pr_kappa_bad : \P_[kappa] [pred p | ~~ Rl p.1 p.2] <= delta.
Proof.
rewrite /kappa pr_dlet espE_rsum.
apply: (le_trans (_ : _ <= rsum (fun q => ((q.2 == None))%:R * hL q))).
+ apply: le_rsum; last first.
  - by apply: esummable_condl; exact: (summable_mu hL).
  (* where [hL] matched, the pair is in the relation, so the integrand   *)
  (* vanishes; where it gave up, bound the probability by 1.             *)
  case=> a [b|]; last first.
  - apply/andP; split; first by rewrite mulr_ge0 ?ge0_pr ?ge0_mu.
    have -> : ((a, None).2 == None)%:R = 1 :> R by [].
    rewrite mul1r -[X in _ <= X]mul1r.
    by apply: ler_wpM2r; [exact: ge0_mu | exact: le1_pr].
  have -> : ((a, Some b).2 == None)%:R = 0 :> R by [].
  rewrite mul0r; apply/andP; split; last first.
  - case/boolP: ((a, Some b) \in dinsupp hL) => [hs|].
    + have hab : Rl a b by exact: (exlift_dsuppL hs).
      have -> : \P_[kf (a, Some b)] [pred p | ~~ Rl p.1 p.2] = 0.
      * by rewrite /kf /= pr_dunit /= hab.
      by rewrite mul0r.
    by rewrite in_dinsupp negbK => /eqP ->; rewrite mulr0.
  by rewrite mulr_ge0 ?ge0_pr ?ge0_mu.
rewrite -prE_rsum; apply: (le_trans _ rr_le).
rewrite /rr r1E (pr_pred1 (dsnd hL) None) pr_dmargin.
by apply: le_in_pr => q _; rewrite !inE.
Qed.

(* -------------------------------------------------------------------- *)
Theorem strassen_coupling :
  exists2 kap : distr (A * A)%type,
    (dfst kap = D1 /\ dsnd kap = D2) &
    \P_[kap] [pred p | ~~ Rl p.1 p.2] <= delta.
Proof.
exists kappa; last exact: pr_kappa_bad.
by split; [exact: dfst_kappa | exact: dsnd_kappa].
Qed.

End Deficiency.
