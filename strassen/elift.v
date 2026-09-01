(* -------------------------------------------------------------------- *)
From mathcomp Require Import boot order algebra finmap.
From mathcomp.classical Require Import boolp classical_sets fsbigop.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import counting_distr ereal esum.

Require Import xbigops misc rsum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation simpm := Monoid.simpm.

(* ==================================================================== *)
Parameter (R : realType).

Local Notation distr T := {distr T%type / R}.

(* ==================================================================== *)
Section SensitivityTx.
Context {R : realType}.

Parameter Ω : R -> R.

Axiom ΩD     : {morph Ω : x y / x + y >-> x * y}.
Axiom Ω0     : Ω 0 = 1.
Axiom mono_Ω : {mono Ω : x y / x <= y >-> x <= y}.
Axiom gt0_Ω  : forall x, 0 < Ω x.

Lemma ltr_Ω : {mono Ω : x y / x < y >-> x < y}.
Proof. by apply/leW_mono/mono_Ω. Qed.

Lemma Ω_ge1 x : (1 <= Ω x) = (0 <= x).
Proof. by rewrite -Ω0 mono_Ω. Qed.

Lemma ge0_Ω x : 0 <= Ω x.
Proof. by apply/ltW/gt0_Ω. Qed.
End SensitivityTx.

(* ==================================================================== *)
Definition edist_set {A : choiceType} (ε : R) (μ1 μ2 : distr A) :=
  [set x | exists S, x = \P_[μ1] S - (Ω ε) * \P_[μ2] S].

Definition edist {A : choiceType} (ε : R) (μ1 μ2 : distr A) : R :=
  if ε < 0 then 0 else sup (edist_set ε μ1 μ2).

(* ==================================================================== *)
Section EDistTheory.
Context {A : choiceType}.

Implicit Types (ε δ : R).

(* -------------------------------------------------------------------- *)
Lemma edistE ε (μ1 μ2 : distr A) :
  0 <= ε -> edist ε μ1 μ2 = sup (edist_set ε μ1 μ2).
Proof. by rewrite /edist ltNge => ->. Qed.

(* -------------------------------------------------------------------- *)
Local Lemma z_in_edistp ε (μ1 μ2 : distr A) :
  0 \in edist_set ε μ1 μ2.
Proof. by rewrite in_setE; exists pred0; rewrite !pr_pred0 mulr0 subr0. Qed.

(* -------------------------------------------------------------------- *)
Lemma has_sup_edistp ε (μ1 μ2 : distr A) :
  has_sup (edist_set ε μ1 μ2).
Proof.
split; first by exists 0; rewrite -in_setE; apply: z_in_edistp ε μ1 μ2.
exists 1; apply/ubP=> y [a ->]; rewrite ler_wnDr ?le1_pr //.
by rewrite oppr_le0 mulr_ge0 // (ge0_pr, ge0_Ω).
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_xx ε (μ : distr A) : edist ε μ μ = 0.
Proof.
rewrite /edist; case: ltrP => // ge0_e.
apply/max_sup=> /=; split; first by rewrite -in_setE; apply/z_in_edistp.
apply/ubP=> y [a ->]; rewrite subr_le0 ler_peMl //.
  by apply/ge0_pr. by rewrite Ω_ge1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ge0_edist ε (μ1 μ2 : distr A) : 0 <= edist ε μ1 μ2.
Proof.
rewrite /edist; case: ltrP => //ge0_e; apply/sup_upper_bound.
  by apply/has_sup_edistp. by rewrite -in_setE; apply/z_in_edistp.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ler_edist ε ε' (μ1 μ2 : distr A) :
  0 <= ε' <= ε -> edist ε μ1 μ2 <= edist ε' μ1 μ2.
Proof.
case/andP=> ge0_e' le_e; rewrite /edist !ltNge.
rewrite ge0_e' (le_trans ge0_e' le_e) /=; apply/sup_le; first last.
- by apply/has_sup_edistp.
- by exists 0; rewrite -in_setE; apply/z_in_edistp.
move=> x [S xE]; rewrite xE; apply/downP.
exists (\P_[μ1] S - Ω ε' * \P_[μ2] S); first by exists S.
by rewrite lerD // lerN2 ler_wpM2r ?ge0_pr // mono_Ω.
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_le ε δ (μ1 μ2 : distr A) : 0 <= ε ->
  reflect
    (forall S, \P_[μ1] S <= Ω ε * \P_[μ2] S + δ)
    (edist ε μ1 μ2 <= δ).
Proof.
move=> ge0_e; rewrite edistE //; apply: (iffP idP).
  move=> sle S; rewrite -lerBlDl (le_trans _ sle) //.
  apply/sup_upper_bound; first by apply/has_sup_edistp.
  by exists S.
move=> led; rewrite ge_sup //.
  by case: (has_sup_edistp ε μ1 μ2).
by apply/ubP=> x [S ->]; rewrite lerBlDr addrC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_le_supp ε δ (μ1 μ2 : distr A) : 0 <= ε ->
    (forall S, {subset S <= [predU dinsupp μ1 & dinsupp μ2]} ->
      \P_[μ1] S <= Ω ε * \P_[μ2] S + δ)
  -> (edist ε μ1 μ2 <= δ).
Proof.
move=> ge0_e; set P := [predU dinsupp μ1 & dinsupp μ2] => h.
apply/edist_le=> // S; rewrite (prID _ P μ1) (prID _ P μ2).
rewrite mulrDr addrAC lerD //; first by apply/h=> x /andP[].
by rewrite !eq0_pr ?mulr0 // => x {}h; rewrite !inE h ?orbT andbF.
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_le_pp ε δ (μ1 μ2 : distr A) : 0 <= ε -> 0 <= δ ->
  reflect
    (exists2 di,
        (esummable [set: A] (EFin \o di)
         /\ (\esum_(x in [set: A]) (di x)%:E <= δ%:E)%E) &
       [/\ forall x, 0 <= di x & forall x, μ1 x <= Ω ε * μ2 x + di x])
    (edist ε μ1 μ2 <= δ).
Proof.
move=> ge0_e ge0_d; apply: (iffP idP) => [led|].
* pose di x := \P_[μ1] (pred1 x) - Ω ε * \P_[μ2] (pred1 x).
  have h S: uniq S -> \sum_(i <- S) Num.max 0 (di i) <= δ.
    move=> uqS; pose S' := [seq x <- S | 0 < di x].
    rewrite (bigID [pred x | 0 < di x]) /= addrC big1 ?add0r.
      by move=> x lt0_dix; rewrite max_l 1?leNgt.
    rewrite (eq_bigr di) => [x gt0_dix|].
      by rewrite max_r 1?ltW.
    rewrite -big_filter -/S'; apply/(le_trans _ led).
    rewrite edistE //; apply/sup_upper_bound.
      by apply/has_sup_edistp.
    exists (ssrbool.mem S'); rewrite !pr_mem ?filter_uniq //.
    rewrite mulr_sumr -sumrB; apply/eq_bigr.
    by move=> i _; rewrite !pr_pred1.
  pose dd x := Num.max 0 (di x).
  have ge0_dd x : 0 <= dd x by rewrite /dd le_max lexx.
  (* the finite-subsum bound [h] is exactly the [ereal_sup] bound *)
  have key : (\esum_(x in [set: A]) (dd x)%:E <= δ%:E)%E.
    rewrite ge0_esum; first by move=> x _; rewrite lee_fin.
    apply: ge_ereal_sup => _ [B [finB _] <-].
    rewrite fsbig_finite; first exact: finB.
    by rewrite sumEFin lee_fin; apply/h/fset_uniq.
  exists dd; last first.
  + split=> x; first exact: ge0_dd.
    by rewrite -lerBlDl /dd le_max /di !pr_pred1 lexx orbT.
  split=> //; rewrite esummableE.
  rewrite (eq_esum _ _ (fun x => (dd x)%:E)).
  + by move=> x _ /=; rewrite (ger0_norm (ge0_dd x)).
  rewrite ge0_fin_numE; first by apply: esum_ge0 => x _; rewrite lee_fin.
  by apply: (le_lt_trans key); rewrite ltry.
case=> di [sm_di led] [ge0_di lemu]; apply/edist_le => // S.
rewrite -lee_fin EFinD EFinM !prE.
rewrite -esumZ; first by move=> t _; rewrite lee_fin mulr_ge0 ?ler0n.
apply: (@le_trans _ _ (\esum_(t in [set: A])
   ((Ω ε)%:E * ((S t)%:R * μ2 t)%:E + ((S t)%:R * di t)%:E))%E).
+ apply: le_esum => t _; rewrite -EFinM -EFinD lee_fin mulrCA -mulrDr.
  by apply: ler_wpM2l; [exact: ler0n | exact: lemu].
rewrite esumD.
+ by move=> t _; rewrite mule_ge0 ?lee_fin ?ge0_Ω // mulr_ge0 ?ler0n.
+ by move=> t _; rewrite lee_fin mulr_ge0 ?ler0n.
apply: leeD2l; apply: (le_trans _ led).
apply: le_esum => t _; rewrite lee_fin.
by case: (S t); rewrite /= ?mul1r ?mul0r ?ge0_di.
Qed.
End EDistTheory.

(* -------------------------------------------------------------------- *)
Notation opred P := [pred x | P (Some x)].

(* -------------------------------------------------------------------- *)
Section ELift.
Context {A B : choiceType} (ε δ : R).
Context (μ1 : distr A) (μ2 : distr B) (P : pred (A * B)).

Definition deliftL (μ : distr (A * option B)) :=
  dmargin (fun xy => (Some xy.1, xy.2)) μ.

Definition deliftR (μ : distr (option A * B)) :=
  dmargin (fun xy => (xy.1, Some xy.2)) μ.

Lemma deliftLE (μ : distr (A * option B)) a b :
  deliftL μ (a, b) = if a is Some a then μ (a, b) else 0.
Proof.                  (* FIXME: general lemma when f is injective *)
rewrite dmargin_psumE; case: a => /= [a|]; last first.
+ rewrite (eq_esum _ _ (fun _ => 0%E)); first by move=> x _ /=; rewrite mul0r.
  by rewrite esum0.
rewrite (eq_esum _ _ (fun x => if (a, b) == x then (μ x)%:E else 0%E)).
+ move=> [x1 x2] _; rewrite !xpair_eqE /=.
  rewrite [a == x1]eq_sym [b == x2]eq_sym.
  by case: ((x1 == a) && (x2 == b)); rewrite ?mul1r ?mul0r.
by rewrite esum_if_eq_op_set1.
Qed.

Lemma deliftRE (μ : distr (option A * B)) a b :
  deliftR μ (a, b) = if b is Some b then μ (a, b) else 0.
Proof.
rewrite dmargin_psumE; case: b => /= [b|]; last first.
+ rewrite (eq_esum _ _ (fun _ => 0%E)).
  * by move=> [x1 x2] _; rewrite xpair_eqE /= andbF mul0r.
  by rewrite esum0.
rewrite (eq_esum _ _ (fun x => if (a, b) == x then (μ x)%:E else 0%E)).
+ move=> [x1 x2] _; rewrite !xpair_eqE /=.
  rewrite [a == x1]eq_sym [b == x2]eq_sym.
  by case: ((x1 == a) && (x2 == b)); rewrite ?mul1r ?mul0r.
by rewrite esum_if_eq_op_set1.
Qed.

Local Notation elift_r μ :=
 [/\ dfst μ.1 =1 μ1, dsnd μ.2 =1 μ2
   , (forall a b, (a, Some b) \in dinsupp μ.1 -> P (a, b))
   , (forall a b, (Some a, b) \in dinsupp μ.2 -> P (a, b))
   & edist ε (deliftL μ.1) (deliftR μ.2) <= δ].

Local Notation T :=
  (distr (A * option B) * distr (option A * B))%type.

Definition elift := { μ : T | elift_r μ }.

Hypothesis η : elift.

Lemma elift_dfstL : dfst (tag η).1 =1 μ1.
Proof. by case: (tagged η). Qed.

Lemma elift_dsndR : dsnd (tag η).2 =1 μ2.
Proof. by case: (tagged η). Qed.

Lemma elift_dsuppL :
  forall a b, (a, Some b) \in dinsupp (tag η).1 -> P (a, b).
Proof. by case: (tagged η). Qed.

Lemma elift_dsuppR :
  forall a b, (Some a, b) \in dinsupp (tag η).2 -> P (a, b).
Proof. by case: (tagged η). Qed.

Lemma elift_edist :
  edist ε (deliftL (tag η).1) (deliftR (tag η).2)  <= δ.
Proof. by case: (tagged η). Qed.
End ELift.

(* -------------------------------------------------------------------- *)
Section ELiftFundamental.
Context {A B : choiceType} (ε δ : R).
Context (μ1 : distr A) (μ2 : distr B).
Context (Ea : pred A) (Eb : pred B).

Hypothesis ge0_ε : 0 <= ε.
Hypothesis ge0_δ : 0 <= δ.

Lemma elift_fundamental :
    elift ε δ μ1 μ2 [pred xy | (xy.1 \in Ea) ==> (xy.2 \in Eb)]
  -> \P_[μ1] Ea <= Ω ε * \P_[μ2] Eb + δ.
Proof.
case=> -[/= μL μR] [EL ER rgL rgR /edist_le -/(_ ge0_ε) /= le_δ].
pose T := [pred ab : option A * option B
  | if ab is (Some a, _) then a \in Ea else false].
move/(_ T): le_δ; rewrite !pr_dmargin /= => /le_trans.
rewrite -(eqr_pr _ EL) -(eqr_pr _ ER) !pr_dmargin; apply.
rewrite lerD2r ler_pM2l ?gt0_Ω //; apply/le_in_pr=> /=.
by case=> [[a|] b] //=; rewrite !inE /= => /rgR /implyP.
Qed.
End ELiftFundamental.

(* -------------------------------------------------------------------- *)
Section ELiftBnd.
Context {A B : choiceType} (ε δ : R).
Context (μ1 : distr A) (μ2 : distr B) (P : pred (A * B)).

Hypothesis ge0_ε : 0 <= ε.
Hypothesis ge0_δ : 0 <= δ.
Hypothesis ed : elift ε δ μ1 μ2 P.

Local Notation T := (distr (A * option B) * distr (option A * B))%type.

Local Notation elift_r μ :=
 [/\ dfst μ.1 =1 μ1, dsnd μ.2 =1 μ2
   , (forall a b, (a, Some b) \in dinsupp μ.1 -> P (a, b))
   , (forall a b, (Some a, b) \in dinsupp μ.2 -> P (a, b))
   & edist ε (deliftL μ.1) (deliftR μ.2) <= δ].

Local Notation R η := (forall a b,
  η.2 (Some a, b) <= η.1 (a, Some b) <= Ω ε * η.2 (Some a, b)).

Lemma elift_bnd : elift ε δ μ1 μ2 P -> { η : T | elift_r η /\ R η }.
Proof.
case=> -[ηL ηR] /= [eqL eqR hSL hSR hD].
pose ML a b := Num.min (ηL (a, Some b)) (Ω ε * ηR (Some a, b)).
pose MR a b := Num.min (ηL (a, Some b)) (ηR (Some a, b)).
pose ξL (ab : _ * _) := let (a, b) := ab in
  if b is Some b then ML a b else μ1 a - rsum (fun b => ML a b).
pose ξR (ab : _ * _) := let (a, b) := ab in
  if a is Some a then MR a b else μ2 b - rsum (fun a => MR a b).
have ge0_ML a b : 0 <= ML a b.
+ by rewrite le_min ge0_mu /= mulr_ge0 ?(ge0_Ω, ge0_mu).
have ge0_MR a b : 0 <= MR a b by rewrite le_min !ge0_mu.
(* [dfst]/[dsnd] are [rsum]s of the corresponding slices *)
have dfstL a : dfst ηL a = rsum (fun y => ηL (a, y)) by rewrite dfstE.
have dsndR b : dsnd ηR b = rsum (fun x => ηR (x, b)) by rewrite dsndE.
have sblML a : esummable [set: B] (EFin \o ML a).
+ apply: (le_esummable (g := fun b => ((Ω ε)%:E * (ηR (Some a, b))%:E)%E)).
  * move=> b _; rewrite /= lee_fin ge0_ML /= -EFinM lee_fin.
    by rewrite ge_min lexx orbT.
  apply: esummableZl => //; exact: (summable_fst ηR (Some a)).
have sblMR b : esummable [set: A] (EFin \o MR^~ b).
+ apply: (le_esummable (g := fun a => (ηL (a, Some b))%:E)).
  * move=> a _; rewrite /= !lee_fin ge0_MR /=.
    by rewrite ge_min lexx orTb.
  exact: (summable_snd ηL (Some b)).
have ge0_ξL a b : 0 <= ξL (a, b).
+ case: b => [b|] /=; first by apply/ge0_ML.
  rewrite subr_ge0; apply: rsum_le => [{}b|J uqJ]; first exact: ge0_ML.
  apply: (@le_trans _ _ (\sum_(j <- J) ηL (a, Some j))).
  * by apply: ler_sum => {}b _; rewrite ge_min lexx orTb.
  rewrite -eqL dfstL -(big_map some predT (fun y => ηL (a, y))).
  apply: gerfinseq_rsum; last exact: (summable_fst ηL a).
  * by rewrite map_inj_uniq // => x y [].
  by move=> ?; exact: ge0_mu.
have ge0_ξR a b : 0 <= ξR (a, b).
+ case: a => [a|] /=; first by apply/ge0_MR.
  rewrite subr_ge0; apply: rsum_le => [{}a|J uqJ]; first exact: ge0_MR.
  apply: (@le_trans _ _ (\sum_(j <- J) ηR (Some j, b))).
  * by apply: ler_sum => {}a _; rewrite ge_min lexx orbT.
  rewrite -eqR dsndR -(big_map some predT (fun x => ηR (x, b))).
  apply: gerfinseq_rsum; last exact: (summable_snd ηR b).
  * by rewrite map_inj_uniq // => x y [].
  by move=> ?; exact: ge0_mu.
have hL: isdistr ξL; first split => /= [[]//|J uqJ].
+ rewrite (partition_big_seq fst (fun j _ => ξL j)) //=; set K := undup _.
  rewrite (@le_trans _ _ (\sum_(a <- K) μ1 a)) //; last first.
  - by rewrite -pr_mem ?undup_uniq // le1_pr.
  apply/ler_sum=> {K} a _; rewrite big_filter.
  rewrite (eq_bigr (fun i => ξL (a, i.2))).
  - by case=> x y /= /eqP->.
  rewrite -big_filter -(big_map _ predT (fun b => ξL (a, b))).
  set K := map _ _.
  have sξL : esummable [set: option B] (EFin \o (fun b => ξL (a, b))).
  * by apply: esummable_optionT; exact: sblML.
  apply: (le_trans (gerfinseq_rsum _ _ _)).
  * rewrite map_inj_in_uniq ?filter_uniq //.
    case=> /= [x1 y1] [x2 y2]; rewrite !mem_filter /=.
    by move=> /andP[/eqP-> _] /andP[/eqP-> _] <-.
  * by move=> ?; exact: ge0_ξL.
  * exact: sξL.
  rewrite (rsum_option sξL) /=.
  by rewrite addrCA addrA lerBlDr lerD2l lexx.
have hR: isdistr ξR; first split => /= [[]//|J uqJ].
+ rewrite (partition_big_seq snd (fun j _ => ξR j)) //=; set K := undup _.
  rewrite (@le_trans _ _ (\sum_(b <- K) μ2 b)) //; last first.
  - by rewrite -pr_mem ?undup_uniq // le1_pr.
  apply/ler_sum=> {K} b _; rewrite big_filter.
  rewrite (eq_bigr (fun i => ξR (i.1, b))).
  - by case=> x y /= /eqP->.
  rewrite -big_filter -(big_map _ predT (fun a => ξR (a, b))).
  set K := map _ _.
  have sξR : esummable [set: option A] (EFin \o (fun a => ξR (a, b))).
  * by apply: esummable_optionT; exact: sblMR.
  apply: (le_trans (gerfinseq_rsum _ _ _)).
  * rewrite map_inj_in_uniq ?filter_uniq //.
    case=> /= [x1 y1] [x2 y2]; rewrite !mem_filter /=.
    by move=> /andP[/eqP-> _] /andP[/eqP-> _] <-.
  * by move=> ?; exact: ge0_ξR.
  * exact: sξR.
  rewrite (rsum_option sξR) /=.
  by rewrite addrCA addrA lerBlDr lerD2l lexx.
pose θL : distr (A * option B) := mkdistr hL.
pose θR : distr (option A * B) := mkdistr hR.
have le1 a b: θR (Some a, b) <= θL (a, Some b).
+ rewrite /θL /θR /MR /ML le_min ge_min lexx /=.
  by rewrite ge_min ler_peMl ?orbT /= ?(ge0_mu, Ω_ge1).
have le2 a b: θL (a, Some b) <= Ω ε * θR (Some a, b).
+ rewrite minr_pMr ?ge0_Ω // le_min !ge_min.
  by rewrite lexx orbT andbT ler_peMl // (ge0_mu, Ω_ge1).
exists (θL, θR); split; [split | by move=> a b; apply/andP].
+ move=> a.
  have -> : dfst θL a = rsum (fun y => θL (a, y)) by rewrite dfstE.
  rewrite (rsum_option (summable_fst θL a)) /θL /=.
  by rewrite addrCA subrr addr0.
+ move=> b.
  have -> : dsnd θR b = rsum (fun x => θR (x, b)) by rewrite dsndE.
  rewrite (rsum_option (summable_snd θR b)) /θR /=.
  by rewrite addrCA subrr addr0.
+ move=> a b h; apply/hSL; move/dinsuppP/eqP: h => /=.
  rewrite eq_le ge0_ML andbT -ltNge /ML lt_min => /andP.
  case=> h _; apply/dinsuppP/eqP; rewrite eq_le.
  by rewrite ge0_mu andbT -ltNge.
+ move=> a b h; apply/hSR; move/dinsuppP/eqP: h => /=.
  rewrite eq_le ge0_MR andbT -ltNge /ML lt_min => /andP.
  case=> _ h; apply/dinsuppP/eqP; rewrite eq_le.
  by rewrite ge0_mu andbT -ltNge.
apply/edist_le => //= X; rewrite (prID _ (isSome \o snd)).
set E : pred (option A * option B) := (X in \P_[_] X + _).
have: \P_[deliftL θL] E <= Ω ε * \P_[deliftR θR] E.
- rewrite -lee_fin EFinM !prE.
  rewrite -esumZ; first by move=> t _; rewrite lee_fin mulr_ge0 ?ler0n.
  apply: le_esum => -[a b] _; rewrite -EFinM lee_fin.
  rewrite mulrCA; case/boolP: (E (a, b)); rewrite ?(mul0r, mul1r) //.
  rewrite deliftLE deliftRE; case: a b => [a|] [b|] //.
  * by rewrite /E !inE andbF.
  * by move=> _; rewrite mulr_ge0 // ge0_Ω.
  * by move=> _; rewrite mulr0.
set p := (X in _ + X); rewrite -(lerD2r p).
move/le_trans; apply; apply/lerD.
- apply/ler_wpM2l; first by apply/ge0_Ω.
  by apply/le_in_pr=> /= ab _ /andP[].
pose Z : pred (option A * option B) := (pred1 None) \o snd.
rewrite {E}/p; apply/(@le_trans _ _ (\P_[deliftL θL] Z)).
- by apply/le_in_pr=> /= -[a [b|]] _; rewrite inE ?andbF.
pose ζ a b := Num.max 0 (deliftL ηL (a, b) - Ω ε * deliftR ηR (a, b)).
have MLE a b : ML a b = ηL (a, Some b) - ζ (Some a) (Some b).
- rewrite /ML /ζ /= /Num.min; case: ifPn => h.
  * by rewrite max_l ?subr0 // !(deliftLE, deliftRE) subr_le0 ltW.
  * rewrite max_r !(deliftLE, deliftRE) ?subKr //.
    by rewrite subr_ge0 // leNgt.
pose h a : option A * option B := (a, None).
pose FZ ab := (Z ab)%:R * deliftL θL ab.
have hinj : injective h by move=> x y [->].
have FZ0 x : (forall u, h u <> x) -> FZ x = 0.
- case: x => [a b] hx; rewrite /FZ /Z /=.
  have -> : (b == None) = false.
  * by apply/negbTE/eqP => e; apply: (hx a); rewrite /h e.
  by rewrite mul0r.
have ge0_FZ x : 0 <= FZ x.
- by rewrite /FZ mulr_ge0 ?ler0n ?ge0_mu.
have -> : \P_[deliftL θL] Z = rsum FZ by [].
rewrite (rsum_image hinj FZ0 ge0_FZ).
rewrite (eq_rsum (g := fun a => deliftL θL (a, None))).
- by move=> a; rewrite /FZ /Z /h /= mul1r.
(* the deficit in row [a] is exactly the ζ-mass of that row *)
have ζle a b : ζ (Some a) b <= ηL (a, b).
- rewrite /ζ ge_max ge0_mu /= deliftLE lerBlDr lerDl.
  by rewrite mulr_ge0 ?ge0_Ω ?ge0_mu.
have ζE a : μ1 a - rsum (fun b => ML a b) = rsum (fun b => ζ (Some a) b).
- have leζ b : 0 <= ζ (Some a) (Some b) <= ηL (a, Some b).
  * by rewrite le_max lexx /= ζle.
  have sηL : esummable [set: B] (EFin \o (fun b => ηL (a, Some b))).
  * by apply: (esummable_option (S := EFin \o (fun y => ηL (a, y))));
      exact: (summable_fst ηL a).
  have sζ : esummable [set: option B] (EFin \o (fun b => ζ (Some a) b)).
  * apply: (le_esummable (g := fun b => (ηL (a, b))%:E)).
    + by move=> b _; rewrite /= !lee_fin le_max lexx /= ζle.
    exact: (summable_fst ηL a).
  rewrite (rsum_option sζ) /=.
  have -> : ζ (Some a) None = ηL (a, None).
  * rewrite /ζ !(deliftLE, deliftRE) mulr0 subr0 max_r //; exact: ge0_mu.
  rewrite -eqL dfstL (rsum_option (summable_fst ηL a)) /=.
  have -> : rsum (fun b => ML a b)
          = rsum (fun b => ηL (a, Some b) - ζ (Some a) (Some b)).
  * by apply: eq_rsum => b; exact: MLE a b.
  rewrite (rsumB leζ sηL).
  by rewrite opprB addrAC addrCA subrr addr0.
rewrite (eq_rsum (g := fun a : option A => rsum (fun b => ζ a b))).
- case=> [a|]; first by rewrite deliftLE /θL /= ζE.
  rewrite deliftLE; symmetry.
  rewrite (eq_rsum (g := fun _ : option B => 0)) ?rsum0 //.
  move=> b; rewrite /ζ deliftLE sub0r.
  have h0 : - (Ω ε * deliftR ηR (None, b)) <= 0.
  * by rewrite oppr_le0 mulr_ge0 ?ge0_Ω ?ge0_mu.
  by rewrite (max_l h0).
pose S (ab : option A * option B) :=
  deliftL ηL ab > Ω ε * deliftR ηR ab.
have ζ0 ab : 0 <= ζ ab.1 ab.2 by rewrite le_max lexx.
have ζleD ab : ζ ab.1 ab.2 <= deliftL ηL ab.
- case: ab => a b /=; rewrite /ζ ge_max ge0_mu /= lerBlDr lerDl.
  by rewrite mulr_ge0 ?ge0_Ω ?ge0_mu.
have sζsl x : esummable [set: option B] (EFin \o (fun y => ζ x y)).
- apply: (le_esummable (g := fun y => (deliftL ηL (x, y))%:E)).
  * by move=> y _; rewrite /= !lee_fin (ζ0 (x, y)) (ζleD (x, y)).
  exact: (summable_fst (deliftL ηL) x).
(* [ζ] is the positive part of the deficit, supported on [S] *)
have ζS ab : ζ ab.1 ab.2
           = (S ab)%:R * deliftL ηL ab - (S ab)%:R * (Ω ε * deliftR ηR ab).
- case: ab => a b; rewrite /ζ /S /=.
  case/boolP: (Ω ε * deliftR ηR (a, b) < deliftL ηL (a, b)) => hS.
  * by rewrite !mul1r max_r // subr_ge0 ltW.
  by rewrite !mul0r subrr max_l // subr_le0 leNgt.
have leSζ ab : 0 <= (S ab)%:R * (Ω ε * deliftR ηR ab)
                 <= (S ab)%:R * deliftL ηL ab.
- rewrite mulr_ge0 ?ler0n ?mulr_ge0 ?ge0_Ω ?ge0_mu //=.
  case/boolP: (S ab) => hS; last by rewrite !mul0r.
  by rewrite !mul1r ltW.
have skey : esummable [set: (option A * option B)%type]
              (EFin \o (fun ab => (S ab)%:R * deliftL ηL ab)).
- by apply: esummable_condl; exact: (summable_mu (deliftL ηL)).
have key : rsum (fun ab => ζ ab.1 ab.2)
         = \P_[deliftL ηL] S - Ω ε * \P_[deliftR ηR] S.
- rewrite (eq_rsum ζS) (rsumB leSζ skey).
  congr (_ - _).
  rewrite (eq_rsum (g := fun ab => Ω ε * ((S ab)%:R * deliftR ηR ab))).
  * by move=> ab; rewrite mulrCA.
  by rewrite rsumZ // => ab; rewrite mulr_ge0 ?ler0n ?ge0_mu.
rewrite -(rsum_pair ζ0 sζsl) key lerBlDl.
move/edist_le: (hD) => -/(_ ge0_ε) -/(_ S).
by rewrite addrC.
Qed.

(* -------------------------------------------------------------------- *)
Section ELiftBndTheory.
Hypothesis η : { η : T | elift_r η /\ R η }.

Lemma exlift_dfstL : dfst (tag η).1 =1 μ1.
Proof. by case: (tagged η); case. Qed.

Lemma exlift_dsndR : dsnd (tag η).2 =1 μ2.
Proof. by case: (tagged η); case. Qed.

Lemma exlift_dsuppL :
  forall a b, (a, Some b) \in dinsupp (tag η).1 -> P (a, b).
Proof. by case: (tagged η); case. Qed.

Lemma exlift_dsuppR :
  forall a b, (Some a, b) \in dinsupp (tag η).2 -> P (a, b).
Proof. by case: (tagged η); case. Qed.

Lemma exlift_edist :
  edist ε (deliftL (tag η).1) (deliftR (tag η).2)  <= δ.
Proof. by case: (tagged η); case. Qed.

Lemma exlift_leLR a b :
  (tag η).1 (a, Some b) <= Ω ε * (tag η).2 (Some a, b).
Proof. by case: (tagged η) => _ /(_ a b) /andP[]. Qed.

Lemma exlift_leRL a b :
  (tag η).2 (Some a, b) <= (tag η).1 (a, Some b).
Proof. by case: (tagged η) => _ /(_ a b) /andP[]. Qed.
End ELiftBndTheory.
End ELiftBnd.
