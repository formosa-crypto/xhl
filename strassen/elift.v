(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.experimental_reals Require Import realsum distr xfinmap.

Require Import xbigops misc.

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

Local Notation distr T := {distr T / R}.

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
exists 1; apply/ubP=> y [a ->]; rewrite ler_naddr ?le1_pr //.
by rewrite oppr_le0 mulr_ge0 // (ge0_pr, ge0_Ω).
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_xx ε (μ : distr A) : edist ε μ μ = 0.
Proof.
rewrite /edist; case: ltrP => // ge0_e.
apply/max_sup=> /=; split; first by rewrite -in_setE; apply/z_in_edistp.
apply/ubP=> y [a ->]; rewrite subr_le0 ler_pemull //.
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
rewrite ge0_e' (le_trans ge0_e' le_e) /=; apply/le_sup; first last.
- by apply/has_sup_edistp.
- by exists 0; rewrite -in_setE; apply/z_in_edistp.
move=> x [S xE]; rewrite xE; apply/downP.
exists (\P_[μ1] S - Ω ε' * \P_[μ2] S); first by exists S.
by rewrite ler_add // ler_opp2 ler_wpmul2r ?ge0_pr // mono_Ω.
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_le ε δ (μ1 μ2 : distr A) : 0 <= ε ->
  reflect
    (forall S, \P_[μ1] S <= Ω ε * \P_[μ2] S + δ)
    (edist ε μ1 μ2 <= δ).
Proof.
move=> ge0_e; rewrite edistE //; apply: (iffP idP).
  move=> sle S; rewrite -ler_subl_addl (le_trans _ sle) //.
  apply/sup_upper_bound; first by apply/has_sup_edistp.
  by exists S.
move=> led; rewrite sup_le_ub //.
  by case: (has_sup_edistp ε μ1 μ2).
by apply/ubP=> x [S ->]; rewrite ler_subl_addr addrC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_le_supp ε δ (μ1 μ2 : distr A) : 0 <= ε ->
    (forall S, {subset S <= [predU dinsupp μ1 & dinsupp μ2]} ->
      \P_[μ1] S <= Ω ε * \P_[μ2] S + δ)
  -> (edist ε μ1 μ2 <= δ).
Proof.
move=> ge0_e; set P := [predU dinsupp μ1 & dinsupp μ2] => h.
apply/edist_le=> // S; rewrite (prID _ P μ1) (prID _ P μ2).
rewrite mulrDr addrAC ler_add //; first by apply/h=> x /andP[].
by rewrite !eq0_pr ?mulr0 // => x {}h; rewrite !inE h ?orbT andbF.
Qed.

(* -------------------------------------------------------------------- *)
Lemma edist_le_pp ε δ (μ1 μ2 : distr A) : 0 <= ε -> 0 <= δ ->
  reflect
    (exists2 di, (summable di /\ psum di <= δ) &
       [/\ forall x, 0 <= di x & forall x, μ1 x <= Ω ε * μ2 x + di x])
    (edist ε μ1 μ2 <= δ).
Proof.
move=> ge0_e ge0_d; apply: (iffP idP) => [led|].
* pose di x := \P_[μ1] (pred1 x) - Ω ε * \P_[μ2] (pred1 x).
  have h S: uniq S -> \sum_(i <- S) `|Num.max 0 (di i)| <= δ.
    move=> uqS; pose S' := [seq x <- S | 0 < di x].
    rewrite (bigID [pred x | 0 < di x]) /= addrC big1 ?add0r.
      by move=> x lt0_dix; rewrite max_l 1?leNgt ?normr0.
    rewrite (eq_bigr di) => [x gt0_dix|].
      by rewrite max_r ?ger0_norm 1?ltW.
    rewrite -big_filter -/S'; apply/(le_trans _ led).
    rewrite edistE //; apply/sup_upper_bound.
      by apply/has_sup_edistp.
    exists (ssrbool.mem S'); rewrite !pr_mem ?filter_uniq //.
    rewrite mulr_sumr -sumrB; apply/eq_bigr.
    by move=> i _; rewrite !pr_pred1.    
  exists (fun x => Num.max 0 (di x)); first (move=> [:a]; split).
  + by abstract: a; apply/summable_seqP; exists δ.
  + rewrite /psum; case: ifP=> _ //; apply/sup_le_ub.
      by exists 0; exists fset0; rewrite big_fset0.
    apply/ubP=> _ [S ->]; pose F x := `|Num.max 0 (di x)|.
    rewrite (big_fset_seq F) /=; apply/h.
    by case: S => S /= /canonical_uniq.
  split=> x; first by rewrite le_maxr lexx.
  by rewrite -ler_subl_addl le_maxr /di !pr_pred1 lexx orbT.
case=> di [sm_di led] [ge0_di lemu]; rewrite edistE 1?sup_le_ub //.
* by exists 0; exists pred0; rewrite !pr_pred0 mulr0 subr0.
apply/ubP=> _ [S ->]; rewrite /pr.
set v1 := psum _; set v2 := psum _; apply/(le_trans _ led).
rewrite ler_subl_addr -psumZ ?ge0_Ω // -psumD //=.
+ by move=> x; rewrite !mulr_ge0 ?(ler0n, ge0_Ω).
+ by apply/summableZ/summable_pr.
apply/le_psum/summableD => //; last by apply/summableZ/summable_pr.
move=> x; rewrite mulr_ge0 ?ler0n //=; case: (S x) => /=.
  by rewrite !mul1r addrC. by rewrite !(mulr0, mul0r) addr0.
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
rewrite dletE; case: a => /= [a|]; last first.
+ by rewrite psum_eq0 //= => ab; rewrite dunit1E mulr0.
rewrite (psum_finseq (r := [:: (a, b)])) //.
+ case=> [a' b']; rewrite !inE dunit1E /= mulf_eq0 => /norP[_].
  by rewrite pnatr_eq0 eqb0 negbK => /eqP[-> ->].
by rewrite big_seq1 dunit1E eqxx mulr1 ger0_norm.
Qed.

Lemma deliftRE (μ : distr (option A * B)) a b :
  deliftR μ (a, b) = if b is Some b then μ (a, b) else 0.
Proof.
rewrite dletE; case: b => /= [b|]; last first.
+ rewrite psum_eq0 //= => ab; rewrite dunit1E.
  by rewrite eqE /= andbF mulr0.
rewrite (psum_finseq (r := [:: (a, b)])) //.
+ case=> [a' b']; rewrite !inE dunit1E /= mulf_eq0 => /norP[_].
  by rewrite pnatr_eq0 eqb0 negbK => /eqP[-> ->].
by rewrite big_seq1 dunit1E eqxx mulr1 ger0_norm.
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
rewrite ler_add2r ler_pmul2l ?gt0_Ω //; apply/le_in_pr=> /=.
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
  if b is Some b then ML a b else μ1 a - psum (fun b => ML a b).
pose ξR (ab : _ * _) := let (a, b) := ab in
  if a is Some a then MR a b else μ2 b - psum (fun a => MR a b).
have ge0_ML a b : 0 <= ML a b.
+ by rewrite le_minr ge0_mu /= mulr_ge0 ?(ge0_Ω, ge0_mu).
have ge0_MR a b : 0 <= MR a b by rewrite le_minr !ge0_mu.
have sblML a : summable (ML a).
+ apply/(le_summable _ (summableZ (Ω ε) (summable_fst ηR (Some a)))).
  by move=> b; rewrite ge0_ML /=; rewrite le_minl lexx orbT.
have sblMR b : summable (MR^~ b).
+ apply/(le_summable _ (summable_snd ηL (Some b))).
  by move=> a; rewrite ge0_MR /=; rewrite le_minl lexx orTb.
have ge0_ξL a b : 0 <= ξL (a, b).
+ case: b => [b|] /=; first by apply/ge0_ML.
  rewrite subr_ge0 -eqL dfstE /=; apply/psum_le => J uqJ.
  apply/(@le_trans _ _ (\sum_(j <- J) ηL (a, Some j))).
  - apply/ler_sum=> b _; rewrite ger0_norm ?ge0_ML //.
    by rewrite le_minl lexx orTb.
  apply/(le_trans _ (gerfinseq_psum (r := map some J) _ _)).
  - by rewrite big_map; apply/ler_sum=> b _; apply/ler_norm.
  - by rewrite map_inj_uniq // => x y [].
  - by apply/summable_fst.
have ge0_ξR a b : 0 <= ξR (a, b).
+ case: a => [a|] /=; first by apply/ge0_MR.
  rewrite subr_ge0 -eqR dsndE /=; apply/psum_le => J uqJ.
  apply/(@le_trans _ _ (\sum_(j <- J) ηR (Some j, b))).
  - apply/ler_sum=> a _; rewrite ger0_norm ?ge0_MR //.
    by rewrite le_minl lexx orbT.
  apply/(le_trans _ (gerfinseq_psum (r := map some J) _ _)).
  - by rewrite big_map; apply/ler_sum=> a _; apply/ler_norm.
  - by rewrite map_inj_uniq // => x y [].
  - by apply/summable_snd.
have hL: isdistr ξL; first split => /= [[]//|J uqJ].
+ rewrite (partition_big_seq fst (fun j _ => ξL j)) //=; set K := undup _.
  rewrite (@le_trans _ _ (\sum_(a <- K) μ1 a)) //; last first.
  - by rewrite -pr_mem ?undup_uniq // le1_pr.
  apply/ler_sum=> {K} a _; rewrite big_filter.
  rewrite (eq_bigr (fun i => ξL (a, i.2))).
  - by case=> x y /= /eqP->.
  rewrite -big_filter -(big_map _ predT (fun b => ξL (a, b))).
  set K := map _ _; rewrite (eq_bigr (fun b => `|ξL (a, b)|)).
  - by move=> b _; rewrite ger0_norm.
  apply/(le_trans (gerfinseq_psum _ _)).
  * rewrite map_inj_in_uniq ?filter_uniq //.
    case=> /= [x1 y1] [x2 y2]; rewrite !mem_filter /=.
    by move=> /andP[/eqP-> _] /andP[/eqP-> _] <-.
  * by apply/summable_option/sblML.
  rewrite psum_option /=; first by apply/summable_option/sblML.
  rewrite ger0_norm ?(ge0_ξL a None) // addrCA.
  by rewrite addrA ler_subl_addr ler_add2l lexx.
have hR: isdistr ξR; first split => /= [[]//|J uqJ].
+ rewrite (partition_big_seq snd (fun j _ => ξR j)) //=; set K := undup _.
  rewrite (@le_trans _ _ (\sum_(b <- K) μ2 b)) //; last first.
  - by rewrite -pr_mem ?undup_uniq // le1_pr.
  apply/ler_sum=> {K} b _; rewrite big_filter.
  rewrite (eq_bigr (fun i => ξR (i.1, b))).
  - by case=> x y /= /eqP->.
  rewrite -big_filter -(big_map _ predT (fun a => ξR (a, b))).
  set K := map _ _; rewrite (eq_bigr (fun a => `|ξR (a, b)|)).
  - by move=> a _; rewrite ger0_norm.
  apply/(le_trans (gerfinseq_psum _ _)).
  * rewrite map_inj_in_uniq ?filter_uniq //.
    case=> /= [x1 y1] [x2 y2]; rewrite !mem_filter /=.
    by move=> /andP[/eqP-> _] /andP[/eqP-> _] <-.
  * by apply/summable_option/sblMR.
  rewrite psum_option /=; first by apply/summable_option/sblMR.
  rewrite ger0_norm ?(ge0_ξR None b) // addrCA.
  by rewrite addrA ler_subl_addr ler_add2l lexx.
pose θL : distr (A * option B) := mkdistr hL.
pose θR : distr (option A * B) := mkdistr hR.
have le1 a b: θR (Some a, b) <= θL (a, Some b).
+ rewrite /θL /θR /MR /ML le_minr le_minl lexx /=.
  by rewrite le_minl ler_pemull ?orbT /= ?(ge0_mu, Ω_ge1).
have le2 a b: θL (a, Some b) <= Ω ε * θR (Some a, b).
+ rewrite minr_pmulr ?ge0_Ω // le_minr !le_minl.
  by rewrite lexx orbT andbT ler_pemull // (ge0_mu, Ω_ge1).
exists (θL, θR); split; [split | by move=> a b; apply/andP].
+ move=> a; rewrite dfstE /= psum_option.
  * by apply/(summable_fst (mkdistr hL) a).
  rewrite ger0_norm ?(ge0_mu (mkdistr hL) (a, None)) //.
  apply/eqP; rewrite eq_sym -subr_eq opprB addrCA.
  by rewrite subrr addr0; apply/eqP/eq_psum.
+ move=> b; rewrite dsndE /= psum_option /=.
  * by apply/(summable_snd (mkdistr hR) b).
  rewrite ger0_norm ?(ge0_mu (mkdistr hR) (None, b)) //.
  apply/eqP; rewrite eq_sym -subr_eq opprB addrCA.
  by rewrite subrr addr0; apply/eqP/eq_psum.
+ move=> a b h; apply/hSL; move/dinsuppP/eqP: h => /=.
  rewrite eq_le ge0_ML andbT -ltNge /ML lt_minr => /andP.
  case=> h _; apply/dinsuppP/eqP; rewrite eq_le.
  by rewrite ge0_mu andbT -ltNge.
+ move=> a b h; apply/hSR; move/dinsuppP/eqP: h => /=.
  rewrite eq_le ge0_MR andbT -ltNge /ML lt_minr => /andP.
  case=> _ h; apply/dinsuppP/eqP; rewrite eq_le.
  by rewrite ge0_mu andbT -ltNge.
apply/edist_le => //= X; rewrite (prID _ (isSome \o snd)).
set E : pred (option A * option B) := (X in \P_[_] X + _).
have: \P_[deliftL θL] E <= Ω ε * \P_[deliftR θR] E.
- rewrite /pr /= -psumZ ?ge0_Ω //; apply/le_psum => /=; last first.
  * by apply/summableZ/summable_condl/summable_mu.
  case=> a b; rewrite mulr_ge0 ?(ler0n, ge0_mu) //=.
  rewrite mulrCA; case/boolP: (E (a, b)); rewrite ?(mul0r, mul1r) //.
  rewrite deliftLE deliftRE; case: a b => [a|] [b|] //.
  * by rewrite /E !inE andbF.
  * by move=> _; rewrite mulr_ge0 // ge0_Ω.
  * by move=> _; rewrite mulr0.
set p := (X in _ + X); rewrite -(ler_add2r p).
move/le_trans; apply; apply/ler_add.
- apply/ler_wpmul2l; first by apply/ge0_Ω.
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
rewrite /pr (reindex_psum (h := h) (P := Z)) /=.
- case=> [a b]; rewrite mulf_eq0 => /norP[].
  by rewrite pnatr_eq0 eqb0 negbK.
- by exists fst => // -[a b] /eqP /= ->.
rewrite (eq_psum (F2 := deliftL θL \o h)).
- by move=> a; rewrite mul1r.
pose F a := μ1 a - psum [eta ML a].
rewrite psum_option /=; first by apply/summable_snd.
rewrite deliftLE normr0 addr0 /= (eq_psum (F2 := F)) {}/F.
- by move=> a /=; rewrite deliftLE.
pose F a := psum (fun b => ζ (Some a) b).
rewrite {h}(eq_psum (F2 := F)) => [a|].
- rewrite (eq_psum (MLE a)) -eqL dfstE /= psum_option.
  * by apply/summable_fst.
  rewrite addrAC -psumB /= => [b||].
  * by rewrite -MLE ge0_ML /= le_minl lexx.
  * apply/(@summable_option _ _ (fun b => ηL (a, b))).
    by apply/summable_fst.
  rewrite (eq_psum (F2 := fun b => ζ (Some a) (Some b))).
  * by move=> b /=; rewrite subKr.
  rewrite [X in `|X|](_ : _ = ζ (Some a) None).
  * rewrite /ζ /= max_r !(deliftLE, deliftRE).
    - by rewrite mulr0 subr0 ge0_mu.
    - by rewrite mulr0 subr0.
  rewrite -psum_option //; apply/summable_option.
  apply/(le_summable (F2 := fun b => ηL (a, Some b))).
  * move=> b; rewrite le_maxr lexx /= /ζ le_maxl.
    rewrite ge0_mu /= !(deliftLE, deliftRE) ler_subl_addr.
    by rewrite ler_addl mulr_ge0 ?(ge0_Ω, ge0_mu).
  apply/(@summable_option _ _ (fun b => ηL (a, b))).
  by apply/summable_fst.
pose S (ab : option A * option B) :=
  deliftL ηL ab > Ω ε * deliftR ηR ab.
move/edist_le: (hD) => -/(_ ge0_ε) -/(_ S).
rewrite -ler_subl_addl => /(le_trans _); apply.
rewrite /pr /= -psumZ ?ge0_Ω // -psumB /=.
* case=> a b; rewrite mulr_ge0 ?ge0_Ω //=.
  - by rewrite mulr_ge0 ?ler0n.
  case/boolP: (S (a, b)); last by rewrite !(mulr0,mul0r).
  by rewrite !(mulr1,mul1r) => /ltW.
* by apply/summable_condl/summable_mu.
rewrite (eq_psum (F2 := fun ab => ζ ab.1 ab.2)) /= ?psum_pair /=.
* case=> a b /=; rewrite /ζ /=; case/boolP: (S (a, b)) => h.
  - by rewrite !(mul1r,mulr1) max_r // subr_ge0 ltW.
  - by rewrite !(mul0r,mulr0) subrr max_l // subr_le0 leNgt.
* apply/(le_summable (F2 := fun ab => deliftL ηL ab))/summable_mu.
  case=> /= a b; rewrite /ζ /Num.max; case: ifPn; last first.
  - by rewrite lexx ge0_mu.
  move/ltW => ->/=; rewrite ler_subl_addr.
  by rewrite ler_addl mulr_ge0 ?(ge0_Ω, ge0_mu).
case/asboolP: (summable F) => h; last first.
* by rewrite psum_out // ge0_psum.
rewrite psum_option; first by apply/summable_option.
by rewrite ler_addl normr_ge0.
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
