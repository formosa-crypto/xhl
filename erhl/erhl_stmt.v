From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp.analysis  Require Import sequences normedtype topology.
From mathcomp           Require finmap.
From xhl                Require Import misc rsum.
From xhl.pwhile         Require Import notations inhabited mem pwhile psemantic passn range.
From xhl.prhl           Require Import prhl.
From xhl.ehl            Require Import ehl_stmt.
From xhl.strassen       Require Import deficiency.
From xhl.erhl           Require Import star.

Import GRing.Theory Order.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope sem_scope.
Local Open Scope classical_set_scope.

Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Section erhl.
Context {R : realType}.

Local Notation Distr T := {distr T%type / R}.

(* ==================================================================== *)
(* Relational pre- and post-expectations                                 *)
(* ==================================================================== *)
Section RCond.
Context {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg}.

Local Notation rmem  := (rmem A B X Xg M).
Local Notation assn  := (pred M).

(* Assertions are quantitative: [rmem = cmem * cmem -> \bar R].  The     *)
(* paper's [E<1>] / [E<2>] are pwhile's [e#'1] / [e#'2].                 *)
Definition rcond  := rmem -> \bar R.

(* The "generic" post-expectation also reads the *initial* pair of       *)
(* memories.  This replaces the paper's type [Z] of logical variables    *)
(* (cf. [hl_stmt.assn2] and [ehl_stmt.cond2]).                          *)
Definition rcond2 := rmem -> rmem -> \bar R.

(* [psi*]: the 0-extension of a post-expectation to starred memories.    *)
Definition rstar (g : rcond) (p : option M * option M) : \bar R :=
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

(* Image of a set of memories under a relation, the paper's [R(M)].      *)
Definition rimage (Rl : rel M) (M : assn) : assn :=
  [pred m2 | `[< exists m1, M m1 && Rl m1 m2 >]].

(* Expectation through [slift]: the mass parked on (None, None) is        *)
(* invisible to [rstar], so nothing is lost.                              *)
Lemma espe_slift (nu : Distr (M * M)%type) (g : rcond) :
  (forall m, (0 <= g m)%E) -> espe (slift nu) (rstar g) = espe nu g.
Proof.
move=> hg.
have hpos : forall o : option (M * M)%type,
  (0 <= (rstar g \o (fun o' => if o' is Some p then (Some p.1, Some p.2)
                               else (@None M, @None M))) o)%E.
+ by move=> o; exact: ge0_rstar.
have hnone : (rstar g \o (fun o' => if o' is Some p then (Some p.1, Some p.2)
                                    else (@None M, @None M))) None = 0%E.
+ by [].
transitivity (espe (dstar nu)
  (rstar g \o (fun o' => if o' is Some p then (Some p.1, Some p.2)
                         else (@None M, @None M)))).
+ by rewrite /slift; apply: eexp_dmargin => p; exact: ge0_rstar.
rewrite (espe_dstar _ _ hpos hnone).
by apply: eexp_eq; case=> a b.
Qed.

(* A star-coupling all of whose mass has [None] on the left sees nothing  *)
(* of the post-expectation.  Note this needs no sign condition on [g] --  *)
(* which is what lets [erhl_abort] hold for an arbitrary post.            *)
Lemma espe_rstar_left0 (mu : Distr (option M)) (g : rcond) :
  espe (dmargin (fun o => (@None M, o)) mu) (rstar g) = 0%E.
Proof.
rewrite /espe -[RHS](@esum0 R (option M * option M)%type [set: _]).
apply: eq_esum; case=> [[a|] b] _ /=; last by rewrite /rstar mul0e.
have -> : dmargin (fun o => (@None M, o)) mu (Some a, b) = 0.
+ rewrite dmarginE dletE_rsum -[RHS](@rsum0 R (option M)).
  by apply: eq_rsum => o; rewrite dunit1E xpair_eqE /= mulr0.
by rewrite mule0.
Qed.

Lemma espe_rstar_right0 (mu : Distr (option M)) (g : rcond) :
  espe (dmargin (fun o => (o, @None M)) mu) (rstar g) = 0%E.
Proof.
rewrite /espe -[RHS](@esum0 R (option M * option M)%type [set: _]).
apply: eq_esum; case=> [[a|] [b|]] _; rewrite /rstar /=;
  try by rewrite mul0e.
have -> : dmargin (fun o => (o, @None M)) mu (Some a, Some b) = 0.
+ rewrite dmarginE dletE_rsum -[RHS](@rsum0 R (option M)).
  by apply: eq_rsum => o; rewrite dunit1E xpair_eqE /= andbF mulr0.
by rewrite mule0.
Qed.

(* Transporting an expectation across [dswap].  Needs [0 <= g] because it   *)
(* goes through [eexp_dmargin].                                             *)
Lemma espe_dswap (nu : Distr (option M * option M)%type) (g : rcond) :
  (forall m, (0 <= g m)%E) ->
  espe (dswap nu) (rstar g) = espe nu (rstar (rswap g)).
Proof.
move=> hg.
have -> : espe (dswap nu) (rstar g)
        = espe nu (rstar g \o (fun xy : option M * option M => (xy.2, xy.1))).
+ by rewrite /dswap; apply: eexp_dmargin => p; exact: ge0_rstar.
by apply: eexp_eq; case=> [[a|] [b|]]; rewrite /comp /rstar /rswap.
Qed.

Lemma espe_dmargin_rstar (nu : Distr (option M * option M)%type)
    (k1 k2 : M -> M) (g : rcond) :
  (forall m, (0 <= g m)%E) ->
  espe (dmargin (fun p => (omap k1 p.1, omap k2 p.2)) nu) (rstar g)
  = espe nu (rstar (fun m' : rmem => g (k1 m'.1, k2 m'.2))).
Proof.
move=> hg.
have -> : espe (dmargin (fun p => (omap k1 p.1, omap k2 p.2)) nu) (rstar g)
        = espe nu (rstar g \o (fun p => (omap k1 p.1, omap k2 p.2))).
+ by apply: eexp_dmargin => p; exact: ge0_rstar.
by apply: eexp_eq; case=> [[a|] [b|]]; rewrite /comp /rstar.
Qed.

(* [rstar] is additive, and so is [espe] on non-negative integrands. *)
Lemma espe_rstarD (nu : Distr (option M * option M)%type)
    (r1 r2 : rcond) :
  (forall m, (0 <= r1 m)%E) -> (forall m, (0 <= r2 m)%E) ->
  espe nu (rstar (fun m => (r1 m + r2 m)%E))
  = (espe nu (rstar r1) + espe nu (rstar r2))%E.
Proof.
move=> hA hB; rewrite /espe -esumD.
+ by move=> p _; apply: mule_ge0; [apply: ge0_rstar; exact: hA
                                 | rewrite lee_fin ge0_mu].
+ by move=> p _; apply: mule_ge0; [apply: ge0_rstar; exact: hB
                                 | rewrite lee_fin ge0_mu].
apply: eq_esum; case=> [[a|] [b|]] _; rewrite /rstar /=;
  try by rewrite mul0e adde0.
have hAb : (0 <= r1 (a, b))%E by exact: hA.
have hBb : (0 <= r2 (a, b))%E by exact: hB.
by rewrite (ge0_muleDl _ hAb hBb).
Qed.

End RCond.

Section Strassen.
Context {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg}.

Local Notation rmem  := (rmem A B X Xg M).

(* ---------------------------------------------------------------------- *)
(* Strassen's theorem with deficiency (paper Prop. 3.2), in                *)
(* star-coupling form.  Sole consumer: [erhl_strassen] (erhl/erhl.v).      *)
(*                                                                        *)
(* [strassen.deficiency.strassen_coupling] gives it in ordinary coupling   *)
(* form; since both sides have weight 1 the two forms coincide, and the    *)
(* translation is [slift] / [scoupling_slift] / [espe_slift] above.        *)
Lemma strassen_deficiency
    (D1 D2 : Distr M) (Rl : rel M) (delta : R) :
  dweight D1 = 1 -> dweight D2 = 1 -> 0 <= delta ->
  (forall M : pred M, \P_[D1] M <= \P_[D2] (rimage Rl M) + delta) ->
  exists2 nu, scoupling D1 D2 nu &
    (espe nu (rstar (fun m' : rmem => ((~~ Rl m'.1 m'.2)%:R)%:E))
       <= delta%:E)%E.
Proof.
move=> w1 w2 hd hM.
(* [rimage] and [strassen.imS] are the same predicate, modulo [exists2]. *)
have hM' : forall M : pred M,
    \P_[D1] M <= \P_[D2] [pred y | `[< exists2 x, x \in M & Rl x y >]] + delta.
+ move=> p.
  have e : [pred m2 | `[< exists m1, p m1 && Rl m1 m2 >]]
        =i [pred y | `[< exists2 x, x \in p & Rl x y >]].
  - move=> y; rewrite !inE; apply/idP/idP.
    * move/asboolP => [x /andP[hx hxy]]; apply/asboolP.
      by exists x.
    move/asboolP => [x hx hxy]; apply/asboolP.
    by exists x; apply/andP; split.
   by rewrite -(@eq_pr _ _ _ _ D2 e); exact: hM p.
have [kap [hf hs] hle] := strassen_coupling w1 w2 hd hM'.
exists (slift kap); first exact: scoupling_slift.
rewrite espe_slift; first by move=> m'; rewrite lee_fin ler0n.
rewrite espe_indic lee_fin.
exact: hle.
Qed.

End Strassen.

(* ==================================================================== *)
(* Validity                                                             *)
(* ==================================================================== *)
Section Validity.
Context {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg}.

Local Notation psi := (Y -> (@cmd_ R A B X Xg M Y)).
Local Notation rcond := (@rcond A B X Xg M).
Local Notation rcond2 := (@rcond2 A B X Xg M).
Local Notation rstar := (@rstar A B X Xg M).
Local Notation cmd  := (@cmd_ R A B X Xg M Y).
Local Notation rmem  := (@rmem A B X Xg M).
Local Notation assn  := (pred M).

Implicit Types (f g : rcond) (c d : cmd) (ps : psi).

(* Definition 4.1: validity witnessed by a star-coupling. *)
Definition erhl_ ps f c d g :=
  forall m : rmem, exists2 nu,
      scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
    & (espe nu (rstar g) <= f m)%E.

(* Generic (Z-free) judgment: the post may read the initial memories. *)
Definition kerhl_ (ps:psi) f c d (g : rcond2) :=
  forall m : rmem, exists2 nu,
      scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
    & (espe nu (rstar (g m)) <= f m)%E.

(* Lemma 4.2: the same, phrased with the infimum [psi#]. *)
Definition scouplings (d1 d2 : Distr M) :
    set (Distr (option M * option M)%type) :=
  [set nu | scoupling d1 d2 nu].

Definition psharp g (d1 d2 : Distr M) : \bar R :=
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

Lemma psharp_lbound (D1 D2 : Distr M) (g : rcond)
    (nu : Distr (option M * option M)%type) :
  scoupling D1 D2 nu -> (psharp g D1 D2 <= espe nu (rstar g))%E.
Proof. by move=> h; apply: ereal_inf_lbound; exists nu. Qed.

Lemma ge0_espe_rstar (nu : Distr (option M * option M)%type) (g : rcond) :
  (forall m, (0 <= g m)%E) -> (0 <= espe nu (rstar g))%E.
Proof.
move=> hg; apply: esum_ge0 => p _.
by apply: mule_ge0; [apply: ge0_rstar | rewrite lee_fin ge0_mu].
Qed.

(* --------------------------------------------------------------------- *)
(* The compactness core, shared by [psharp_attained] and [psharp_dlim].    *)
(*                                                                       *)
(* From a sequence of star-couplings whose marginals converge pointwise,  *)
(* [dcompact] extracts a pointwise-convergent subsequence; its limit is   *)
(* again a star-coupling, and the objective is lower semicontinuous along *)
(* it.  Two things do the work.  [dlim_weight1] (rsum.v) says no mass     *)
(* escapes -- which is where the fullness of [dstar _] is used, and which *)
(* Fatou alone could never give, since Fatou only ever yields [<=].  The  *)
(* pinching lemma [le_rsum_eqP] then upgrades the two marginal            *)
(* inequalities to equalities.  Only the last step uses [espe_fatou].     *)
Lemma scoupling_lim (mu1 mu2 : nat -> Distr M) (D1 D2 : Distr M)
    (nu : nat -> Distr (option M * option M)%type) (g : rcond) :
  (forall n, scoupling (mu1 n) (mu2 n) (nu n)) ->
  (forall a, ((fun n => dstar (mu1 n) a) @ \oo --> dstar D1 a)%classic) ->
  (forall b, ((fun n => dstar (mu2 n) b) @ \oo --> dstar D2 b)%classic) ->
  (forall m, (0 <= g m)%E) ->
  exists2 nu0, scoupling D1 D2 nu0 &
    exists2 omega : nat -> nat, {homo omega : x y / (x < y)%N} &
      (espe nu0 (rstar g)
         <= limn_einf (fun n => espe (nu (omega n)) (rstar g)))%E.
Proof.
move=> hnu c1 c2 hg.
have [omega homo_om cvom] := dcompact nu.
pose nu0 := dlim (fun n => nu (omega n)).
have hf : forall n, dfst (nu (omega n)) = dstar (mu1 (omega n)).
+ by move=> n; case: (hnu (omega n)).
have hs : forall n, dsnd (nu (omega n)) = dstar (mu2 (omega n)).
+ by move=> n; case: (hnu (omega n)).
have c1' : forall a, ((fun n => dstar (mu1 (omega n)) a) @ \oo
                        --> dstar D1 a)%classic.
+ move=> a.
  by apply: (cvg_comp omega (fun k => dstar (mu1 k) a)
               (cvg_homo_oo homo_om) (c1 a)).
have c2' : forall b, ((fun n => dstar (mu2 (omega n)) b) @ \oo
                        --> dstar D2 b)%classic.
+ move=> b.
  by apply: (cvg_comp omega (fun k => dstar (mu2 k) b)
               (cvg_homo_oo homo_om) (c2 b)).
have cf : forall a, ((fun n => dfst (nu (omega n)) a) @ \oo
                        --> dstar D1 a)%classic.
+ move=> a; have -> : ((fun n => dfst (nu (omega n)) a) @ \oo)
                    = ((fun n => dstar (mu1 (omega n)) a) @ \oo).
  - by apply: near_eq_cvg_eq; apply: nearW => n; rewrite hf.
  exact: c1' a.
have cs : forall b, ((fun n => dsnd (nu (omega n)) b) @ \oo
                        --> dstar D2 b)%classic.
+ move=> b; have -> : ((fun n => dsnd (nu (omega n)) b) @ \oo)
                    = ((fun n => dstar (mu2 (omega n)) b) @ \oo).
  - by apply: near_eq_cvg_eq; apply: nearW => n; rewrite hs.
  exact: c2' b.
have wt : dweight nu0 = 1.
+ by apply: (dlim_weight1 (dweight_dstar D1) (dweight_dstar D2) cf cs cvom).
(* the two marginal inequalities, from finite partial sums *)
have le1 : forall a, dfst nu0 a <= dstar D1 a.
+ move=> a; rewrite dfstE_rsum; apply: rsum_le; first by move=> b; exact: ge0_mu.
  move=> J uJ.
  have cvJ : ((fun n => \sum_(b <- J) nu (omega n) (a, b)) @ \oo
                --> \sum_(b <- J) nu0 (a, b))%classic.
  + by apply: cvg_bigseq => b; exact: cvg_dlim_pt.
  have hnear : (\forall n \near \oo,
      \sum_(b <- J) nu (omega n) (a, b) <= dstar (mu1 (omega n)) a)%classic.
  + by apply: nearW => n; rewrite -(hf n); exact: sum_seq_le_dfst.
  have : \sum_(b <- J) nu0 (a, b) <= dstar D1 a
    by exact: (ler_cvg_to cvJ (c1' a) hnear).
  by [].
have le2 : forall b, dsnd nu0 b <= dstar D2 b.
+ move=> b; rewrite dsndE_rsum; apply: rsum_le; first by move=> a; exact: ge0_mu.
  move=> J uJ.
  have cvJ : ((fun n => \sum_(a <- J) nu (omega n) (a, b)) @ \oo
                --> \sum_(a <- J) nu0 (a, b))%classic.
  + by apply: cvg_bigseq => a; exact: cvg_dlim_pt.
  have hnear : (\forall n \near \oo,
      \sum_(a <- J) nu (omega n) (a, b) <= dstar (mu2 (omega n)) b)%classic.
  + by apply: nearW => n; rewrite -(hs n); exact: sum_seq_le_dsnd.
  have : \sum_(a <- J) nu0 (a, b) <= dstar D2 b
    by exact: (ler_cvg_to cvJ (c2' b) hnear).
  by [].
(* mass preservation pinches them into equalities *)
have hfst : dfst nu0 = dstar D1.
+ apply/distr_eqP; apply: (le_rsum_eqP (g := dstar D1)).
  - by move=> a; rewrite ge0_mu /= le1.
  - exact: summable_mu.
  have e1 : rsum (dfst nu0) = 1 by rewrite -dweightE dweight_dfst wt.
  by rewrite e1 -dweightE dweight_dstar.
have hsnd : dsnd nu0 = dstar D2.
+ apply/distr_eqP; apply: (le_rsum_eqP (g := dstar D2)).
  - by move=> b; rewrite ge0_mu /= le2.
  - exact: summable_mu.
  have e2 : rsum (dsnd nu0) = 1 by rewrite -dweightE dweight_dsnd wt.
  by rewrite e2 -dweightE dweight_dstar.
exists nu0; first by split.
exists omega => //.
by apply: espe_fatou => p; apply: ge0_rstar.
Qed.

(* The non-negativity hypothesis is NOT cosmetic: [esum] on a signed      *)
(* family is a Jordan difference [pos_esum g^+ - pos_esum g^-], and for a *)
(* [g] unbounded below the infimum need not be attained (nor even be      *)
(* meaningful when both parts diverge).                                   *)
Lemma psharp_attained (D1 D2 : Distr M) (g : rcond) :
  (forall m, (0 <= g m)%E) ->
  exists2 nu, scoupling D1 D2 nu & espe nu (rstar g) = psharp g D1 D2.
Proof.
move=> hg.
have h0 : (0 <= psharp g D1 D2)%E.
+ by apply: le_ereal_inf_tmp => _ [nu _ <-]; exact: ge0_espe_rstar.
case: (eqVneq (psharp g D1 D2) (+oo)%E) => [hoo|hfin].
+ (* the infimum of a nonempty set is [+oo] only if every element is *)
  have [nu hnu] := exists_scoupling D1 D2.
  exists nu => //; apply/eqP; rewrite eq_le hoo leey /=.
  by rewrite -hoo; exact: psharp_lbound.
have hfn : psharp g D1 D2 \is a fin_num by rewrite ge0_fin_numE // ltey.
have [c hcE] : exists c : R, psharp g D1 D2 = c%:E.
+ by exists (fine (psharp g D1 D2)); rewrite fineK.
(* a minimising sequence, with harmonic error *)
have hseq : forall n : nat, exists nu, scoupling D1 D2 nu
              /\ (espe nu (rstar g) <= (c + harmonic n)%:E)%E.
+ move=> n.
  have [x [nu hnu <-] hlt] := lb_ereal_inf_adherent (harmonic_gt0 n) hfn.
  by exists nu; split=> //; apply: ltW; rewrite EFinD -hcE.
have [nu hnuP] := choice hseq.
have hcst1 : forall a, ((fun _ : nat => dstar D1 a) @ \oo
                          --> dstar D1 a)%classic by move=> a; exact: cvg_cst.
have hcst2 : forall b, ((fun _ : nat => dstar D2 b) @ \oo
                          --> dstar D2 b)%classic by move=> b; exact: cvg_cst.
have [nu0 hnu0 [omega homo_om hle]] :=
  scoupling_lim (fun _ => D1) (fun _ => D2) D1 D2 nu g
    (fun n => proj1 (hnuP n)) hcst1 hcst2 hg.
exists nu0 => //; apply/eqP; rewrite eq_le; apply/andP; split;
  last exact: psharp_lbound.
apply: (le_trans hle); rewrite hcE; apply: limn_einf_le_harmonic => n.
apply: (le_trans (proj2 (hnuP (omega n)))).
(* [n <= omega n], and [harmonic] is antitone *)
rewrite lee_fin lerD2l /harmonic /= lef_pV2 ?posrE ?ltr0n //.
by rewrite ler_nat ltnS homo_geidfun.
Qed.
(* --------------------------------------------------------------------- *)

(* The [->] half of Lemma 4.2 needs no hypothesis. *)
Lemma erhl_ierhl_ptL (D1 D2 : Distr M) (g : rcond) (r : \bar R) :
  (exists2 nu, scoupling D1 D2 nu & (espe nu (rstar g) <= r)%E) ->
  (psharp g D1 D2 <= r)%E.
Proof.
by case=> nu hnu hle; apply: (le_trans _ hle); exact: psharp_lbound.
Qed.

(* Lemma 4.2, pointwise in the pair of output distributions. *)
Lemma erhl_ierhl_pt (D1 D2 : Distr M) (g : rcond) (r : \bar R) :
  (forall m, (0 <= g m)%E) ->
  ((exists2 nu, scoupling D1 D2 nu & (espe nu (rstar g) <= r)%E)
   <-> (psharp g D1 D2 <= r)%E).
Proof.
move=> hg; split=> [h|h]; first exact: erhl_ierhl_ptL.
have [nu hnu heq] := psharp_attained D1 D2 g hg.
by exists nu => //; rewrite heq.
Qed.

Lemma erhl_ierhl ps f c d g :
  (forall m, (0 <= g m)%E) -> (erhl_ ps f c d g <-> ierhl_ ps f c d g).
Proof.
by move=> hg; split=> h m; apply/(erhl_ierhl_pt _ _ _ _ hg); exact: h.
Qed.

(* --------------------------------------------------------------------- *)
(* A [psharp] bound holding at every stage of a monotone approximation     *)
(* survives the limit.  This is what the paper calls "the sequence of      *)
(* star-couplings converges, in a certain sense, to a star-coupling"; it   *)
(* is the analogue of [esum_dlim_r] for the unary logic [ehl].             *)
(*                                                                       *)
(* Note it could not be proved by exhibiting a *monotone* family of        *)
(* star-couplings: they all have weight 1 ([dweight_scoupling]), so a      *)
(* nondecreasing family is constant.  Hence [scoupling_lim], which works   *)
(* with a merely convergent subsequence.  Used by [erhl_while] and         *)
(* [recursive_proc].                                                       *)
Lemma psharp_dlim (mu1 mu2 : nat -> Distr M) (g : rcond)
    (r : \bar R) :
  (forall n p, (n <= p)%N -> mu1 n <=1 mu1 p) ->
  (forall n p, (n <= p)%N -> mu2 n <=1 mu2 p) ->
  (forall m, (0 <= g m)%E) ->
  (forall n, (psharp g (mu1 n) (mu2 n) <= r)%E) ->
  (psharp g (dlim mu1) (dlim mu2) <= r)%E.
Proof.
move=> h1 h2 hg hb.
have hseq : forall n, exists nu, scoupling (mu1 n) (mu2 n) nu
              /\ (espe nu (rstar g) <= r)%E.
+ move=> n; have [nu hnu heq] := psharp_attained (mu1 n) (mu2 n) g hg.
  by exists nu; split=> //; rewrite heq; exact: hb.
have [nu hnuP] := choice hseq.
have [nu0 hnu0 [omega _ hle]] :=
  scoupling_lim mu1 mu2 (dlim mu1) (dlim mu2) nu g
    (fun n => proj1 (hnuP n)) (cvg_dstar_dlim mu1 h1) (cvg_dstar_dlim mu2 h2) hg.
apply: (@le_trans _ _ (espe nu0 (rstar g))); first exact: psharp_lbound.
apply: (le_trans hle); apply: limn_einf_le => n.
exact: (proj2 (hnuP (omega n))).
Qed.
(* --------------------------------------------------------------------- *)

End Validity.

(* ==================================================================== *)
(* Relational procedure contracts                                        *)
(*                                                                      *)
(* A contract relates a *pair* of procedures; one-sided calls relate a   *)
(* procedure to [skip].  Indexing by [option ident] covers both, with    *)
(* [None] standing for [skip].                                          *)
(* ==================================================================== *)
Section RContract.
Context {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg}.

Local Notation psi := (Y -> (@cmd_ R A B X Xg M Y)).
Local Notation rcond := (@rcond A B X Xg M).
Local Notation rcond2 := (@rcond2 A B X Xg M).
Local Notation cmd  := (@cmd_ R A B X Xg M Y).
Local Notation rmem  := (@rmem A B X Xg M).

Definition ocmd (o : option Y) : cmd :=
  if o is Some f then call f else skip.

Definition obody (ps : psi) (o : option Y) : cmd :=
  if o is Some f then ps f else skip.

Definition rclause : Type := rcond * rcond2.

Definition get_pre (an : rclause) := let: (pre, _) := an in pre.
Definition get_post (an : rclause) := let: (_, post) := an in post.

Definition rphi : Type := option Y -> option Y -> rclause.

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

(* The [(None, None)] clause of a contract relates [skip] to [skip], so it  *)
(* never degenerates to [dnull] and the induction in [recursive_proc] has   *)
(* no base case for it: it must be assumed.  A trivial obligation, and that *)
(* instance of [H_call] is subsumed by [H_Skip] anyway.                     *)
Definition rcl_skip_valid (cl : rphi) :=
  forall s : rmem, (get_post (cl None None) s s <= get_pre (cl None None) s)%E.

End RContract.
End erhl.

HB.mixin Record isRPhi {R: realType} {A B : codeType}
  {X Xg Y : eqType} {M : memType A B X Xg}
  (cl : @rphi R A B X Xg Y M) := {
  rpre_pos  : rcl_pre_pos  cl;
  rpost_pos : rcl_post_pos cl;
}.

HB.structure Definition RPhi
  {R: realType} {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg} :=
  {f of @isRPhi R A B X Xg Y M f}.

Lemma rpre_pos_rcl_empty
  {R: realType} {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg} :
  rcl_pre_pos (@rcl_empty R A B X Xg Y M).
Proof. by move=> ???; exact: leey. Qed.

Lemma rpost_pos_rcl_empty
  {R: realType} {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg}:
  rcl_post_pos (@rcl_empty R A B X Xg Y M).
Proof. by []. Qed.

HB.instance Definition _ {R: realType} {A B : codeType} {X Xg Y : countType}
  {M : memType A B X Xg} :=
  isRPhi.Build R A B X Xg Y M (@rcl_empty R A B X Xg Y M)
    rpre_pos_rcl_empty rpost_pos_rcl_empty.
