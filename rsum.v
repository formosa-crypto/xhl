(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import cardinality fsbigop.
From mathcomp.finmap    Require Import finmap.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import filter.
From mathcomp.analysis  Require Import esum counting_distr ereal.
From mathcomp.analysis  Require Import sequences normedtype topology.
(* [Require] without [Import]: [realsum] declares its own [summable],     *)
(* which would shadow [esum]'s [Notation summable := esummable].          *)
From mathcomp.experimental_reals Require discrete realsum.
                        Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

Section RSum.
Context {R : realType} {T : choiceType}.

Implicit Types (f g : T -> R).

Definition rsum f : R := fine (\esum_(x in [set: T]) (f x)%:E).

Lemma eq_rsum f g : f =1 g -> rsum f = rsum g.
Proof.
by move=> eq; rewrite /rsum; congr fine; apply: eq_esum => x _; rewrite eq.
Qed.

Lemma rsum0 : rsum (fun _ : T => 0) = 0.
Proof.
rewrite /rsum (eq_esum _ _ (fun _ => 0%E)); first by [].
by rewrite esum0.
Qed.

Lemma ge0_rsum f : (forall x, 0 <= f x) -> 0 <= rsum f.
Proof.
move=> f0; rewrite /rsum fine_ge0 //.
by apply: esum_ge0 => x _; rewrite lee_fin.
Qed.

Lemma rsumE f : esummable [set: T] (EFin \o f) ->
  (rsum f)%:E = \esum_(x in [set: T]) (f x)%:E.
Proof.
move=> sf; rewrite /rsum fineK //.
by apply: (esummable_esum_fin_num sf).
Qed.

Lemma esum_seq_le f z : (forall x, 0 <= f x) ->
  (forall J : seq T, uniq J -> \sum_(j <- J) f j <= z) ->
  (\esum_(x in [set: T]) (f x)%:E <= z%:E)%E.
Proof.
move=> f0 h; rewrite ge0_esum; first by move=> x _; rewrite lee_fin.
apply: ge_ereal_sup => _ [B [finB _] <-].
rewrite fsbig_finite; first exact: finB.
by rewrite sumEFin lee_fin; apply/h/fset_uniq.
Qed.

Lemma esummable_ge0_le f z : (forall x, 0 <= f x) ->
  (\esum_(x in [set: T]) (f x)%:E <= z%:E)%E ->
  esummable [set: T] (EFin \o f).
Proof.
move=> f0 h; rewrite esummableE.
rewrite (eq_esum _ _ (fun x => (f x)%:E)).
+ by move=> x _ /=; rewrite (ger0_norm (f0 x)).
rewrite ge0_fin_numE; first by apply: esum_ge0 => x _; rewrite lee_fin.
by apply: (le_lt_trans h); rewrite ltry.
Qed.

Lemma rsum_le f z : (forall x, 0 <= f x) ->
  (forall J : seq T, uniq J -> \sum_(j <- J) f j <= z) -> rsum f <= z.
Proof.
move=> f0 h; have key := esum_seq_le f0 h.
by rewrite -lee_fin rsumE // (esummable_ge0_le f0 key).
Qed.

Lemma gerfinseq_rsum f (r : seq T) : uniq r ->
  (forall x, 0 <= f x) -> esummable [set: T] (EFin \o f) ->
  \sum_(j <- r) f j <= rsum f.
Proof.
move=> uqr f0 sf; rewrite -lee_fin rsumE // -sumEFin.
apply: esum_ge; first by move=> x _; rewrite lee_fin.
have pr : perm_eq (fset_set ([set` r])%classic) r.
+ apply: uniq_perm; [exact: fset_uniq | exact: uqr |].
  move=> i; rewrite in_fset_set; first exact: finite_seq.
  by rewrite mem_setE.
exists ([set` r])%classic; first by split; [exact: finite_seq | by []].
rewrite fsbig_finite; first exact: finite_seq.
by rewrite (perm_big r pr).
Qed.

(* A single term is bounded by the whole sum. *)
Lemma le_rsum1 f x : (forall y, 0 <= f y) ->
  esummable [set: T] (EFin \o f) -> f x <= rsum f.
Proof.
move=> f0 sf; have h := gerfinseq_rsum (f := f) (r := [:: x]) isT f0 sf.
by rewrite big_seq1 in h.
Qed.

(* A non-negative family with vanishing sum vanishes. *)
Lemma rsum_eq0 f x : (forall y, 0 <= f y) ->
  esummable [set: T] (EFin \o f) -> rsum f = 0 -> f x = 0.
Proof.
move=> f0 sf h0; apply/eqP; rewrite eq_le f0 andbT -h0.
exact: le_rsum1.
Qed.

Lemma rsumZ f c : (forall x, 0 <= f x) ->
  rsum (fun x => c * f x) = c * rsum f.
Proof.
move=> f0; rewrite /rsum.
rewrite (eq_esum _ _ (fun x => (c%:E * (f x)%:E)%E)); first by move=> x _.
rewrite esumZ; first by move=> x _; rewrite lee_fin.
by rewrite fineMl.
Qed.

Lemma rsumB f g : (forall x, 0 <= g x <= f x) ->
  esummable [set: T] (EFin \o f) ->
  rsum (fun x => f x - g x) = rsum f - rsum g.
Proof.
move=> gf sf.
have sg : esummable [set: T] (EFin \o g).
+ apply: (le_esummable (g := EFin \o f)) => // x _.
  by rewrite /= !lee_fin; exact: gf x.
have ff := esummable_esum_fin_num sf.
have fg := esummable_esum_fin_num sg.
have E : \esum_(x in [set: T]) ((f x - g x)%:E)
       = ((\esum_(x in [set: T]) (f x)%:E)
          - (\esum_(x in [set: T]) (g x)%:E))%E.
+ rewrite -(esummable_esumB sf sg); apply: eq_esum => x _; exact: EFinB.
by rewrite /rsum E fineB.
Qed.

Lemma le_rsum f g : (forall x, 0 <= f x <= g x) ->
  esummable [set: T] (EFin \o g) -> rsum f <= rsum g.
Proof.
move=> fg sg; have sf : esummable [set: T] (EFin \o f).
  apply: (le_esummable (g := EFin \o g)) => // x _.
  by rewrite /= !lee_fin; have /andP[-> ->] := fg x.
rewrite -lee_fin !rsumE //; apply: le_esum => x _.
by rewrite lee_fin; have /andP[_ ->] := fg x.
Qed.

(* The converse of [gerfinseq_rsum]: [rsum] is approached from below by    *)
(* its finite partial sums.  This is the tightness input of               *)
(* [dlim_weight1] (erhl/erhl_stmt.v).                                     *)
Lemma rsum_approx f (e : R) : (forall x, 0 <= f x) ->
  esummable [set: T] (EFin \o f) -> 0 < e ->
  exists2 r : seq T, uniq r & rsum f - e < \sum_(x <- r) f x.
Proof.
move=> f0 sf e0.
have fin := esummable_esum_fin_num sf.
have E : \esum_(x in [set: T]) (f x)%:E
       = ereal_sup [set \sum_(x \in B) (f x)%:E | B in fsets [set: T]].
+ by rewrite ge0_esum // => x _; rewrite lee_fin.
have finsup : ereal_sup [set \sum_(x \in B) (f x)%:E | B in fsets [set: T]]
                \is a fin_num by rewrite -E.
have [x [B [finB _] <-] hlt] := ub_ereal_sup_adherent e0 finsup.
exists (fset_set B); first exact: fset_uniq.
rewrite -lte_fin EFinB (rsumE sf) E.
by rewrite -sumEFin -fsbig_finite.
Qed.

(* Pinching: below a summable bound, equal totals force equality.         *)
Lemma le_rsum_eqP f g : (forall x, 0 <= f x <= g x) ->
  esummable [set: T] (EFin \o g) -> rsum f = rsum g -> f =1 g.
Proof.
move=> fg sg eqfg x.
have h0 : forall y, 0 <= g y - f y.
+ by move=> y; rewrite subr_ge0; case/andP: (fg y).
have hle : forall y, g y - f y <= g y.
+ by move=> y; rewrite lerBlDr lerDl; case/andP: (fg y).
have sh : esummable [set: T] (EFin \o (fun y => g y - f y)).
+ by apply: (le_esummable (g := EFin \o g)) => // y _; rewrite /= !lee_fin h0 hle.
have hB : rsum (fun y => g y - f y) = 0.
+ by rewrite rsumB ?eqfg ?subrr // => y; rewrite (h0 y) /=; case/andP: (fg y).
have key : forall y, (@setT T) y -> (0 <= ((g y - f y)%:E))%E.
+ by move=> y _; rewrite lee_fin h0.
have hz : \esum_(y in [set: T]) ((g y - f y)%:E) = 0%E.
+ by rewrite -(rsumE sh) hB.
have h := @esum_eq0P R T setT (fun y => ((g y - f y)%:E)) key hz x I.
by move: h => /eqP; rewrite eqe subr_eq0 => /eqP; exact/esym.
Qed.

End RSum.

Lemma rsum_fin {R : realType} {I : finType} (f : I -> R) :
  (forall i, 0 <= f i) -> rsum f = \sum_i f i.
Proof.
move=> f0; rewrite /rsum (esum_fset finite_finset).
- by move=> i _; rewrite lee_fin.
by rewrite sum_eq_set sumEFin.
Qed.

Lemma rsum_finseq {R : realType} {T : choiceType} (f : T -> R) (r : seq T) :
  uniq r -> (forall x, 0 <= f x) -> (forall x, f x != 0 -> x \in r) ->
  rsum f = \sum_(x <- r) f x.
Proof.
move=> uqr f0 supp.
have fin : finite_set ([set` r])%classic by exact: finite_seq.
have pr : perm_eq (fset_set ([set` r])%classic) r.
+ apply: uniq_perm; [exact: fset_uniq | exact: uqr |].
  by move=> i; rewrite in_fset_set // mem_setE.
rewrite /rsum (esumID ([set` r])%classic [set: T]);
  first by move=> ? _; rewrite lee_fin.
rewrite !setTI.
have -> : \esum_(x in ~` ([set` r])%classic) ((f x)%:E) = 0%E.
+ apply: esum1 => x xNr.
  have -> : f x = 0; last by [].
  apply/eqP/negPn/negP => nz; apply: xNr.
  exact: supp nz.
rewrite adde0 esum_fset // ; first by move=> i _; rewrite lee_fin.
by rewrite fsbig_finite // (perm_big r pr) sumEFin.
Qed.

Lemma le1_rsum {R : realType} {T : choiceType} (mu : {distr T / R}) :
  rsum mu <= 1.
Proof.
by rewrite -lee_fin (rsumE (summable_mu mu)); exact: le1_mu.
Qed.

Lemma prE_rsum {R : realType} {T : choiceType}
    (mu : {distr T / R}) (E : pred T) :
  \P_[mu] E = rsum (fun x => (E x)%:R * mu x).
Proof. by []. Qed.

Lemma dweightE {R : realType} {T : choiceType} (d : {distr T / R}) :
  dweight d = rsum d.
Proof. by rewrite prE_rsum; apply: eq_rsum => x /=; rewrite mul1r. Qed.

Lemma dletE_rsum {R : realType} {A B : choiceType}
    (mu : {distr A / R}) (f : A -> {distr B / R}) y :
  (\dlet_(x <- mu) f x) y = rsum (fun x => mu x * f x y).
Proof. by rewrite dletE. Qed.

Lemma espE_rsum {R : realType} {T : choiceType}
    (mu : {distr T / R}) (g : T -> R) :
  \E_[mu] g = rsum (fun x => g x * mu x).
Proof. by []. Qed.

Lemma dmargin_comp {R : realType} {A B C : choiceType}
    (f : B -> C) (g : A -> B) (mu : {distr A / R}) :
  dmargin f (dmargin g mu) = dmargin (f \o g) mu.
Proof.
by apply/distr_eqP => z; exact: (dlet_dmargin mu g (fun y => dunit (f y)) z).
Qed.

(* Congruence for [dmargin] under a pointwise equality -- avoids needing    *)
(* functional extensionality to change the mapped function.                 *)
Lemma eq_dmargin {R : realType} {A B : choiceType}
    (k k' : A -> B) (mu : {distr A / R}) :
  k =1 k' -> dmargin k mu = dmargin k' mu.
Proof.
move=> e; apply/distr_eqP => z.
apply: (eq_in_dlet (mu := mu) (nu := mu)); last by [].
by move=> a _ y; rewrite e.
Qed.

Lemma dmargin_id {R : realType} {A : choiceType} (mu : {distr A / R}) :
  dmargin idfun mu = mu.
Proof. by apply/distr_eqP => z; exact: (dlet_dunit_id mu z). Qed.

Lemma pr_approx {R : realType} {T : choiceType} (mu : {distr T / R}) (e : R) :
  0 < e -> exists2 r : seq T, uniq r & dweight mu - e < \sum_(x <- r) mu x.
Proof.
move=> e0.
have -> : dweight mu = rsum mu.
+ by rewrite prE_rsum; apply: eq_rsum => x /=; rewrite mul1r.
by apply: rsum_approx; [exact: ge0_mu | exact: summable_mu | exact: e0].
Qed.

Lemma dfstE_rsum {R : realType} {T U : choiceType}
    (mu : {distr (T * U)%type / R}) x :
  dfst mu x = rsum (fun y => mu (x, y)).
Proof. by rewrite dfstE. Qed.

Lemma dsndE_rsum {R : realType} {T U : choiceType}
    (mu : {distr (T * U)%type / R}) y :
  dsnd mu y = rsum (fun x => mu (x, y)).
Proof. by rewrite dsndE. Qed.

Lemma dfstE_fin {R : realType} {T U : finType}
    (mu : {distr (T * U)%type / R}) x :
  dfst mu x = \sum_y mu (x, y).
Proof.
have -> : dfst mu x = rsum (fun y => mu (x, y)) by rewrite dfstE.
by rewrite rsum_fin // => ?; exact: ge0_mu.
Qed.

Lemma dsndE_fin {R : realType} {T U : finType}
    (mu : {distr (T * U)%type / R}) y :
  dsnd mu y = \sum_x mu (x, y).
Proof.
have -> : dsnd mu y = rsum (fun x => mu (x, y)) by rewrite dsndE.
by rewrite rsum_fin // => ?; exact: ge0_mu.
Qed.

Lemma rsum_image {R : realType} {T U : choiceType} (g : U -> T) (f : T -> R) :
  injective g -> (forall x, (forall u, g u <> x) -> f x = 0) ->
  (forall x, 0 <= f x) -> rsum f = rsum (f \o g).
Proof.
move=> ginj f0 fge0; rewrite /rsum; congr fine.
rewrite (esumID (g @` [set: U]) [set: T]); first by move=> ? _; rewrite lee_fin.
rewrite !setTI.
have -> : \esum_(x in ~` (g @` [set: U])) ((f x)%:E) = 0%E.
+ apply: esum1 => x xNim.
  have -> : f x = 0 by apply: f0 => u gu; apply: xNim; exists u.
  by [].
rewrite adde0.
by rewrite (esum_image [set: U] g (fun x => (f x)%:E)) // => x y _ _; exact: ginj.
Qed.

Lemma rsum_pair {R : realType} {T U : choiceType} (f : T * U -> R) :
  (forall x, 0 <= f x) ->
  (forall x, esummable [set: U] (EFin \o (fun y => f (x, y)))) ->
  rsum f = rsum (fun x => rsum (fun y => f (x, y))).
Proof.
move=> f0 sfx; rewrite /rsum; congr fine.
have dom : ([set: T] `*`` (fun _ : T => [set: U]))%classic
         = @setT (T * U)%type.
+ by rewrite predeqE => -[x y]; split.
transitivity (\esum_(x in [set: T]) \esum_(y in [set: U]) (f (x, y))%:E);
  last by apply: eq_esum => x _; rewrite -(rsumE (sfx x)).
rewrite (esum_esum (f := fun x y => (f (x, y))%:E));
  first by move=> ?? _ _; rewrite lee_fin.
by rewrite dom; apply: eq_esum => -[x y] _.
Qed.

Lemma rsum_pair_swap {R : realType} {T U : choiceType} (f : T * U -> R) :
  (forall x, 0 <= f x) ->
  (forall y, esummable [set: T] (EFin \o (fun x => f (x, y)))) ->
  rsum f = rsum (fun y => rsum (fun x => f (x, y))).
Proof.
move=> f0 sfy; rewrite /rsum; congr fine.
have dom : ([set: T] `*`` (fun _ : T => [set: U]))%classic
         = @setT (T * U)%type.
+ by rewrite predeqE => -[x y]; split.
transitivity (\esum_(y in [set: U]) \esum_(x in [set: T]) (f (x, y))%:E);
  last by apply: eq_esum => y _; rewrite -(rsumE (sfy y)).
rewrite -(@exchange_esum R T U [set: T] [set: U]
            (fun x y => (f (x, y))%:E)); first by move=> ??; rewrite lee_fin.
rewrite (esum_esum (f := fun x y => (f (x, y))%:E));
  first by move=> ?? _ _; rewrite lee_fin.
by rewrite dom; apply: eq_esum => -[x y] _.
Qed.

Lemma rsum_option {R : realType} {T : choiceType} (f : option T -> R) :
  esummable [set: option T] (EFin \o f) ->
  rsum f = rsum (f \o some) + f None.
Proof.
move=> sf; have sfs := esummable_option sf.
rewrite /rsum (esum_option sf) fineD //.
by apply: (esummable_esum_fin_num sfs).
Qed.

(* ==================================================================== *)
(* Dominated convergence for [rsum].                                     *)
(*                                                                      *)
(* mathcomp-analysis proves dominated convergence only for the Lebesgue  *)
(* integral (lebesgue_integral_dominated_convergence.v), over a          *)
(* [measurableType]; there is no [esum] counterpart.  But it follows from *)
(* [misc.esum_fatou] by the textbook argument: Fatou applied to the       *)
(* non-negative families [g + un] and [g - un].  Only the first is        *)
(* written out ([esum_dom_le]); the second is that same bound applied to  *)
(* [- un].                                                              *)
(* ==================================================================== *)

(* One half of dominated convergence: Fatou against the dominating [g].   *)
Lemma esum_dom_le {R : realType} {T : choiceType}
    (un : nat -> T -> R) (u g : T -> R) :
     (forall x, ((un^~ x) @ \oo --> u x)%classic)
  -> (forall n x, - g x <= un n x)
  -> esummable [set: T] (EFin \o g)
  -> esummable [set: T] (EFin \o u)
  -> (forall n, esummable [set: T] (EFin \o un n))
  -> (\esum_(x in [set: T]) (u x)%:E
        <= limn_einf (fun n => \esum_(x in [set: T]) (un n x)%:E))%E.
Proof.
move=> cvu bdn sg su sn.
pose Sg := (\esum_(x in [set: T]) (g x)%:E)%E.
pose Sn n := (\esum_(x in [set: T]) (un n x)%:E)%E.
have fSg : Sg \is a fin_num by exact: (esummable_esum_fin_num sg).
(* [g + h] splits off [Sg], for any summable [h] *)
have eD (h : T -> R) : esummable [set: T] (EFin \o h) ->
    (\esum_(x in [set: T]) ((g x + h x))%:E
   = Sg + \esum_(x in [set: T]) (h x)%:E)%E.
+ move=> sh; rewrite -(esummable_esumD sg sh).
  by apply: eq_esum => x _; rewrite /= EFinD.
have h0 : forall x n, (0 <= ((g x + un n x))%:E)%E.
+ move=> x n; rewrite lee_fin.
  have -> : g x + un n x = un n x - (- g x) by rewrite opprK addrC.
  by rewrite subr_ge0; exact: bdn.
have hlim x : limn_einf (fun n => ((g x + un n x))%:E) = ((g x + u x))%:E.
+ by apply: limn_einf_EFin; apply: cvgnD; [exact: cvg_cst | exact: cvu x].
have e1 : esum [set: T] (fun x => limn_einf (fun n => ((g x + un n x))%:E))
        = (Sg + \esum_(x in [set: T]) (u x)%:E)%E.
+ rewrite -(eD u su); apply: eq_esum => x _; exact: hlim x.
have e2 : (fun n => esum [set: T] (fun x => ((g x + un n x))%:E))
        =1 (fun n => (Sg + Sn n)%E).
+ by move=> n; exact: eD (un n) (sn n).
have := esum_fatou [set: T] h0.
by rewrite e1 (eq_limn_einf e2) (limn_einf_shift _ fSg) leeD2lE.
Qed.

Lemma rsum_dct {R : realType} {T : choiceType}
    (un : nat -> T -> R) (u g : T -> R) :
     (forall x, ((un^~ x) @ \oo --> u x)%classic)
  -> (forall n x, `|un n x| <= g x)
  -> esummable [set: T] (EFin \o g)
  -> esummable [set: T] (EFin \o u)
     /\ ((fun n => rsum (un n)) @ \oo --> rsum u)%classic.
Proof.
move=> cvu bd sg.
have ge0_g x : 0 <= g x by apply: le_trans (bd 0%N x); exact: normr_ge0.
have bdn n x : - g x <= un n x <= g x by rewrite -ler_norml; exact: bd.
(* [u] inherits the domination, hence the summability *)
have bdu x : `|u x| <= g x.
+ rewrite ler_norml; apply/andP; split.
  - apply: (cvgr_to_ge (cvu x)); apply: nearW => n.
    by case/andP: (bdn n x).
  apply: (cvgr_to_le (cvu x)); apply: nearW => n.
  by case/andP: (bdn n x).
have sm h : (forall x, `|h x| <= g x) -> esummable [set: T] (EFin \o h).
+ move=> hb; rewrite /esummable; apply: (le_lt_trans _ sg).
  apply: le_esum => x _ /=.
  by rewrite !lee_fin (le_trans (hb x)) // ler_norm.
have su := sm _ bdu.
have sn n := sm _ (bd n).
pose Su := (\esum_(x in [set: T]) (u x)%:E)%E.
pose Sn n := (\esum_(x in [set: T]) (un n x)%:E)%E.
have fSu : Su \is a fin_num by exact: (esummable_esum_fin_num su).
have low : (Su <= limn_einf Sn)%E.
+ by apply: (esum_dom_le cvu _ sg su sn) => n x; case/andP: (bdn n x).
(* the [limsup] half is [esum_dom_le] applied to [- un] *)
have upp : (limn_esup Sn <= Su)%E.
+ have cvuN x : (((fun n => - un n x)) @ \oo --> - u x)%classic.
  - by apply: cvgN; exact: cvu x.
  have suN : esummable [set: T] (EFin \o (fun x => - u x)).
  - by apply: sm => x; rewrite normrN; exact: bdu.
  have snN n : esummable [set: T] (EFin \o (fun x => - un n x)).
  - by apply: sm => x; rewrite normrN; exact: bd.
  have := esum_dom_le (un := fun n x => - un n x) (u := fun x => - u x)
                      (g := g) cvuN _ sg suN snN.
  rewrite (esummable_esumN su) -/Su.
  have eN : (fun n => \esum_(x in [set: T]) (- un n x)%:E)%E =1 (-%E \o Sn).
  - by move=> n; rewrite /Sn /= -(esummable_esumN (sn n));
       apply: eq_esum => x _; rewrite /= EFinN.
  rewrite (eq_limn_einf eN) limn_einfN => h.
  rewrite -leeN2; apply: h => n x.
  by rewrite lerN2; case/andP: (bdn n x).
split=> //.
have cvS : (Sn @ \oo --> Su)%classic by exact: (cvg_limn_einf_esup upp low).
rewrite /rsum -/Su.
have -> : (fun n => fine (\esum_(x in [set: T]) (un n x)%:E)%E) = fine \o Sn by [].
by apply: fine_cvg; rewrite -(fineK fSu) in cvS.
Qed.

(* ==================================================================== *)
(* Sequential compactness of [{distr T / R}] for the topology of         *)
(* pointwise convergence, for an *arbitrary* [T : choiceType].           *)
(*                                                                      *)
(* Cantor's diagonal ([misc.diag_cvg]) only extracts a subsequence       *)
(* convergent at countably many coordinates, and [cmem] -- a dependent   *)
(* product over all of [IhbType.type] -- is very far from countable.     *)
(* What saves the day is that a distribution is summable, hence supported *)
(* on a countable set ([realsum.summable_countn0]); the union over [n] of *)
(* those supports is still countable ([discrete.cunion_countable]), and   *)
(* off it every [mu n] is identically [0], so the sequence converges      *)
(* there for free.                                                      *)
(*                                                                      *)
(* [discrete.countable E] is a *data* (a [pcancel] pair on [[psub E]]),  *)
(* not a Prop, which is what lets [diag_cvg] be applied at [nat] with    *)
(* [runpickle] as the decoding -- no [countType] instance on a           *)
(* proof-local subtype needs to be declared.                            *)
(* ==================================================================== *)
Section DCompact.
Context {R : realType} {T : choiceType}.

Lemma dcompact (mu : nat -> {distr T / R}) :
  { om : nat -> nat
  | {homo om : x y / (x < y)%N}
  & forall x, cvgn (fun n => mu (om n) x) }.
Proof.
pose E n : pred T := [pred x | mu n x != 0].
have cS : discrete.countable [pred x | `[< exists i, x \in E i >]].
+ apply: discrete.cunion_countable => n.
  apply: realsum.summable_countn0.
  by apply/realsum.esum_summableP; exact: summable_mu.
set S := [pred x | `[< exists i, x \in E i >]].
pose v (n k : nat) : R :=
  if discrete.runpickle cS k is Some s then mu n (discrete.rsval s) else 0.
have bv : forall n k, `|v n k| <= 1.
+ move=> n k; rewrite /v; case: (discrete.runpickle cS k) => [s|]; last first.
  - by rewrite normr0.
  by rewrite ger0_norm ?ge0_mu // le1_mu1.
case: (diag_cvg (u := v) (M := 1) bv) => om homo_om cvg_v.
exists om => // x.
case/boolP: (x \in S) => [xS|xNS]; last first.
+ (* [x] is outside every support: the sequence is constantly [0].       *)
  have hz : forall n, mu (om n) x = 0.
  - move=> n; apply/eqP; move: xNS; apply: contraNT => hne.
    by rewrite inE /=; apply/asboolP; exists (om n); rewrite inE.
  apply: (@cvgn_eq _ _ (fun=> 0)); first by move=> n; rewrite hz.
  exact: is_cvg_cst.
pose s : discrete.pred_sub S := discrete.PSubSub xS.
apply: (@cvgn_eq _ _ (fun n => v (om n) (discrete.rpickle cS s))).
+ by move=> n; rewrite /v (discrete.rpickleK cS s).
exact: cvg_v.
Qed.

(* An increasing sequence of finite sets exhausting the support.  Same    *)
(* countability input as [dcompact]: this is the [choiceType] replacement  *)
(* for [strassen.v]'s [E i := seq_fset (pmap unpickle (iota 0 i))], which  *)
(* needed a [countType].  Note it only covers the *support* -- off it      *)
(* every truncation agrees with [mu] anyway, both being [0].               *)
Lemma dsupp_exhaust (mu : {distr T / R}) :
  { c : nat -> {fset T} |
    forall x, x \in dinsupp mu -> exists N, forall n, (N <= n)%N -> x \in c n }.
Proof.
have cS : discrete.countable [pred x | mu x != 0].
+ by apply: realsum.summable_countn0; apply/realsum.esum_summableP; exact: summable_mu.
exists (fun i => seq_fset tt
  (pmap (fun k => omap (fun s => discrete.rsval s) (discrete.runpickle cS k))
        (iota 0 i))).
move=> x hx; pose s : discrete.pred_sub [pred y | mu y != 0] :=
  discrete.PSubSub hx.
exists (discrete.rpickle cS s).+1 => n hn.
rewrite seq_fsetE mem_pmap; apply/mapP.
exists (discrete.rpickle cS s); last by rewrite (discrete.rpickleK cS s).
by rewrite mem_iota leq0n add0n.
Qed.

End DCompact.

(* Two families, one subsequence -- the [choiceType] counterpart of        *)
(* [strassen.strcvg2].                                                    *)
Lemma dcompact2 {R : realType} {T U : choiceType}
    (mu1 : nat -> {distr T / R}) (mu2 : nat -> {distr U / R}) :
  { om : nat -> nat | {homo om : x y / (x < y)%N} &
    [/\ forall x, cvgn (fun n => mu1 (om n) x)
      & forall y, cvgn (fun n => mu2 (om n) y) ] }.
Proof.
case: (dcompact mu1) => om1 mono1 cvg1.
case: (dcompact (mu2 \o om1)) => om2 mono2 cvg2.
(exists (om1 \o om2); last split) => // [m n|x].
+ by move/mono2/mono1.
by apply/(cvgn_subseq (u := (mu1 \o om1)^~ x) (s := om2)).
Qed.

(* ==================================================================== *)
(* Tightness: a pointwise limit of distributions with full, converging   *)
(* marginals keeps all of its mass.                                      *)
(*                                                                      *)
(* Fatou alone would only give [dfst (dlim nu) <=1 P]; mass genuinely    *)
(* can escape under a pointwise limit, and what rules that out here is   *)
(* that [P] and [Q] have weight 1.  The argument is the standard one:    *)
(* approximate [P] and [Q] by finite partial sums ([pr_approx]), observe *)
(* that inclusion/exclusion bounds [nu n] from below on the product of   *)
(* the two finite sets *uniformly in [n]*, and pass to the limit there   *)
(* -- a finite sum, so no exchange of limit and infinite sum is needed.  *)
(* ==================================================================== *)
Section PrSeq.
Context {R : realType} {A B : choiceType}.

Lemma pr_fstseq (mu : {distr (A * B)%type / R}) (F : seq A) :
  uniq F -> \P_[mu] [pred p | p.1 \in F] = \sum_(a <- F) dfst mu a.
Proof.
move=> uF; rewrite -(pr_mem _ uF) (pr_dmargin _ fst).
by apply/eq_pr => p; rewrite !inE.
Qed.

Lemma pr_sndseq (mu : {distr (A * B)%type / R}) (G : seq B) :
  uniq G -> \P_[mu] [pred p | p.2 \in G] = \sum_(b <- G) dsnd mu b.
Proof.
move=> uG; rewrite -(pr_mem _ uG) (pr_dmargin _ snd).
by apply/eq_pr => p; rewrite !inE.
Qed.

(* The pointwise-convergence hypothesis cannot be weakened to a bound on  *)
(* [limn_einf]: [liminf] is superadditive, so summing it gives the wrong  *)
(* inequality.                                                           *)
Lemma dlim_weight1 (nu : nat -> {distr (A * B)%type / R})
    (P : {distr A / R}) (Q : {distr B / R}) :
  dweight P = 1 -> dweight Q = 1 ->
  (forall a, ((fun n => dfst (nu n) a) @ \oo --> P a)%classic) ->
  (forall b, ((fun n => dsnd (nu n) b) @ \oo --> Q b)%classic) ->
  (forall p, cvgn (fun n => nu n p)) ->
  dweight (dlim nu) = 1.
Proof.
move=> wP wQ cP cQ cnu.
apply/eqP; rewrite eq_le le1_pr /=; apply/ler_addgt0Pr => e e0.
have e20 : 0 < e / 2 by rewrite divr_gt0.
have [F uF hF] := pr_approx P e20.
have [G uG hG] := pr_approx Q e20.
rewrite wP in hF; rewrite wQ in hG.
pose FG := [seq (a, b) | a <- F, b <- G].
have uFG : uniq FG := uniq_allpairs_pair uF uG.
(* inclusion/exclusion, uniformly in [n] *)
have key : forall n,
    (\sum_(a <- F) dfst (nu n) a) + (\sum_(b <- G) dsnd (nu n) b) - 1
      <= \sum_(p <- FG) nu n p.
+ move=> n; rewrite -(pr_fstseq _ uF) -(pr_sndseq _ uG) -(pr_mem _ uFG).
  have -> : \P_[nu n] [pred x | x \in FG]
          = \P_[nu n] [predI [pred p | p.1 \in F] & [pred p | p.2 \in G]].
  + by apply: eq_pr => p; rewrite !inE /= mem_allpairs_pair.
  by rewrite pr_and lerD2l lerN2 le1_pr.
(* pass to the limit inside the finite sum *)
have cvgL : ((fun n => \sum_(p <- FG) nu n p) @ \oo
               --> \sum_(p <- FG) dlim nu p)%classic.
+ by apply: cvg_bigseq => p; exact: cvg_dlim_pt.
have cvgR : ((fun n => (\sum_(a <- F) dfst (nu n) a)
                     + (\sum_(b <- G) dsnd (nu n) b) - 1) @ \oo
               --> (\sum_(a <- F) P a) + (\sum_(b <- G) Q b) - 1)%classic.
+ apply: cvgnB; last exact: cvg_cst.
  by apply: cvgnD; apply: cvg_bigseq.
have nkey : (\forall n \near \oo,
    (\sum_(a <- F) dfst (nu n) a) + (\sum_(b <- G) dsnd (nu n) b) - 1
      <= \sum_(p <- FG) nu n p)%classic.
+ by apply: nearW; exact: key.
have step : (\sum_(a <- F) P a) + (\sum_(b <- G) Q b) - 1
              <= \sum_(p <- FG) dlim nu p.
+ exact: (ler_cvg_to cvgR cvgL nkey).
have hlast : \sum_(p <- FG) dlim nu p <= dweight (dlim nu).
+ by rewrite -(pr_mem _ uFG); apply: subset_pr => q; rewrite !inE.
have hsum : (1 - e / 2) + (1 - e / 2) = 1 + (1 - e).
+ by rewrite addrACA -opprD -splitr addrA.
apply: ltW; rewrite -ltrBlDr.
apply: (lt_le_trans _ (le_trans step hlast)).
rewrite ltrBrDr addrC -hsum.
exact: ltrD hF hG.
Qed.

(* -------------------------------------------------------------------- *)
(* A finite partial sum of a section of a joint distribution is bounded   *)
(* by the corresponding marginal.                                        *)
Lemma sum_seq_le_dfst (mu : {distr (A * B)%type / R}) (a : A) (J : seq B) :
  uniq J -> \sum_(b <- J) mu (a, b) <= dfst mu a.
Proof.
move=> uJ.
have uP : uniq [seq (a, b) | b <- J].
+ by rewrite map_inj_uniq // => x y [].
rewrite -(big_map (fun b => (a, b)) predT mu) -(pr_mem _ uP).
have -> : dfst mu a = \P_[mu] [pred p | p.1 \in pred1 a].
+ by rewrite -(pr_dmargin _ fst) -pr_pred1.
by apply: subset_pr => p; rewrite !inE => /mapP[b _ ->]; rewrite /= eqxx.
Qed.

Lemma sum_seq_le_dsnd (mu : {distr (A * B)%type / R}) (b : B) (J : seq A) :
  uniq J -> \sum_(a <- J) mu (a, b) <= dsnd mu b.
Proof.
move=> uJ.
have uP : uniq [seq (a, b) | a <- J].
+ by rewrite map_inj_uniq // => x y [].
rewrite -(big_map (fun a => (a, b)) predT mu) -(pr_mem _ uP).
have -> : dsnd mu b = \P_[mu] [pred p | p.2 \in pred1 b].
+ by rewrite -(pr_dmargin _ snd) -pr_pred1.
by apply: subset_pr => p; rewrite !inE => /mapP[a _ ->]; rewrite /= eqxx.
Qed.

Lemma dweight_dfst (nu : {distr (A * B)%type / R}) :
  dweight (dfst nu) = dweight nu.
Proof. by rewrite (pr_dmargin predT fst nu) (eq_pr (B := predT)). Qed.

Lemma dweight_dsnd (nu : {distr (A * B)%type / R}) :
  dweight (dsnd nu) = dweight nu.
Proof. by rewrite (pr_dmargin predT snd nu) (eq_pr (B := predT)). Qed.

End PrSeq.
