(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Local Notation "x @ i" := (x 0 i) (at level 20).
Local Notation "x @^ i" := (x i 0) (at level 20).

Declare Scope syntax_scope.

(* -------------------------------------------------------------------- *)
Section LPDef.
Context {F : realFieldType} (n p : nat).

Context (A : 'M[F]_(n,p)) (b : 'rV[F]_p) (C : 'cV[F]_n).

Implicit Types (x : 'rV[F]_n).

(* -------------------------------------------------------------------- *)
Definition lpcost x : F := ((x *m C) 0 0).

Lemma lpcost_is_linear : scalar lpcost.
Proof.
by move=> a u v; rewrite /lpcost mulmxDl -scalemxAl 2!mxE.
Qed.

(* HB.instance Definition _ := GRing.isScalable.Build F _ _ _ *:%R lpcost lpcost_is_linear. *)

Canonical lpcost_additive := isAdditive.Build lpcost_is_linear.
Canonical lpcost_linear := AddLinear lpcost_is_linear.

(* -------------------------------------------------------------------- *)
Definition lpset x :=
  [forall i, 0 <= x @ i] && (x *m A == b).

Lemma lpsetP x :
  reflect ((forall i, 0 <= x @ i) /\ x *m A = b) (lpset x).
Proof. apply: (iffP andP).
+ by case=> /forallP ? /eqP.
+ by case=> h1 h2; split; [apply/forallP | apply/eqP].
Qed.

Lemma lpset_ge0 x : lpset x -> forall i, 0 <= x @ i.
Proof. by case/lpsetP. Qed.

Lemma lpset_sol x : lpset x -> x *m A = b.
Proof. by case/lpsetP. Qed.

(* -------------------------------------------------------------------- *)
Definition lpconvex (S : 'rV[F]_n -> Prop) :=
  forall x y, S x -> S y ->
    forall k : F, 0 <= k <= 1 -> S (k *: x + (1 - k) *: y).

(* -------------------------------------------------------------------- *)
Definition lpcvxcb (S : 'rV[F]_n -> Prop) (x : 'rV[F]_n) :=
  exists k (c : 'I_k -> F) (A : 'I_k -> 'rV[F]_n),
    [/\ x = \sum_i c i *: A i
      , \sum_i c i = 1
      , forall i, 0 <= c i
      & forall i, S (A i)].

(* -------------------------------------------------------------------- *)
CoInductive lpcvxcb_spec S x : Prop :=
| LPCvxCb k (c : 'I_k -> F) (A : 'I_k -> 'rV[F]_n) of
      (x = \sum_i c i *: A i)
    & (\sum_i c i = 1)
    & (forall i, 0 <= c i)
    & forall i, S (A i).

(* -------------------------------------------------------------------- *)
Lemma lpcvxcbP S x : lpcvxcb S x <-> lpcvxcb_spec S x.
Proof. split.
+ by case=> [k] [c] [G] [-> h1 h2 h3]; exists k c G.
+ by case=> k c G -> h1 h2 h3; exists k, c, G; split.
Qed.

(* -------------------------------------------------------------------- *)
Definition lpextrem x := lpset x /\
  forall x1 x2 k,
      0 < k < 1 -> lpset x1 -> lpset x2
   -> x = k *: x1 + (1 - k) *: x2
   -> x1 = x2.

(* -------------------------------------------------------------------- *)
Lemma lpextrem_sol x : lpextrem x -> lpset x.
Proof. by case. Qed.

(* -------------------------------------------------------------------- *)
Lemma lpextrem_ext x : lpextrem x ->
  forall x1 x2 k,
      0 < k < 1 -> lpset x1 -> lpset x2
   -> x = k *: x1 + (1 - k) *: x2
   -> x1 = x2.
Proof. by case. Qed.

(* -------------------------------------------------------------------- *)
Definition lpbounded :=
  exists M : F, forall x, lpset x -> forall i, x @ i < M.

(* -------------------------------------------------------------------- *)
Definition lpbasei x :=
  [seq i <- enum 'I_n | x @ i != 0].

(* -------------------------------------------------------------------- *)
Definition lpbase x :=
  [seq row i A | i <- lpbasei x].

(* -------------------------------------------------------------------- *)
Lemma lpbaseiP x i : reflect (x @ i <> 0) (i \in lpbasei x).
Proof. by rewrite mem_filter mem_enum andbT; apply/(iffP idP) => /eqP. Qed.

(* -------------------------------------------------------------------- *)
Lemma lpbaseiPn x i : i \notin lpbasei x <-> x @ i = 0.
Proof. split.
+ by rewrite mem_filter mem_enum andbT negbK (rwP eqP).
+ by move=> z_xi; rewrite mem_filter z_xi eqxx mem_enum.
Qed.

(* -------------------------------------------------------------------- *)
Lemma uniq_lpbasei x : uniq (lpbasei x).
Proof. by apply/filter_uniq/enum_uniq. Qed.

(* -------------------------------------------------------------------- *)
Lemma cvxcb_mem (S : 'rV[F]_n -> Prop) x : S x -> lpcvxcb S x.
Proof.
exists 1%N, (fun i => 1), (fun u => x); split=> //.
- by rewrite big_const_ord iterS addr0 scale1r.
- by rewrite big_const_ord iterS addr0.
(* - by rewrite ltW // ltr01. *)
Qed.

(* -------------------------------------------------------------------- *)
Lemma cvx_cvxcb S : lpconvex (lpcvxcb S).
Proof.
move=> x1 x2 /lpcvxcbP[k1 c1 A1 -> sm1 ge01 SA1].
move=> /lpcvxcbP[k2 c2 A2 -> sm2 ge02 SA2] k /andP[ge0_k le1_k].
pose c := fsplit (fun i => k * c1 i) (fun i => (1 - k) * c2 i).
pose G := fsplit (fun i => A1 i) (fun i => A2 i).
pose Z1 i : 'rV[F]_n := (k * c1 i) *: A1 i.
pose Z2 i : 'rV[F]_n := ((1 - k) * c2 i) *: A2 i.
apply/lpcvxcbP; exists _ c G.
- rewrite !scaler_sumr [RHS](eq_bigr (fsplit Z1 Z2)).
  + by move=> i _; rewrite /c /G /fsplit; case: split.
  by rewrite big_fsplit /= /Z1 /Z2; congr +%R;
    apply/eq_bigr => i _; rewrite scalerA.
- rewrite big_fsplit /= -!mulr_sumr !(sm1, sm2) !mulr1.
  by rewrite addrCA subrr addr0.
- move=> i; rewrite /c /fsplit; case: split => j.
  + by rewrite mulr_ge0.
  + by rewrite mulr_ge0 // subr_ge0.
- by move=> i; rewrite /G /fsplit; case: split => j.
Qed.
End LPDef.

(* ==================================================================== *)
Section LP.

Context {F : realFieldType} (n' p' : nat).

Local Notation n := n'.+1.
Local Notation p := p'.+1.

Context (A : 'M[F]_(n,p)) (b : 'rV[F]_p) (C : 'cV[F]_n).

Local Notation lpbase     := (lpbase A).
Local Notation lpbounded  := (lpbounded A b).
Local Notation lpset x    := (lpset A b x).
Local Notation lpextrem   := (fun x => lpextrem A b x).
Local Notation lpcost     := (lpcost C).

Implicit Types (x : 'rV[F]_n).

Lemma free_lpbaseP x (μ : 'I_n -> F) :
     free (lpbase x)
  -> (forall i : 'I_n, i \notin lpbasei x -> μ i = 0)
  -> \sum_j (μ j *: row j A) = 0
  -> forall i, μ i = 0.
Proof.
move=> frx zμ; rewrite (bigID (mem (lpbasei x))) /= addrC big1.
+ by move=> i /zμ ->; rewrite scale0r.
rewrite add0r -big_uniq ?uniq_lpbasei //= => h.
move: frx; rewrite -[lpbase x]in_tupleE => /freeP.
have eqp: size (lpbase x) = size (lpbasei x) by rewrite size_map.
pose k j := μ (tnth (in_tuple (lpbasei x)) (cast_ord eqp j)).
move/(_ k) => zk i; case/boolP: (i \in lpbasei x); last by apply/zμ.
case/seq_tnthP=> [[j ltji] ->]; rewrite (tnth_nth 0) /=.
have ltj: (j < size (lpbase x))%N by rewrite eqp.
have := zk _ (Ordinal ltj); rewrite /k (tnth_nth 0); apply.
pose G i : 'rV[F]_p := μ (lpbasei x)`_i *: row (lpbasei x)`_i A.
rewrite (eq_bigr (G \o val)) => /= [z _|].
+ by rewrite {}/G (tnth_nth 0) (nth_map 0) // -eqp.
rewrite -(big_mkord xpredT G) {}/G eqp.
by rewrite -(big_nth 0 xpredT (fun i => μ i *: row i A)).
Qed.

(* -------------------------------------------------------------------- *)
Lemma free_lpbasePn x :
  ~~ free (lpbase x) -> exists (μ : 'rV[F]_n),
    [/\ \sum_(i < n) μ @ i *: row i A = 0
      , forall i, i \notin lpbasei x -> μ @ i = 0
      & μ != 0].
Proof.
rewrite -[lpbase _]in_tupleE freeNE => /existsP[j /coord_span /=].
have ltj: (j < size (lpbasei x))%N by move: j; rewrite /= size_map.
set s := drop_tuple _ _; set e := lpbase x.
pose X := [seq coord s i e`_j | i <- enum 'I_(size e - j.+1)].
pose G i : 'rV[F]_p := ((nseq j.+1 0) ++ X)`_i *: e`_i.
rewrite (eq_bigr ((G \o (fun i => i + j.+1)%N) \o val)) => [/= i _|].
+ rewrite {}/G [(i+_)%N]addnC -!nth_drop drop_size_cat ?size_nseq //.
  by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
rewrite -(big_mkord xpredT) /= -(big_addn _ _ _ xpredT) add0n => ejE.
exists (\row_i (nseq j 0 ++ (-1) :: X)`_(index i (lpbasei x))); split.
+ rewrite (bigID (fun i => i \in lpbasei x)) /= addrC big1 ?add0r.
  - move=> i ix; rewrite !mxE nth_default ?scale0r //.
    rewrite /X /= size_cat size_nseq /= -addSnnS !size_map.
    by rewrite size_enum_ord subnKC // leqNgt size_map index_mem.
  rewrite -big_uniq ?uniq_lpbasei //= (big_nth 0).
  pose H i := (nseq j 0 ++ (-1) :: X)`_i *: e`_i.
  rewrite (eq_big_nat _ _ (F2 := H)) {}/H => /= [i lti|].
  - by rewrite !mxE index_uniq ?uniq_lpbasei // /e (nth_map 0).
  rewrite (big_cat_nat _ (n := j.+1)) //= big_nat_recr //=.
  rewrite big_nat big1 ?add0r => /= [i lt_ij|].
  - by rewrite nth_cat size_nseq lt_ij nth_nseq lt_ij scale0r.
  rewrite nth_cat size_nseq ltnn subnn /= scaleN1r ejE addrC.
  rewrite {4}[size e]size_map -sumrB big_nat big1 //.
  move=> i /andP[lt_ji lt_i]; rewrite /G !nth_cat !size_nseq.
  rewrite ![(i < _)%N]ltnNge ltnW // lt_ji /= subnS.
  move: lt_ji; rewrite -subn_gt0; case: (i - j)%N => //=.
  by move=> n _; rewrite subrr.
+ move=> i ix; rewrite !mxE nth_default // size_cat size_nseq /=.
  rewrite -addSnnS /X /= size_map size_enum_ord subnKC //.
  by rewrite leqNgt size_map index_mem.
+ apply/eqP/rowP => /(_ (lpbasei x)`_j); rewrite !mxE.
  rewrite index_uniq ?uniq_lpbasei // nth_cat size_nseq.
  by rewrite ltnn subnn /= (rwP eqP) oppr_eq0 oner_eq0.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma L1 (μ : 'rV[F]_n) x :
     lpbounded -> lpset x -> μ != 0
  -> (forall i : 'I_n, i \notin lpbasei x -> μ @ i = 0)
  -> \sum_i μ @ i *: row i A = 0
  -> exists2 ij, 0 < μ @ ij.1 & 0 > μ @ ij.2.
Proof.
case=> M ltM solx nzμ basμ bdμ; move/eqP/rowP/eqfunP: nzμ.
case/forallPn=> /= i; rewrite !mxE => /negP nz_μi.
wlog: i μ basμ bdμ nz_μi / 0 < μ @ i => [wlog|].
+ case/lt_total/orP: (nz_μi) => [lt0_μi|]; last by apply/wlog.
  case: (wlog i (- μ)); rewrite ?mxE ?(oppr_cp0, oppr_eq0) //.
  * by move=> j hj; rewrite !mxE (rwP eqP) oppr_eq0 basμ.
  * rewrite -[RHS]oppr0 -[X in _=-X]bdμ (rwP eqP) -addr_eq0.
    rewrite -big_split big1 //= => j _; rewrite !mxE.
    by rewrite scaleNr addNr.
  by case=> j1 j2 /=; rewrite !mxE !oppr_cp0; exists (j2, j1).
move=> gt0_μi; case/boolP: [forall i, 0 <= μ @ i]; last first.
+ by case/forallPn=> /= j /negP; rewrite -ltNge; exists (i, j).
move/forallP=> /= ge0_μ; have ix: i \in lpbasei x.
+ by apply/contraLR: nz_μi => /basμ ->; rewrite negbK.
have lp_xDkμ: forall k, 0 <= k -> lpset (x + k *: μ).
+ move=> k ge0_k; apply/lpsetP; split.
  * move=> j; rewrite !mxE addr_ge0 1?(lpset_ge0, mulr_ge0) //.
    by apply/(lpset_ge0 solx).
  rewrite mulmxDl (lpset_sol solx) // -scalemxAl mulmx_sum_row.
  by rewrite bdμ scaler0 addr0.
have: 0 <= M / μ@i; first rewrite divr_ge0 //.
+ by apply/ltW/(le_lt_trans (lpset_ge0 solx i))/ltM.
move/lp_xDkμ => {lp_xDkμ} /ltM/(_ i); rewrite !mxE.
by rewrite -mulrA mulVf // mulr1 gtr_addr ltNge (lpset_ge0 solx).
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma L2 (μ : 'rV[F]_n) x :
     lpbounded -> lpset x -> μ != 0
  -> (forall i : 'I_n, i \notin lpbasei x -> μ @ i = 0)
  -> \sum_i μ @ i *: row i A = 0
  -> exists (t : F) (i : 'I_n), [/\
       0 < t, lpset (x - t *: μ),
       x @ i != 0 & (x - t *: μ) @ i == 0].
Proof.
move=> bd lpx nzμ basμ bdμ; case: (@L1 μ x) => //.
case=> i _ /= gt0_μi _; have hp: exists i, 0 < μ @ i by exists i.
pose k : 'I_n := arg_minr (fun i => x @ i / μ @ i) hp.
pose t : F := x @ k / μ @ k; exists t, k.
rewrite /t /k; case: arg_minrP=> {t k gt0_μi hp} /=.
move=> k gt0_μk bdk; split; rewrite ?mxE.
+ rewrite divr_gt0 // lt_neqAle (lpset_ge0 lpx) // andbT.
  rewrite eq_sym; apply/eqP/lpbaseiPn => /basμ.
  by move/eqP; rewrite gt_eqF.
+ apply/lpsetP; split => [j|]; rewrite ?mxE.
  * rewrite subr_ge0; case: (ltrP 0 (μ @ j)).
    - by move=> gt0_μj; rewrite -ler_pdivl_mulr // bdk.
    move=> le0_μj; apply/(@le_trans _ _ 0)/(lpset_ge0 lpx) => //.
    by rewrite mulr_ge0_le0 // divr_ge0 ?(lpset_ge0 lpx) ?ltW.
  * rewrite mulmxBl (lpset_sol lpx) // -scalemxAl mulmx_sum_row.
    by rewrite bdμ scaler0 subr0.
+ by apply/eqP => /lpbaseiPn /basμ /eqP; rewrite gt_eqF.
+ rewrite -mulrA mulVf; first by rewrite gt_eqF.
  by rewrite mulr1 subrr.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma L3 x :
  lpbounded -> lpset x -> ~~ free (lpbase x) ->
    exists x1 x2 k, [/\
      0 < k < 1, x1 != x2, x = k *: x1 + (1 - k) *: x2,
      [/\ lpset x1 & lpset x2] &
         [/\ {subset lpbasei x1 ++ lpbasei x2 <= lpbasei x}
           , exists2 e : 'I_n, e \in lpbasei x & e \notin lpbasei x1
           & exists2 e : 'I_n, e \in lpbasei x & e \notin lpbasei x2]].
Proof.
move=> bd lpx /free_lpbasePn [μ /= [bdμ basμ nzμ]].
pose y k : 'rV[F]_n := x + k *: μ.
have h j: {subset lpbasei (y j) <= lpbasei x}.
+ move=> /= z /lpbaseiP; rewrite {}/y !mxE.
  case/boolP: (z \in lpbasei x) => // h.
  by rewrite basμ // mulr0 addr0; move/lpbaseiPn: h.
case: (@L2 μ x) => // t1 [i1 [ge0_t1 lpx1 /eqP nz_xi1 z_x1]].
have {z_x1} st1: i1 \notin lpbasei (y (-t1)).
+ by apply/lpbaseiPn; rewrite /y scaleNr (eqP z_x1).
case: (@L2 (- μ) x) => //; last move=> t2 [i2 []].
+ by rewrite oppr_eq0.
+ by move=> i /basμ; rewrite !mxE => ->; rewrite oppr0.
+ rewrite -[RHS]oppr0 -[0 in RHS]bdμ (rwP eqP).
  rewrite -addr_eq0 -big_split /= big1 // => i _.
  by rewrite !mxE scaleNr addNr.
rewrite !scalerN !opprK => ge0_t2 lpx2 /eqP nz_xi2 z_x2.
have {z_x2} st2: i2 \notin lpbasei (y t2).
+ by apply/lpbaseiPn; rewrite /y (eqP z_x2).
pose k := t2 / (t1 + t2); have in01_k: 0 < k < 1.
+ rewrite divr_gt0 1?addr_gt0 //= ltr_pdivr_mulr ?addr_gt0 //.
  by rewrite mul1r ltr_addr.
have xE: x = k *: (x - t1 *: μ) + (1 - k) *: (x + t2 *: μ).
+ rewrite !(scalerBr, scalerDr) addrACA -scalerDl.
  rewrite [k + _]addrCA subrr addr0 scale1r -!scaleNr.
  rewrite !scalerA -scalerDl; set l := (X in X *: _).
  suff ->: l = 0 by rewrite scale0r addr0.
  rewrite {}/l {in01_k}/k -mulNr mulrAC -[1]divr1.
  rewrite addf_div ?oner_neq0 // ?gt_eqF ?addr_gt0 //.
  rewrite !(mul1r, mulr1) [X in _ + X]mulrAC -mulrDl.
  by rewrite -addrA subrr addr0 mulNr [t2*_]mulrC addNr mul0r.
exists (x - t1 *: μ), (x + t2 *: μ), k; split=> //; last first.
+ split.
  * by move=> e; rewrite mem_cat => /orP[]; rewrite -?scaleNr => /h.
  * by exists i1; rewrite -?scaleNr //; apply/lpbaseiP.
  * by exists i2 => //; apply/lpbaseiP.
rewrite -subr_eq0 opprD addrACA subrr add0r -scaleNr.
rewrite -scalerBl scaler_eq0 (negbTE nzμ) orbF.
by rewrite -opprD oppr_eq0 gt_eqF // addr_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lpbase_freeP x : lpset x -> free (lpbase x) -> lpextrem x.
Proof.
move=> lpx frx; split=> // x1 x2 k /andP [ge0k lt1k] lp1 lp2 xE.
apply/rowP=> i; have h (j : 'I_n): j \notin lpbasei x -> x1 @ j = x2 @ j.
+ move/lpbaseiPn; rewrite xE !mxE (rwP eqP) paddr_eq0.
  - by rewrite mulr_ge0 1?(lpset_ge0 lp1) 1?ltW.
  - by rewrite mulr_ge0 1?(lpset_ge0 lp2) 1?ltW // subr_gt0.
  case/andP; rewrite !mulf_eq0 subr_eq0 [_ == k]eq_sym.
  by rewrite [k == 0]gt_eqF 1?[k == 1]lt_eqF //= => /eqP-> /eqP->.
case/boolP: (i \in lpbasei x) => [i_in_nzx|/h //]; apply/eqP.
rewrite -subr_eq0 -(rwP eqP); pose w i := x1 @ i - x2 @ i.
apply/(free_lpbaseP (μ := w) frx) => /=.
+ by move=> j /h /eqP; rewrite -subr_eq0 (rwP eqP).
rewrite -[RHS](subrr b) -{1}(lpset_sol lp1) -(lpset_sol lp2).
rewrite !mulmx_sum_row -sumrB; apply/eq_bigr.
by move=> /= o _; rewrite scalerBl.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lpbase_freePn x :
  lpbounded -> lpextrem x -> free (lpbase x).
Proof.
move=> bd [lpx lpex]; case/boolP: (free _) => // /L3.
case=> // [x1] [x2] [k] [in01_k neq_xi xE [lpx1 lpx2] _].
move/(_ _ _ _ in01_k lpx1 lpx2 xE): lpex => {lpx1 lpx2 xE}.
by rewrite (rwP eqP) (negbTE neq_xi).
Qed.

(* -------------------------------------------------------------------- *)
Lemma lp_cvx_hull x :
  lpbounded -> lpset x -> lpcvxcb lpextrem x.
Proof.
move=> bp; move: x; suff h: forall n x,
  (size (lpbasei x) < n)%N -> lpset x -> lpcvxcb lpextrem x.
+ by move=> x lpx; apply: (h (size (lpbasei x)).+1).
elim=> [|k ih] x; rewrite (ltn0, ltnS) // => ltn lpx.
case/boolP: (free (lpbase x)) => [fpx|].
+ by apply/cvxcb_mem/lpbase_freeP.
case/L3 => // [x1] [x2] [l] [in01_l neq_xi xE [lpx1 lpx2]].
case=> lep [i1 st1 stN1] [i2 st2 stN2].
have sub1: {subset lpbasei x1 <= lpbasei x}.
+ by move=> i hi; apply/lep; rewrite mem_cat hi.
have sub2: {subset lpbasei x2 <= lpbasei x}.
+ by move=> i hi; apply/lep; rewrite mem_cat hi orbT.
have lt1: (size (lpbasei x1) < k)%N.
+ apply/(leq_trans _ ltn); rewrite ltnNge; apply/negP=> le_sz.
  case: (uniq_min_size (uniq_lpbasei _) sub1 le_sz).
  by move=> _ mi; move: stN1; rewrite mi st1.
have lt2: (size (lpbasei x2) < k)%N.
+ apply/(leq_trans _ ltn); rewrite ltnNge; apply/negP=> le_sz.
  case: (uniq_min_size (uniq_lpbasei _) sub2 le_sz).
  by move=> _ mi; move: stN2; rewrite mi st2.
have [h1 h2] := (ih _ lt1 lpx1, ih _ lt2 lpx2).
rewrite xE; apply/cvx_cvxcb=> //.
by case/andP: in01_l=> *; rewrite !ltW.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lpmax_on_extrems  x :
  lpbounded -> lpset x ->
    exists2 e, lpextrem e & lpcost x <= lpcost e.
Proof.
move=>lpb /lp_cvx_hull /lpcvxcbP[] // k c E xE sm1 ge0_c ex.
case/boolP: [exists i, lpcost (E i) >= lpcost x].
+ by case/existsP=> /= i le; exists (E i).
move/existsPn=> /= gt; suff: lpcost x < lpcost x by rewrite ltxx.
have {1}->: lpcost x = \sum_i c i * (lpcost (E i)).
+ by rewrite xE linear_sum /=; apply/eq_bigr=> i _; rewrite linearZ.
rewrite -[X in _ < X]mul1r -sm1 mulr_suml; have: exists i, 0 < c i.
+ apply/existsP; move/eqP: sm1; apply/contraLR => /existsPn=> /= eq0.
  rewrite big1 1?eq_sym ?oner_eq0 // => i _; apply/eqP.
  by rewrite eq_le ge0_c andbT leNgt -(rwP negP).
case=> i gt0_ci; rewrite [X in X < _](bigD1 i) //=.
rewrite [X in _ < X](bigD1 i) //=; apply/ltr_le_add.
+ by rewrite ltr_pmul2l // ltNge -(rwP negP).
+ apply/ler_sum=> j ne_ji; rewrite ler_wpmul2l //.
  by apply/ltW; rewrite ltNge -(rwP negP).
Qed.

(* -------------------------------------------------------------------- *)
Local Notation lpmask m := (mask m (enum 'I_n)).

CoInductive lpesol_spec (m : n.-tuple bool) (s : seq 'rV[F]_n) : Prop :=
| LPENFree of
   ~~ free [seq row i A | i <- lpmask m] & s = [::]

| LPEFree of
    free [seq row i A | i <- lpmask m]
  & (size s <= 1)%N
  & (forall x, reflect (lpset x /\ {subset lpbasei x <= lpmask m}) (x \in s)).

Lemma lpesolP (m : n.-tuple bool) : {s : seq 'rV[F]_n | lpesol_spec m s}.
Proof.
case/boolP: (free [seq row i A | i <- lpmask m]); last first.
+ by move=> Nfrx; exists [::]; apply/LPENFree.
move=> frx; set X := [seq row i A | i <- lpmask m] in frx.
case/boolP: (b \in <<X>>%VS); last first.
+ move=> bNX; exists [::]; apply/LPEFree=> // x; rewrite in_nil.
  constructor=> -[lpx lpbx]; move/negP: bNX; apply; rewrite -[X]in_tupleE.
  apply/spanP=> /=; exists (fun i => x @ ((lpmask m)`_i)); apply/esym.
  rewrite -[RHS](lpset_sol lpx) mulmx_sum_row; apply/esym.
  rewrite (bigID (mem (lpmask m))) /= addrC big1 ?add0r => [i ilpi|].
  * case: (x @ i =P 0) => [->|]; first by rewrite scale0r.
    by move/lpbaseiPn/negP/negbNE/lpbx; rewrite (negbTE ilpi).
  pose G i : 'rV[F]_p := x @ (lpmask m)`_i *: X`_i.
  rewrite [RHS](eq_bigr (G \o val)) -?(big_mkord xpredT) /=.
  * by move=> i _; rewrite {}/G (tnth_nth 0).
  rewrite -big_uniq ?mask_uniq ?enum_uniq //= (big_nth 0).
  rewrite /X size_map; apply/eq_big_nat => i.
  by case/andP=> _ lti; rewrite /G (nth_map 0).
case/(free_span frx) => /= μ bE uq; have uqX := free_uniq frx.
pose x := \row_i (if i \in lpmask m then μ X`_(index i (lpmask m)) else 0).
have uqx y: {subset lpbasei y <= lpmask m} -> y *m A = b -> x = y.
+ move=> ylpi; rewrite mulmx_sum_row (bigID (mem (lpmask m))) /=.
  rewrite addrC big1 ?add0r => [i iNlpi|].
  * suff ->: y @ i = 0 by rewrite scale0r.
    by apply/lpbaseiPn/negP => /ylpi; rewrite (negbTE iNlpi).
  rewrite -big_uniq ?mask_uniq ?enum_uniq //=.
  pose G (x : 'rV_p) : 'rV_p := y @ (lpmask m)`_(index x X) *: x.
  rewrite big_seq (eq_bigr (G \o (fun i : 'I_n => X`_(index i (lpmask m))))).
  * move=> i ilpi /=; rewrite {}/G; congr *:%R; last first.
    - by rewrite (nth_map 0) ?index_mem // nth_index.
    by rewrite index_uniq ?size_map ?index_mem // nth_index.
  rewrite -big_seq /= -(big_map _ xpredT); set s := map _ _.
  have ->: s = X; first apply/(@eq_from_nth _ 0).
  * by rewrite !size_map.
  * move=> i; rewrite !size_map => ilpi; rewrite !(nth_map 0) //.
    - by rewrite index_uniq // ?mask_uniq ?enum_uniq.
    by rewrite nth_index // mem_nth.
  rewrite {}/G => /esym /uq eqμ; apply/rowP=> i.
  rewrite !mxE; case: ifPn => [ilpi|]; last first.
  * move=> iNlpi; apply/esym/lpbaseiPn/negP.
    by move/ylpi; rewrite (negbTE iNlpi).
  rewrite -eqμ ?mem_nth // ?size_map ?index_mem //.
  by rewrite index_uniq ?size_map ?index_mem // nth_index.
case/boolP: [forall i, 0 <= x @ i]; last first.
+ move=> h; exists [::]; apply/LPEFree=> //= y.
  constructor; move/forallPn: h=> /= [j]; rewrite (rwP negP) -ltNge.
  move=> lt0_xj -[] /lpsetP[ge0_y soly] /uqx /(_ soly) /rowP /(_ j).
  by move=> xjE; move: lt0_xj; rewrite xjE ltNge ge0_y.
move/forallP=> /= ge0_x; exists [:: x]; apply/LPEFree=> //.
move=> y; rewrite mem_seq1; apply: (iffP eqP) => [->|]; last first.
+ by case=> /lpset_sol h1 h2; apply/esym/uqx.
split; first (apply/lpsetP; split => //).
* rewrite mulmx_sum_row (bigID (mem (lpmask m))) /= addrC big1.
  - by move=> i iNlpi; rewrite /x !mxE (negbTE iNlpi) scale0r.
  rewrite add0r [RHS]bE [RHS]big_map -big_uniq /=.
  - by rewrite mask_uniq ?enum_uniq.
  rewrite !big_seq; apply/eq_bigr => /= i ilpi.
  by rewrite /x !mxE ilpi (nth_map 0) ?index_mem ?nth_index.
* move=> i /lpbaseiP /eqP; apply/contraR => iNlpi.
  by rewrite /x !mxE (negbTE iNlpi).
Qed.

(* -------------------------------------------------------------------- *)
Definition lpextrems : seq 'rV[F]_n :=
  undup (flatten [seq tag (lpesolP m) | m <- enum {: n.-tuple bool}]).

(* -------------------------------------------------------------------- *)
Lemma lpextremsP x : lpbounded ->
  reflect (lpextrem x) (x \in lpextrems).
Proof. move=> bd; apply: (iffP idP).
+ rewrite mem_undup => /flatten_mapP [/= m _].
  case: lpesolP => /= rv [_ ->//| frx _ /(_ x) /rwP [_ h /h {h}]].
  case=> lpx lpi; apply/lpbase_freeP => //.
  apply/(sub_free _ frx); last first.
  * rewrite map_inj_in_uniq ?uniq_lpbasei // => /= y1 y2.
    move=> /lpi h1 /lpi h2; set s := map _ _ in frx.
    have ->: row y1 A = s`_(index y1 (lpmask m)).
    - by rewrite (nth_map 0) ?index_mem // nth_index.
    have ->: row y2 A = s`_(index y2 (lpmask m)).
    - by rewrite (nth_map 0) ?index_mem // nth_index.
    move/eqP; rewrite nth_uniq ?size_map ?index_mem //.
    - by apply/free_uniq.
    rewrite -(@nth_uniq _ 0 (lpmask m)) ?index_mem //.
    - by rewrite mask_uniq ?enum_uniq.
    by rewrite !nth_index // (rwP eqP).
  by move=> /= y /mapP[/= i /lpi im ->]; apply/map_f.
+ case=> lpx lpex; rewrite mem_undup; apply/flatten_mapP => /=.
  exists [tuple x @ i != 0 | i < n]; first by rewrite mem_enum.
  have frx := (@lpbase_freePn x bd (conj lpx lpex)).
  case: lpesolP => /= rv [/= h _|]; first move: h.
  * by rewrite -filter_mask frx.
  move=> _ _ /(_ x) /rwP [h _]; apply/h; split=> //= {h} i.
  rewrite -filter_mask => /lpbaseiP /eqP nz_xi.
  by rewrite mem_filter nz_xi mem_enum.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lpsolvebd_r : lpbounded -> {x | lpset x} ->
  {x | lpset x /\ forall y, lpset y -> lpcost y <= lpcost x}.
Proof.
move=> bd [x lpx]; pose I := seq_sub lpextrems; have x0: I.
+ case E: lpextrems => [|y s]; last first.
  * have pr: y \in lpextrems by rewrite E mem_head.
    by apply: (SeqSub pr).
  absurd False => //; case: (lp_cvx_hull bd lpx) => -[|k] [c] [M] [_].
  * by rewrite big_ord0 (rwP eqP) eq_sym oner_eq0.
  by move=> _ _ /(_ 0) /(@lpextremsP _ bd); rewrite E.
have h := ex_intro xpredT x0 (erefl true).
pose m : I := arg_minr (fun x : I => - lpcost (val x)) h.
exists (val m); rewrite {}/m; case: arg_minrP => -[/= m lme] _ min.
move/lpextremsP: lme => /(_ bd) [lpm _]; split=> // y lpy.
have {}min: forall j, lpextrem j -> lpcost j <= lpcost m.
+ move=> j /lpextremsP -/(_ bd) lje; have /= := min (SeqSub lje).
  by rewrite ler_oppr opprK; apply.
have /lpcvxcbP [k c M -> sc1 ge0_c exM] := lp_cvx_hull bd lpy.
rewrite linear_sum.  /=; apply/(@le_trans _ _ (\sum_i (c i * lpcost m))).
+ apply/ler_sum=> i _; rewrite linearZ /= ler_wpmul2l //.
  by apply/min/exM.
+ by rewrite -mulr_suml sc1 mul1r.
Qed.
End LP.

(* -------------------------------------------------------------------- *)
Lemma lpsolvebd {F : realFieldType} {n p} (A : 'M[F]_(n, p)) b c :
  lpbounded A b -> {x | lpset A b x} ->
  {x | lpset A b x /\ forall y, lpset A b y -> lpcost c y <= lpcost c x}.
Proof.
case: n A c => [|n] A c.
+ move=> _ [x hx]; exists x; split=> // y _; rewrite /lpcost.
  by rewrite !mulmx_sum_row !summxE !big_ord0.
case: p A b => [|p] A b; last by apply/lpsolvebd_r.
move=> h _; absurd false => //; case: h => M h.
have ge0_M: 0 < M; first have := h 0 _ 0.
- rewrite mxE; apply; apply/lpsetP; split.
  * by move=> i; rewrite mxE.
  * by apply/rowP=> -[].
pose x := \row_(_ < n.+1) M; have: lpset A b x.
- apply/lpsetP; split; last by apply/rowP=> -[].
  by move=> i; apply/ltW; rewrite mxE.
by move/h=> /(_ 0); rewrite mxE ltxx.
Qed.

(* ==================================================================== *)
Delimit Scope syntax_scope with T.

Section LPPb.
Context {F : realFieldType} (n : nat).

Inductive lprel := LPRLe | LPRGe | LPREq.

Bind Scope syntax_scope with lprel.

Notation "<=%:T" := LPRLe : syntax_scope.
Notation ">=%:T" := LPRGe : syntax_scope.
Notation "==%:T" := LPREq : syntax_scope.

Scheme Equality for lprel.

Lemma lprel_eqP : Equality.axiom lprel_beq.
Proof. by case=> [] [] /=; constructor. Qed.

Definition lprel_eqMixin := EqMixin lprel_eqP.
Canonical lprel_eqType := Eval hnf in EqType lprel lprel_eqMixin.

Definition rel_of_lprel (r : lprel) :=
  match r return rel F with
  | (<=%:T)%T => <=%R
  | (>=%:T)%T => >=%R
  | (==%:T)%T => eq_op
  end.

Coercion rel_of_lprel : lprel >-> rel.

Record lpeq := LPEq {
  lpeq_coeffs : 'cV[F]_n;
  lpeq_rel    : lprel;
  lpeq_const  : F;
}.

Coercion lpeq_coeffs : lpeq >-> matrix.
Coercion lpeq_rel    : lpeq >-> lprel.

Notation "a <= b" := (LPEq a <=%:T b) : syntax_scope.
Notation "a >= b" := (LPEq a >=%:T b) : syntax_scope.
Notation "a == b" := (LPEq a ==%:T b) : syntax_scope.

Notation "a =[ r ]= b" := (LPEq a r b)
  (at level 70, no associativity, format "a  =[ r ]=  b")
  : syntax_scope.

Definition mem_lpeq (e : lpeq) (x : 'rV[F]_n) :=
  let: LPEq a r b := e in r ((x *m a) 0 0) b.

Canonical lpeq_predType :=
  Eval hnf in PredType (fun e : lpeq => mem_lpeq e).

Lemma mem_lpeqE (e : lpeq) (x : 'rV[F]_n) : (x \in e) = mem_lpeq e x.
Proof. by []. Qed.

Record lppb (k : nat) := LPPb {
  lppb_eqs  : k.-tuple lpeq;
  lppb_bnd  : F;
  lppb_cost : {linear 'rV[F]_n -> F^o};
}.

Definition mem_lppb {k} (pb : lppb k) (x : 'rV[F]_n) :=
     [forall i, x \in tnth pb.(lppb_eqs) i]
  && [forall i, `|x @ i| <= pb.(lppb_bnd)].

Canonical lppb_predType {k} :=
  Eval hnf in PredType (fun pb : lppb k => mem_lppb pb).

Lemma lppbP {k} (pb : lppb k) (x : 'rV[F]_n) :
  reflect
    (  (forall i, x \in tnth pb.(lppb_eqs) i)
    /\ (forall i, `|x @ i| <= pb.(lppb_bnd)))
    (x \in pb).
Proof. apply: (iffP andP).
+ by case=> /forallP? /forallP?; split.
+ by case=> ??; split; apply/forallP.
Qed.

(* -------------------------------------------------------------------- *)
Notation vshift k x := (lshift (n+n) (@lshift (n+n) k x)).
Notation eshift k x := (lshift (n+n) (@rshift (n+n) k x)).
Notation bshift k x := (@rshift ((n+n)+k) (n+n) x).

(* -------------------------------------------------------------------- *)
Local Notation Z k := ((n + n) + k + (n + n))%N.

Section ZInd.
Context {k} (P : 'I_(Z k) -> Prop).

Hypothesis hvl : forall i, P (vshift _ (lshift _ i)).
Hypothesis hvr : forall i, P (vshift _ (rshift _ i)).
Hypothesis he  : forall i, P (eshift _ i).
Hypothesis hbl : forall i, P (bshift _ (lshift _ i)).
Hypothesis hbr : forall i, P (bshift _ (rshift _ i)).

Lemma zW i : P i.
Proof. by move: i; do! elim/splitW. Qed.
End ZInd.

(* -------------------------------------------------------------------- *)
Definition lpeq_var       (x : 'I_n) : 'cV[F]_n := delta_mx x 0.
Definition lpeq_shift {k} (x : 'I_k) : 'cV[F]_k := delta_mx x 0.
Definition lpeq_bd        (x : 'I_n) : 'cV[F]_n := delta_mx x 0.

Definition lprel_sign (r : lprel) :=
  match r return F with
  | (<=%:T)%T =>  1
  | (>=%:T)%T => -1
  | (==%:T)%T =>  0
  end.

(* -------------------------------------------------------------------- *)
Record nmpb (n k : nat) := NMPb {
  nmpb_coeffs : 'M[F]_(n, k);
  nmpb_const  : 'rV[F]_k;
  nmpb_cost   : 'cV[F]_n;
}.

Definition mem_nmpb {n k} (pb : nmpb n k) (x : 'rV[F]_n) :=
  lpset pb.(nmpb_coeffs) pb.(nmpb_const) x.

Canonical nmpb_predType {n k} :=
  Eval hnf in PredType (fun pb : nmpb n k => mem_nmpb pb).

Lemma nmpbP {m k} (pb : nmpb m k) (x : 'rV[F]_m) :
  (x \in pb) = lpset pb.(nmpb_coeffs) pb.(nmpb_const) x.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition normmx {k} xp xn s bp bn : 'cV[F]_(Z k) :=
  col_mx (col_mx (col_mx xp xn) s) (col_mx bp bn).

Definition mxvar {k} (M : 'rV[F]_(Z k)) :=
  lsubmx (lsubmx M).

Definition mxbd {k} (M : 'rV[F]_(Z k)) :=
  rsubmx M.

Definition mxvarp  {k} (M : 'rV[F]_(Z k)) := lsubmx (mxvar M).
Definition mxvarn  {k} (M : 'rV[F]_(Z k)) := rsubmx (mxvar M).
Definition mxshift {k} (M : 'rV[F]_(Z k)) := rsubmx (lsubmx M).
Definition mxbdp   {k} (M : 'rV[F]_(Z k)) := lsubmx (mxbd M).
Definition mxbdn   {k} (M : 'rV[F]_(Z k)) := rsubmx (mxbd M).

(* -------------------------------------------------------------------- *)
Definition norm_lpeq k (e : lpeq) (i : 'I_k) : 'cV[F]_(Z k) :=
  normmx
    (\sum_(j < n) (  e @^ j *: lpeq_var j))
    (\sum_(j < n) (- e @^ j *: lpeq_var j))
    (lprel_sign e *: lpeq_shift i)
    0 0.

Definition norm_lpeqs k (e : k.-tuple lpeq) : 'M[F]_(Z k, k) :=
  \matrix_(i < _, j < k) norm_lpeq (tnth e j) j i 0.

Definition norm_bndp k (i : 'I_n) : 'cV[F]_(Z k) :=
  normmx (lpeq_var i) 0 0 (lpeq_bd i) 0.

Definition norm_bndn k (i : 'I_n) : 'cV[F]_(Z k) :=
  normmx 0 (lpeq_var i) 0 0 (lpeq_bd i).

Definition norm_bnde k (e : lpeq) (i : 'I_k) : 'cV[F]_(Z k) :=
  let m := (lpeq_rel e == ==%:T%T)%:R *: lpeq_shift i in
  normmx 0 0 m 0 0.

Definition norm_bnds k (e : k.-tuple lpeq) : 'M[F]_(Z k, (n + n) + k) :=
  row_mx
    (row_mx
      (\matrix_(i < _, j < n) (norm_bndp k j) i 0)
      (\matrix_(i < _, j < n) (norm_bndn k j) i 0))
    (\matrix_(i < _, j < k) (norm_bnde (tnth e j) j i 0)).

Definition norm_lpeqs_bnd k (e : k.-tuple lpeq) : 'M[F]_(Z k, k + ((n + n) + k)) :=
  row_mx (norm_lpeqs e) (norm_bnds e).

Definition norm_const k (e : k.-tuple lpeq) : 'rV[F]_k :=
  \row_(i < k) lpeq_const (tnth e i).

Definition norm_const_bnd k M (e : k.-tuple lpeq) : 'rV[F]_(k + ((n + n) + k)) :=
  row_mx
    (norm_const e)
    (row_mx
       (const_mx M)
       (\row_(i < k) (lpeq_rel (tnth e i) == ==%:T%T)%:R)).

Definition norm_cost k (f : 'rV[F]_n -> F) : 'cV[F]_(Z k) :=
  let m : 'cV[F]_n := \col_(i < n) f (delta_mx 0 i) in
  col_mx (col_mx (col_mx m (-m)) 0) 0.

(* -------------------------------------------------------------------- *)
Definition norm_pb k (pb : lppb k) : nmpb (Z k) (k + ((n + n) + k)) :=
  {| nmpb_coeffs := norm_lpeqs_bnd pb.(lppb_eqs);
     nmpb_const  := norm_const_bnd pb.(lppb_bnd) pb.(lppb_eqs);
     nmpb_cost   := norm_cost k pb.(lppb_cost); |}.

(* -------------------------------------------------------------------- *)
Section LPPbTx.
Context {k : nat} (pb : lppb k).

Notation A := (norm_pb pb).(nmpb_coeffs).
Notation b := (norm_pb pb).(nmpb_const).
Notation c := (norm_pb pb).(nmpb_cost).
Notation E := (tnth pb.(lppb_eqs)).

Definition lp2pb (x : 'rV[F]_(Z k)) : 'rV[F]_n :=
  mxvarp x - mxvarn x.

Let simpmx := (mxE, splitlr).

(* -------------------------------------------------------------------- *)
Local Lemma norm_bnd_vE i j :
  A (vshift k j) (rshift k (lshift _ i)) = (j == i)%:R.
Proof.
elim/splitW: j => j; elim/splitW: i => i;
  rewrite !simpmx -?val_eqE ?eqn_add2l ?andbT //=.
+ by rewrite ltn_eqF // ltn_addr.
+ by rewrite gtn_eqF // ltn_addr.
Qed.

Local Lemma norm_bnd_bE i j :
  A (bshift k j) (rshift k (lshift _ i)) = (j == i)%:R.
Proof.
elim/splitW: j => j; elim/splitW: i => i;
  rewrite !simpmx -?val_eqE ?eqn_add2l ?andbT //=.
+ by rewrite ltn_eqF // ltn_addr.
+ by rewrite gtn_eqF // ltn_addr.
Qed.

Local Lemma norm_bndE (x : 'rV[F]_(Z k)) (i : 'I_(n + n)) :
  (x *m A) @ (rshift _ (lshift _ i)) = x @ (vshift _ i) + x @ (bshift _ i) .
Proof.
rewrite mulmx_sum_rowE 2!big_split_ord /=.
rewrite [X in _+X+_=_]big1 ?addr0 => [j _|].
+ by elim/splitW: i => i; rewrite !simpmx mulr0.
rewrite (bigD1 i) //= -!addrA; congr +%R.
+ by rewrite norm_bnd_vE eqxx mulr1.
rewrite big1 ?add0r => [j ne_ji|].
+ by rewrite norm_bnd_vE (negbTE ne_ji) mulr0.
rewrite (bigD1 i) //= big1 ?addr0 => [j ne_ji|].
+ by rewrite norm_bnd_bE (negbTE ne_ji) mulr0.
by rewrite norm_bnd_bE eqxx mulr1.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma norm_eqE (x : 'rV[F]_(Z k)) i :
    (x *m A) @ (lshift _ i)
  = \sum_(j < n) E i @^ j *
      (x @ (vshift _ (lshift _ j)) - x @ (vshift _ (rshift _ j)))
    + x @ eshift _ i * lprel_sign (E i).
Proof.
rewrite mulmx_sum_rowE big_split_ord /= [X in _+X]big1 ?addr0.
+ by elim/splitW => j; rewrite !simpmx mulr0.
rewrite big_split_ord /=; congr +%R; last first.
+ rewrite (bigD1 i) //= big1 ?addr0; last first.
  * by rewrite !simpmx !eqxx mulr1.
  by move=> j ne_ji; rewrite !simpmx andbT (negbTE ne_ji) !mulr0.
rewrite big_split_ord -big_split /=; apply/eq_bigr=> j _.
rewrite !simpmx !summxE !(bigD1 (P := xpredT) j) //= !big1 ?addr0.
+ by move=> m ne_mj; rewrite !mxE [j==_]eq_sym (negbTE ne_mj) mulr0.
+ by move=> m ne_mj; rewrite !mxE [j==_]eq_sym (negbTE ne_mj) mulr0.
by rewrite !simpmx !eqxx !mulr1 mulrN -mulrBl mulrC.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma norm_vbndE (x : 'rV[F]_(Z k)) i :
    (x *m A) @ (rshift _ (rshift _ i))
  = x @ eshift k i * (lpeq_rel (E i) == ==%:T%T)%:R.
Proof.
rewrite mulmx_sum_rowE big_split_ord /= [X in _+X]big1 ?addr0.
+ by elim/splitW => j _; rewrite !simpmx mulr0.
rewrite big_split_ord /= [X in X+_]big1 ?add0r.
+ by elim/splitW => j _; rewrite !simpmx mulr0.
rewrite (bigD1 i) //= big1 ?addr0 => [m ne|].
+ by rewrite !simpmx (negbTE ne) !mulr0.
by rewrite !simpmx !eqxx mulr1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sol_lp2pb (x : 'rV[F]_(Z k)) :
  x \in norm_pb pb -> lp2pb x \in pb.
Proof.
rewrite nmpbP => /lpsetP[ge0_x solx]; apply/lppbP; split; last first.
+ move=> i; rewrite !mxE. 
  move/rowP: (solx) => /(_ (rshift _ (lshift _ (lshift _ i)))).
  move/rowP: (solx) => /(_ (rshift _ (lshift _ (rshift _ i)))).
  rewrite !norm_bndE !(mxE,splitlr) ler_norml => h1 h2.
  rewrite ler_oppl opprB -{1}h1 -{1}h2 !ler_add2l.
  rewrite (le_trans _ (ge0_x _)) ?oppr_le0 //=.
  by rewrite (le_trans _ (ge0_x _)) ?oppr_le0.
move=> i; rewrite mem_lpeqE /mem_lpeq.
case E: (tnth _ _) => [a r e]; move/rowP: solx.
move/(_ (lshift _ i)); rewrite norm_eqE !simpmx E /=.
set f := BIG_F; have eqf j: f j = (lp2pb @^ x) j * a @^ j.
+ by rewrite {}/f mulrC !simpmx.
rewrite {f eqf}(eq_bigr _ (fun i _ => eqf i)) => /esym/eqP.
rewrite -subr_eq => /eqP <-; case: {E} r => //=.
+ by rewrite mulr1 ler_subl_addr ler_addl ge0_x.
+ by rewrite mulrN1 opprK ler_addl ge0_x.
+ by rewrite mulr0 subr0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cost_lp2pb (x : 'rV[F]_(Z k)) :
  pb.(lppb_cost) (lp2pb x) = (x *m (norm_pb pb).(nmpb_cost)) 0 0.
Proof.
rewrite !simpmx big_split_ord /= [X in _ + X]big1 ?addr0.
+ by elim/splitW=> i _; rewrite !simpmx mulr0.
rewrite big_split_ord /= [X in _ + X]big1 ?addr0.
+ by move=> i _; rewrite !simpmx mulr0.
rewrite big_split_ord -big_split /=; set f := BIG_F.
have eqf i: f i = (lp2pb x) @ i * (lppb_cost pb) (delta_mx 0 i).
+ by rewrite {}/f !simpmx mulrN -mulrBl.
rewrite {eqf f}(eq_bigr _ (fun i _ => eqf i)).
rewrite {1}[lp2pb x]row_sum_delta linear_sum.
by apply/eq_bigr=> /= i _; rewrite linearZ.
Qed.
End LPPbTx.

(* -------------------------------------------------------------------- *)
Section LpPbRevTx.
Context {k : nat} (pb : lppb k).

Notation A := (norm_pb pb).(nmpb_coeffs).
Notation b := (norm_pb pb).(nmpb_const).
Notation c := (norm_pb pb).(nmpb_cost).
Notation E := (tnth pb.(lppb_eqs)).

Let simpmx := (mxE, splitlr).

Let ε (x : 'rV[F]_n) i : F :=
  lprel_sign (E i) *
    (lpeq_const (E i) - (x *m (E i)) 0 0).

Definition pb2lp (x : 'rV[F]_n) :=
  trmx (normmx
    (\col_i   Num.max (x @ i) 0)
    (\col_i - Num.min (x @ i) 0)
    (\col_i if lpeq_rel (tnth pb.(lppb_eqs) i) is ==%:T%T then 1 else ε x i)
    (\col_i (pb.(lppb_bnd) - Num.max (x @ i) 0))
    (\col_i (pb.(lppb_bnd) + Num.min (x @ i) 0))).

(* -------------------------------------------------------------------- *)
Lemma sol_pb2lp x : x \in pb -> lpset A b (pb2lp x).
Proof.
case/lppbP => solx bdx; apply/lpsetP; split.
+ elim/(@zW k) => i; rewrite !simpmx.
  * by rewrite le_maxr lexx orbT.
  * by rewrite oppr_ge0 le_minl lexx orbT.
  * move/(_ i): solx; rewrite mem_lpeqE /mem_lpeq /ε.
    case: (E i) => [a r e]; case: r => /=; rewrite ?Monoid.simpm.
    + by rewrite subr_ge0.
    + by rewrite mulN1r oppr_ge0 subr_le0.
    + by rewrite ler01.
  * by rewrite subr_ge0 le_maxl !(le_trans _ (bdx i)) ?ler_norm.
  * rewrite -ler_subl_addr sub0r oppr_min oppr0.
    rewrite le_maxl !(le_trans _ (bdx i)) ?normr_ge0 //.
    by rewrite -normrN ler_norm.
apply/rowP; elim/splitW => i.
+ rewrite norm_eqE [X in X+_](_ : _ = (x *m E i) 0 0).
  * rewrite !simpmx; apply/eq_bigr=> /= j _; rewrite mulrC.
    by congr *%R; rewrite !simpmx opprK addr_max_min addr0.
  rewrite ![in X in _+X]simpmx ![in RHS]simpmx /ε.
  case EE: (E i) => [a [] e] /=.
  * by rewrite !Monoid.simpm /= addrAC subrr add0r.
  * by rewrite !(mulN1r, mulrN1) opprK addrCA subrr addr0.
  rewrite !Monoid.simpm /=; move/(_ i): solx.
  by rewrite mem_lpeqE /mem_lpeq EE /= => /eqP.
+ elim/splitW: i; last first.
  * move=> i; rewrite norm_vbndE !simpmx.
    by case: (lpeq_rel _); rewrite !Monoid.simpm //=.
  elim/splitW=> i; rewrite norm_bndE !simpmx.
  * by rewrite addrCA subrr addr0.
  * by rewrite addrCA addNr addr0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cost_pb2lp (x : 'rV[F]_n) :
  pb.(lppb_cost) x = (pb2lp x *m (norm_pb pb).(nmpb_cost)) 0 0.
Proof.
rewrite !simpmx big_split_ord /= [X in _ + X]big1 ?addr0.
+ by elim/splitW=> i _; rewrite !simpmx mulr0.
rewrite big_split_ord /= [X in _ + X]big1 ?addr0.
+ by move=> i _; rewrite !simpmx mulr0.
rewrite big_split_ord -big_split /= {1}[x]row_sum_delta.
rewrite linear_sum; apply/eq_bigr=> /= i _.
rewrite !simpmx linearZ /= !(mulNr, mulrN) opprK.
by rewrite -mulrDl addr_max_min addr0.
Qed.

End LpPbRevTx.

(* ==================================================================== *)
Section LpPbTxBnd.
Context {k : nat} (pb : lppb k).

Notation A := (norm_pb pb).(nmpb_coeffs).
Notation b := (norm_pb pb).(nmpb_const).
Notation c := (norm_pb pb).(nmpb_cost).
Notation E := (tnth pb.(lppb_eqs)).

Let simpmx := (mxE, splitlr).

(* -------------------------------------------------------------------- *)
Lemma norm_pb_bnd : lpbounded A b.
Proof.
pose T i := `|lpeq_const (E i)| + \sum_(j < n) `|E i @^ j| * `|pb.(lppb_bnd)|.
pose N := \sum_(i < k) (1 + T i); have ge0_T i : 0 <= T i.
+ rewrite addr_ge0 ?normr_ge0 //; apply/sumr_ge0=> /= j _.
  by rewrite mulr_ge0 ?normr_ge0.
pose M := `|pb.(lppb_bnd)| + N; have ge0_N: 0 <= N.
+ by apply/sumr_ge0=> /= i _; rewrite addr_ge0.
exists (1 + M) => x /lpsetP[ge0_x solx] => i.
rewrite (@le_lt_trans _ _ M) ?ltr_addr ?ltr01 // /M.
elim/splitW: i => i; move/rowP: solx => solx; last first.
+ move/(_ (rshift _ (lshift _ i))): solx.
  rewrite norm_bndE !simpmx => <-.
  rewrite ger0_norm ?addr_ge0 ?ge0_x //.
  by rewrite -addrA addrCA ler_addl addr_ge0 ?ge0_x.
elim/splitW: i => i.
+ move/(_ (rshift _ (lshift _ i))): solx.
  rewrite norm_bndE !simpmx=> <-.
  rewrite ger0_norm ?addr_ge0 ?ge0_x //.
  by rewrite -addrA ler_addl addr_ge0 ?ge0_x.
rewrite -[X in X <= _]add0r ler_add ?normr_ge0 //.
rewrite /N (bigD1 i) //= -[X in X <= _]addr0 ler_add //; last first.
+ by apply/sumr_ge0 => j _; rewrite addr_ge0.
case EE: (E i) => [a r e] /=; case: (r =P ==%:T%T) => /eqP eqr.
+ move/(_ (rshift _ (rshift _ i))): solx; rewrite norm_vbndE.
  by rewrite !simpmx EE eqr /= mulr1 => ->; rewrite ler_addl.
rewrite ler_paddl // /T; move/(_ (lshift _ i)): (solx).
rewrite norm_eqE !simpmx EE /=; set s := lprel_sign _.
rewrite (rwP eqP) addrC eq_sym -subr_eq => /eqP.
move/(congr1 Num.norm); rewrite normrM (_ : `|s| = 1) /s.
+ by case: {+}r eqr => //=; rewrite (normr1, normrN1).
rewrite mulr1 => eq; apply/(le_trans (ler_norm _)).
rewrite -{}eq (le_trans (ler_norm_sub _ _)) //.
rewrite ler_add2l (le_trans (ler_norm_sum _ _ _)) //.
apply/ler_sum=> j _; rewrite normrM ler_wpmul2l //.
rewrite ler_normr; apply/orP; left.
move/(_ (rshift _ (lshift _ (lshift _ j)))): (solx).
move/(_ (rshift _ (lshift _ (rshift _ j)))): (solx).
rewrite !norm_bndE !(mxE,splitlr) ler_norml => h1 h2.
rewrite ler_oppl opprB -{1}h1 -{1}h2 !ler_add2l.
rewrite (le_trans _ (ge0_x _)) ?oppr_le0 //=.
by rewrite (le_trans _ (ge0_x _)) ?oppr_le0.
Qed.
End LpPbTxBnd.

(* ==================================================================== *)
Section LPPbSol.
Context {k : nat} (pb : lppb k).

Notation A := (norm_pb pb).(nmpb_coeffs).
Notation b := (norm_pb pb).(nmpb_const).
Notation c := (norm_pb pb).(nmpb_cost).
Notation E := (tnth pb.(lppb_eqs)).

Lemma lppbsolve :
  {x | x \in pb} -> {x | x \in pb /\
     forall y, y \in pb -> pb.(lppb_cost) y <= pb.(lppb_cost) x}.
Proof.
move=> solx; case: (@lpsolvebd _ _ _ A b c).
+ by apply/norm_pb_bnd.
+ by case: solx => x solx; exists (pb2lp pb x); apply/sol_pb2lp.
move=> {solx} x [solx maxx]; exists (lp2pb x); split.
+ by apply/sol_lp2pb.
+ move=> y /sol_pb2lp soly; rewrite cost_lp2pb.
  by apply/(le_trans _ (maxx _ soly)); rewrite cost_pb2lp.
Qed.

End LPPbSol.

End LPPb.

(* ==================================================================== *)
Bind Scope syntax_scope with lprel.

Notation "<=%:T" := LPRLe : syntax_scope.
Notation ">=%:T" := LPRGe : syntax_scope.
Notation "==%:T" := LPREq : syntax_scope.

Notation "a <= b" := (LPEq a <=%:T b) : syntax_scope.
Notation "a >= b" := (LPEq a >=%:T b) : syntax_scope.
Notation "a == b" := (LPEq a ==%:T b) : syntax_scope.
