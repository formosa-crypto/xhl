(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis  Require Import reals discrete realseq realsum distr.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Local Notation "← x" := (inl x) (at level 2).
Local Notation "→ x" := (inr x) (at level 2).

(* -------------------------------------------------------------------- *)
Notation IFP := (if _ then _ else _)%pattern.
Notation IFC := (X in if X then _ else _)%pattern.
Notation IFT := (X in if _ then X else _)%pattern.
Notation IFF := (X in if _ then _ else X)%pattern.

(* -------------------------------------------------------------------- *)
Lemma fun2_if {A B C : Type} (f : A -> B -> C) b vT1 vT2 vF1 vF2 :
    f (if b then vT1 else vF1) (if b then vT2 else vF2)
  = if b then f vT1 vT2 else f vF1 vF2.
Proof. by case: b. Qed.

(* -------------------------------------------------------------------- *)
Lemma forallPn {T : finType} (P : pred T) :
  reflect (exists x : T, ~ P x) (~~ [forall x : T, P x]).
Proof. by rewrite negb_forall; apply/'exists_negP. Qed.

(* -------------------------------------------------------------------- *)
Lemma existsPn {T : finType} (P : pred T) :
  reflect (forall x : T, ~ P x) (~~ [exists x : T, P x]).
Proof. by rewrite negb_exists; apply/'forall_negP. Qed.

(* -------------------------------------------------------------------- *)
Section FSplit.
Context {T : Type} (n p : nat).
Context (fn : 'I_n -> T) (fp : 'I_p -> T).

Definition fsplit i :=
  match split i with
  | inl i1 => fn i1
  | inr i2 => fp i2
  end.

Lemma fsplitl (i : 'I_n) : fsplit (lshift p i) = fn i.
Proof.
rewrite /fsplit; case: splitP => j.
+ by move/(@val_inj _ _ 'I_n) => ->.
rewrite /lshift /= => iE; have := ltn_ord i.
by rewrite iE -{2}[n]addn0 ltn_add2l ltn0.
Qed.

Lemma fsplitr (i : 'I_p) : fsplit (rshift n i) = fp i.
Proof.
rewrite /fsplit; case: splitP => j; rewrite /rshift /= => jE.
+ by have := ltn_ord j; rewrite -jE -{2}[n]addn0 ltn_add2l ltn0.
+ by move/addnI: jE => /(@val_inj _ _ 'I_p) => ->.
Qed.

Definition fsplitlr := (@fsplitl, @fsplitr).
End FSplit.

(* -------------------------------------------------------------------- *)
Section BigFSplit.
Context {T R : Type} (idx : R) (op : Monoid.com_law idx).
Context {n p : nat} (Fn : 'I_n -> R) (Fp : 'I_p -> R).

Lemma big_fsplit :
  \big[op/idx]_(i < n + p) fsplit Fn Fp i =
    op (\big[op/idx]_(i < n) Fn i) (\big[op/idx]_(i < p) Fp i).
Proof.
rewrite big_split_ord; congr (op _ _).
+ by apply/eq_bigr=> /= i _; rewrite fsplitl.
+ by apply/eq_bigr=> /= i _; rewrite fsplitr.
Qed.
End BigFSplit.

(* -------------------------------------------------------------------- *)
Lemma splitl m1 m2 (z : 'I_m1) : split (lshift m2 z) = inl _ z.
Proof. case: splitP => j /=.
+ by move/(can_inj (valKd _)) => -/(_ z) ->.
+ by move/eqP; rewrite ltn_eqF // ltn_addr.
Qed.

Lemma splitr m1 m2 (z : 'I_m2) : split (rshift m1 z) = inr _ z.
Proof. case: splitP => j /= /eqP.
+ by rewrite gtn_eqF // ltn_addr.
+ by rewrite eqn_add2l => /eqP /(can_inj (valKd _)) -/(_ z) ->.
Qed.

Definition splitlr := (splitl, splitr).

(* -------------------------------------------------------------------- *)
Section SplitInd.
Context (m1 m2 : nat) (P : 'I_(m1 + m2) -> Prop).

Hypothesis hl : forall i, P (lshift _ i).
Hypothesis hr : forall i, P (rshift _ i).

Lemma splitW i : P i.
Proof. case: (splitP i) => j eq.
+ suff ->: i = lshift _ j by apply/hl. by apply/val_eqP/eqP.
+ suff ->: i = rshift _ j by apply/hr. by apply/val_eqP/eqP.
Qed.
End SplitInd.

(* --------------------------------------------------------------------- *)
Lemma tnth_cat {T : Type} {n m} (t1 : n.-tuple T) (t2 : m.-tuple T) i :
  tnth [tuple of t1 ++ t2] i =
    match split i with
    | inl i => tnth t1 i
    | inr i => tnth t2 i
    end.
Proof.
elim/splitW: i=> i; rewrite splitlr.
+ rewrite (tnth_nth (tnth t1 i)) nth_cat size_tuple /=.
  by rewrite ltn_ord -tnth_nth.
+ rewrite (tnth_nth (tnth t2 i)) nth_cat size_tuple /=.
  by rewrite ltnNge leq_addr /= addKn -tnth_nth.
Qed.

Lemma tnth_catl {T : Type} {n m} (t1 : n.-tuple T) (t2 : m.-tuple T) i :
  tnth [tuple of t1 ++ t2] (lshift _ i) = tnth t1 i.
Proof. by rewrite tnth_cat splitl. Qed.

Lemma tnth_catr {T : Type} {n m} (t1 : n.-tuple T) (t2 : m.-tuple T) i :
  tnth [tuple of t1 ++ t2] (rshift _ i) = tnth t2 i.
Proof. by rewrite tnth_cat splitr. Qed.

Definition tnth_catlr := (@tnth_catl, @tnth_catr).

(* -------------------------------------------------------------------- *)
Section Extrema.
Context {R : realDomainType} {I : finType} (P : pred I) (F : I -> R).

Hypothesis hP : (exists i, P i).

Local Lemma arg_min_proof :
  exists i, P i && [forall (j | P j), (F i <= F j)%R].
Proof.
pose s := [seq i <- enum I | P i]; pose i0 := xchoose hP.
suff: exists2 i, i \in s & (forall j, j \in s -> (F i <= F j)%R).
+ case=> i; rewrite mem_filter => /andP[Pi _] mini; exists i.
  apply/andP; split=> //; apply/forall_inP => j Pj.
  by apply/mini; rewrite mem_filter Pj mem_enum.
have: s != [::]; first rewrite -has_filter.
+ by apply/hasP; exists i0; [rewrite mem_enum | apply/xchooseP].
elim: s => {i0} // i s ih _; case: (s =P [::]) => [{ih}->|].
+ by exists i => [|j]; rewrite mem_seq1 => // /eqP ->.
move/eqP=> /ih[{ih} j j_in_s ih]; case: (lerP (F i) (F j)).
+ move=> le_FiFj; exists i; first by rewrite mem_head.
  move=> k; rewrite in_cons => /orP[/eqP->//|/ih].
  by apply/(le_trans le_FiFj).
+ move/ltW=> le_FjFi; exists j; first by rewrite mem_behead.
  by move=> k; rewrite in_cons => /orP[/eqP->|/ih].
Qed.

Definition arg_minr := nosimpl (xchoose arg_min_proof).

CoInductive extremum_spec : I -> Type :=
  ExtremumSpec i of P i & (forall j, P j -> (F i <= F j)%R)
    : extremum_spec i.

Lemma arg_minrP : extremum_spec arg_minr.
Proof.
by have /andP[Px /forall_inP Plex] := xchooseP arg_min_proof.
Qed.
End Extrema.

(* -------------------------------------------------------------------- *)
Section SpanP.
Context {K : fieldType} {vT: vectType K}.

Lemma spanP {n} (X : n.-tuple vT) (x : vT) :
  reflect
    (exists μ, x = \sum_i μ i *: tnth X i)
    (x \in <<X>>%VS).
Proof. apply: (iffP idP) => /=.
+ move/coord_span => ->; exists (fun i => coord X i x).
  by apply/eq_bigr=> /= i _; rewrite (tnth_nth 0).
+ case=> μ ->; rewrite span_def big_tuple; apply/memv_sumP => /=.
  exists (fun i => μ i *: tnth X i) => // i _.
  by apply/vlineP; exists (μ i).
Qed.
End SpanP.

(* -------------------------------------------------------------------- *)
Section FreeSub.
Context {K : fieldType} {vT : vectType K}.

Lemma sub_free (X Y : seq vT) :
  {subset X <= Y} -> free Y -> uniq X -> free X.
Proof.
move=> leXY frY uqX; have /permPl peq := perm_filterC (mem X) Y.
have := frY; rewrite -(perm_free peq) => /catl_free.
rewrite -(@perm_free _ _ X) //; apply/uniq_perm => // [|x].
+ by rewrite filter_uniq // free_uniq.
+ by rewrite mem_filter andbC; apply/esym/andb_idl => /leXY.
Qed.
End FreeSub.

(* -------------------------------------------------------------------- *)
Section PR.
Context {R : realType}.

(* -------------------------------------------------------------------- *)
Lemma pr_finE {T : finType} (d : {distr T / R}) (E : pred T) :
  \P_[d] E = \sum_i (E i)%:R * d i :> R.
Proof.
rewrite /pr psum_fin; apply/eq_bigr => t _.
by rewrite ger0_norm // mulr_ge0 // ler0n.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eqr_in_pr {T : choiceType} (mu1 mu2 : {distr T / R}) E :
  {in E, mu1 =1 mu2} -> \P_[mu1] E = \P_[mu2] E.
Proof.
move=> h; apply/eq_psum=> x; case/boolP: (E x) => hE.
+ by rewrite !mul1r h. + by rewrite !mul0r.
Qed.

(* -------------------------------------------------------------------- *)
Lemma eqr_pr {T : choiceType} (mu1 mu2 : {distr T / R}) E :
  mu1 =1 mu2 -> \P_[mu1] E = \P_[mu2] E.
Proof. by move=> eq; apply/eqr_in_pr. Qed.
End PR.

(* -------------------------------------------------------------------- *)
Lemma perm_cat2lE {T : eqType} (s1 s2 s3 : seq T) :
  perm_eq s2 s3 -> perm_eql (s1 ++ s2) (s1 ++ s3).
Proof. by move=> h; apply/permPl; rewrite perm_cat2l. Qed.

(* -------------------------------------------------------------------- *)
Lemma perm_cat2rE {T : eqType} (s1 s2 s3 : seq T) :
  perm_eq s2 s3 -> perm_eql (s2 ++ s1) (s3 ++ s1).
Proof. by move=> h; apply/permPl; rewrite perm_cat2r. Qed.

(* -------------------------------------------------------------------- *)
Lemma perm_cat {T : eqType} (s1 s2 t1 t2 : seq T) :
  perm_eq s1 t1 -> perm_eq s2 t2 -> perm_eq (s1 ++ s2) (t1 ++ t2).
Proof.
by move=> h1 h2; rewrite (perm_cat2rE _ h1) perm_cat2l.
Qed.

(* -------------------------------------------------------------------- *)
Lemma enum_bool_perm : perm_eq (enum {: bool}) [:: true; false].
Proof.
apply/uniq_perm => //; first by apply/enum_uniq.
by move=> b; rewrite mem_enum; case: b.
Qed.

(* -------------------------------------------------------------------- *)
Lemma enum_sum_perm {T U : finType} :
  perm_eq
    (enum {: T + U})
    ([seq ← t | t : T] ++ [seq → u | u : U]).
Proof.
have inj_inl: injective inl by move=> T1 T2 x y [].
have inj_inr: injective inr by move=> T1 T2 x y [].
apply/uniq_perm; rewrite ?enum_uniq //.
+ rewrite cat_uniq ?map_inj_uniq -?enumT ?enum_uniq ?andbT //=.
  by apply/hasPn=> /= x /mapP[u _ ->]; apply/mapP; case.
move=> x; apply/esym; rewrite mem_cat mem_enum [in RHS]/in_mem /=.
by apply/orP; case: x => [t|u]; [left|right]; apply/map_f; rewrite enumT.
Qed.

(* -------------------------------------------------------------------- *)
Lemma enum_option_perm {T : finType} :
  perm_eq
    (enum {: option T})
    (None :: [seq Some t | t : T]).
Proof.
apply/uniq_perm; rewrite ?enum_uniq //=.
+ apply/andP; split.
  * by apply/negP=> /mapP[].
  * by rewrite map_inj_uniq ?enum_uniq // => x y [].
move=> x; apply/esym; rewrite mem_enum [in RHS]/in_mem /=.
by case: x => [x|] //=; apply/map_f; rewrite enumT.
Qed.

(* -------------------------------------------------------------------- *)
Section BigOp.
Context {R : Type} (idx : R) (op : Monoid.com_law idx).

Local Notation "1" := idx.
Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma big_sum {I J : finType} (P : pred (I + J)) (F : I + J -> R) :
  \big[op/1]_(ij | P ij) F ij =
      (\big[op/1]_(i | P (← i)) F (← i))
    * (\big[op/1]_(j | P (→ j)) F (→ j)).
Proof.
rewrite /index_enum -!enumT (perm_big _ enum_sum_perm).
by rewrite big_cat !big_map.
Qed.

Lemma big_option {I : finType} (P : pred (option I)) (F : option I -> R) :
  \big[op/1]_(ij | P ij) F ij =
      (if P None then F None else 1)
    * (\big[op/1]_(i | P (Some i)) F (Some i)).
Proof.
rewrite /index_enum -!enumT (perm_big _ enum_option_perm) big_cons.
by rewrite -[IFF](Monoid.mul1m op) -fun2_if if_same big_map.
Qed.
End BigOp.

(* -------------------------------------------------------------------- *)
Section Uniq.
Context {T : eqType} (x0 : T).

Implicit Types (s : seq T).

Lemma uniqPn s :
  reflect
    (exists i j, [/\ i < j, j < size s & nth x0 s i = nth x0 s j])%N
    (~~ uniq s).
Proof.
apply: (iffP idP) => [|[i [j [ltij ltjs]]]]; last first.
  by apply: contra_eqN => Us; rewrite nth_uniq ?ltn_eqF // (ltn_trans ltij).
elim: s => // x s IHs /nandP[/negbNE | /IHs[i [j]]]; last by exists i.+1, j.+1.
by exists 0%N, (index x s).+1; rewrite !ltnS index_mem /= nth_index.
Qed.

Lemma uniqP s :
  reflect
    {in [pred i | (i < size s)%N] &, injective (nth x0 s)}
    (uniq s).
Proof.
apply: (iffP idP) => [????? /eqP|]; first by rewrite nth_uniq // => /eqP.
move=> nth_inj; apply/uniqPn => -[i [j [ltij ltjs /nth_inj ]]].
by move=> /(_ (ltn_trans ltij ltjs)) /(_ ltjs) eq_ij; rewrite eq_ij ltnn in ltij.
Qed.
End Uniq.

(* -------------------------------------------------------------------- *)
Section Ord.
Context (n : nat).

Definition double_ord_proof x : (x < n)%N -> (x.*2 < n.*2)%N.
Proof. by rewrite ltn_double. Qed.

Definition inc_double_ord_proof x : (x < n)%N -> (x.*2.+1 < n.*2)%N.
Proof. by rewrite ltn_Sdouble. Qed.

Definition double_ord (x : 'I_n) := Ordinal (double_ord_proof (ltn_ord x)).
Definition inc_double_ord (x : 'I_n) := Ordinal (inc_double_ord_proof (ltn_ord x)).
End Ord.

(* -------------------------------------------------------------------- *)
Section Matrix.
Context (R : ringType) (m n : nat).

Lemma mulmx_sum_rowE (u : 'rV[R]_m) (A : 'M[R]_(m, n)) i :
  (u *m A) 0 i = \sum_j u 0 j * A j i.
Proof.
by rewrite mulmx_sum_row summxE; apply/eq_bigr => j _; rewrite !mxE.
Qed.
End Matrix.

(* -------------------------------------------------------------------- *)
Lemma head_rot_index {T : eqType} (s : seq T) x :
  x \in s -> uniq s -> next s x = head x (rot (index x s).+1 s).
Proof.
move/path.splitP=> [p1 p2]; rewrite -cats1 -catA => uq.
rewrite !index_cat mem_seq1 /= !eqxx addn0.
move: (uq); rewrite uniq_catC -catA => /=.
case/andP; rewrite mem_cat negb_or => /andP[_ /negbTE ->] _.
rewrite rotS; first by rewrite size_cat /= addnS ltnS leq_addr.
rewrite rot_size_cat /= rot1_cons -nth0.
rewrite -(next_rot (size p1)); first by rewrite -cat1s.
rewrite rot_size_cat cat_cons next_nth mem_head.
by case: (p2 ++ p1) => //=; rewrite eqxx.
Qed.

Lemma next_head {T : eqType} (s : seq T) x : next (x :: s) x = head x s.
Proof. by rewrite next_nth mem_head /= eqxx nth0. Qed.

(* -------------------------------------------------------------------- *)
Section CompMonoid.
Context {T: Type}.

Notation comp := (@comp T T T).

Definition compA : associative comp.
Proof. done. Qed.

Definition compf1 : left_id idfun comp.
Proof. done. Qed.

Definition comp1f : right_id idfun comp.
Proof. done. Qed.

HB.instance Definition comp_monoid :=
  Monoid.isLaw.Build (T -> T) idfun comp compA compf1 comp1f.
End CompMonoid.

(* -------------------------------------------------------------------- *)
Lemma eq_bigcomp {I T : Type} (P : pred I) (F1 F2 : I -> T -> T) r :
     (forall x, P x -> F1 x =1 F2 x)
  ->    \big[comp/idfun]_(x <- r | P x) F1 x
     =1 \big[comp/idfun]_(x <- r | P x) F2 x.
Proof.
move=> eqF; elim: r => [|x r ih] v; first by rewrite !big_nil.
rewrite !big_cons; case: ifP => //= Px.
by rewrite ih; apply/eqF.
Qed.

Lemma homo_comp (f g : nat -> nat) :
     {homo f : m n / (m < n)%N}
  -> {homo g : m n / (m < n)%N}
  -> {homo f \o g : m n / (m < n)%N}.
Proof. by move=> hf hg m n /= ltmn; apply/hf/hg. Qed.

Lemma homo_bigcomp {I : Type} (P : pred I) (F : I -> nat -> nat) r :
     (forall x, P x -> {homo F x : m n / (m < n)%N})
  -> {homo \big[comp/idfun]_(x <- r | P x) F x : m n / (m < n)%N}.
Proof.
move=> h; elim: r => [|x r ih]; first by rewrite !big_nil.
move=> m n lt_mn; rewrite big_cons; case: ifPn => [/h Px|_].
by apply/Px/ih. by apply/ih.
Qed.

Lemma homo_geidfun (f : nat -> nat) :
  {homo f : m n / (m < n)%N} -> forall n, (n <= f n)%N.
Proof.
by move=> h; elim => // n ih; apply/(leq_ltn_trans ih)/h.
Qed.

Lemma homo_leq_mono (f : nat -> nat) :
   {homo f : m n / (m <  n)%N} ->
   {mono f : m n / (m <= n)%N}.
Proof.
move=> mf m n /=; case: (leqP m n); last first.
+ by move/mf; rewrite leqNgt ltnS => /negbTE.
by rewrite leq_eqVlt => /orP[/eqP->|/mf/ltnW //]; rewrite leqnn.
Qed.

Lemma homo_ltn_mono (f : nat -> nat) :
   {homo f : m n / (m < n)%N} ->
   {mono f : m n / (m < n)%N}.
Proof.
move=> h x y; apply/idP/idP; [apply/contraLR | by apply/h].
by rewrite -!leqNgt leq_eqVlt => /orP[/eqP->//|/h/ltnW].
Qed.

(* -------------------------------------------------------------------- *)
Lemma pr_drestr {R : realType} {T : choiceType} (mu : {distr T / R}) D E :
  \P_[drestr D mu] E = \P_[mu] [predI D & E].
Proof.
rewrite /pr; apply/eq_psum => x /=; rewrite drestrE /in_mem /=.
by case: (D x); case: (E x); rewrite !Monoid.simpm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma summable_option {R : realType} {T : choiceType} (S : option T -> R) :
  summable (fun x => S (Some x)) <-> summable S.
Proof. split.
+ case/summable_seqP => M ge0_M leM; apply/summable_seqP => /=.
  exists (M + `|S None|); first by rewrite addr_ge0.
  move=> J uqJ; rewrite (bigID isSome) lerD //=.
  - apply/(le_trans _ (leM (pmap idfun J) _)); last first.
    * by apply/(pmap_uniq (g := some)) => // -[].
    rewrite -(big_map _ predT (fun x => `|S x|)) pmapS_filter.
    by rewrite map_id /= big_filter.
  - case/boolP: (None \in J) => NoneJ; last first.
    * rewrite big_seq_cond big_pred0 //= => x; rewrite andbC.
      by case: x => //; rewrite (negbTE NoneJ).
    rewrite (perm_big _ (perm_to_rem NoneJ)) big_cons /=.
    rewrite big_seq_cond big1 ?addr0 // => x.
    by rewrite mem_rem_uniq //= !inE andbAC; case: x.
+ case/summable_seqP => /= M ge0_M leM; apply/summable_seqP.
  exists M => // J uqJ; apply/(le_trans _ (leM (map some J) _)).
  - by rewrite big_map.
  - by rewrite map_inj_uniq // => x y [].
Qed.

(* -------------------------------------------------------------------- *)
Lemma psum_option {R : realType} {T : choiceType} (S : option T -> R) :
  summable S -> psum S = psum (S \o some) + `|S None|.
Proof.
move=> hS; have hSo: summable (S \o some) by apply/summable_option.
rewrite (psumID isSome) //=; congr +%R; last first.
+ rewrite (psum_finseq (r := [:: None])) //; last first.
  * by rewrite big_seq1 mul1r.
  by case=> // a; rewrite !inE /= mul0r eqxx.
rewrite (reindex_psum_onto (h := some) (h' := idfun) (P := isSome)) //=.
+ by case=> //; rewrite mul0r eqxx.
+ by case.
+ by apply/eq_psum=> x; rewrite mul1r.
Qed.


(* -------------------------------------------------------------------- *)
Lemma dinsupp_dlim {R : realType } {T: choiceType} (μ : nat -> {distr T / R}) x :
  x \in dinsupp (dlim μ) ->
    exists K, forall n, (K <= n)%N -> x \in dinsupp (μ n).
Proof.
move/dinsuppP; rewrite dlimE; case: nlimP => // -[] // l cvg.
move/eqP => /= nz_l; have gt0_absl: 0 < `|l| by rewrite normr_gt0.
case/ncvg_abs/(_ (NFin _ gt0_absl)): cvg=> K cvg; exists K => n.
move/cvg; rewrite inE ltr_distl => /andP[h _]; apply/dinsuppP.
by apply/eqP; rewrite -normr_gt0 (le_lt_trans _ h) ?subrr.
Qed.

(* -------------------------------------------------------------------- *)
Lemma homoS_lt (f : nat -> nat) :
   (forall x, (f x < f x.+1)%N) -> {homo f : x y / (x < y)%N}. 
Proof.
move=> homo x y lt_xy; rewrite -(subnK lt_xy).
elim: (y - _)%N => [|n ih]; first by apply/homo.
by rewrite addSn (leq_trans ih) // 1?ltnW.
Qed.

(* -------------------------------------------------------------------- *)
Lemma homoS_ler {T : numDomainType} (f : nat -> T) :
  (forall x, f x <= f x.+1) -> {homo f : x y / (x <= y)%N >-> x <= y}.
Proof.
move=> homo x y lt_xy; rewrite -(subnK lt_xy).
by elim: (y - _)%N => // n ih; rewrite addSn (le_trans ih (homo _)).
Qed.

(* -------------------------------------------------------------------- *)
Lemma natpred_finiteN (E : pred nat) :
     (forall s : seq nat, ~ {subset E <= s})
  -> { σ : nat -> nat |
        {homo σ : x y / (x < y)%N} & forall n, E (σ n)}.
Proof.
move=> finNE; have h s : exists n, (n > \max_(x <- s) x)%N && E n.
+ set N := \max_(x <- s) x; pose r := iota 0 N.+1 ++ s.
  apply: contra_notP (finNE r) => /asboolPn /forallp_asboolPn h x.
  move=> xE; rewrite mem_cat; have /negP := h x.
  rewrite negb_and -leqNgt mem_iota /= add0n ltnS.
  by rewrite /in_mem /= in xE; rewrite xE orbF => ->.
pose ω s : nat := xchoose (h s).
pose σ := fix σ n := if n is n.+1 then ω (σ n) :: σ n else [::].
exists (fun n => head 0%N (σ n.+1)); last first.
+ by move=> n /=; have := xchooseP (h (σ n)) => /andP[].
apply/homoS_lt => /= nl; set r := _ :: _.
have := xchooseP (h r) => /andP[].
by rewrite {1}big_cons gtn_max => /andP[].
Qed.
