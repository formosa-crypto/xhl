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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.
Import numFieldNormedType.Exports.

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
    + by rewrite /lshift => /= /(ord_inj) ->.
    + rewrite /lshift /= => iE; have := ltn_ord i.
      by rewrite iE -{2}[n]addn0 ltn_add2l ltn0.
  Qed.

  Lemma fsplitr (i : 'I_p) : fsplit (rshift n i) = fp i.
  Proof.
    rewrite /fsplit; case: splitP => j; rewrite /rshift /= => jE.
     + by have := ltn_ord j; rewrite -jE -{2}[n]addn0 ltn_add2l ltn0.
     + move /addnI: jE.
       by rewrite /lshift => /= /(ord_inj) ->.
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

  Definition arg_minr := (xchoose arg_min_proof).

  Arguments arg_minr : simpl never.

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
  Proof.
    apply: (iffP idP) => /=.
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

  Lemma sum_eq_set {T: finType} : forall F : T -> \bar R,
    (\sum_(i \in [set: T]) F i = \sum_(i : T) F i)%E.
  Proof.
    move=> F; rewrite fsbig_finite//=.
    apply: perm_big; apply: uniq_perm.
      - exact: fset_uniq.
      - exact: index_enum_uniq.
      - by move=> i; rewrite mem_index_enum in_fset_set //= in_setT.
  Qed.

  Lemma pr_finE {T : finType} (d : {distr T / R}) (E : pred T) :
    \P_[d] E = \sum_i (E i)%:R * d i :> R.
  Proof.
    rewrite /pr (esum_fset finite_finset).
    - by move=> i _;
      rewrite lee_fin; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
    rewrite sum_eq_set.
    under eq_bigr do rewrite /=.
    by rewrite sumEFin.
  Qed.

  (* -------------------------------------------------------------------- *)
  Lemma eqr_in_pr {T : choiceType} (mu1 mu2 : {distr T / R}) E :
    {in E, mu1 =1 mu2} -> \P_[mu1] E = \P_[mu2] E.
  Proof.
    move=> h; rewrite /pr; congr fine.
    apply/eq_esum => x _ /=.
    case/boolP: (E x) => hE.
    + by rewrite !mul1r h.
    + by rewrite !mul0r.
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
  by rewrite enumT  Finite.enum.unlock.
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
  Context (R : pzRingType) (m n : nat).

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
  rewrite /pr; congr fine.
  apply/eq_esum => x /=; rewrite drestrE /in_mem /=.
  by case: (D x); case: (E x); rewrite !Monoid.simpm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma hset {T: choiceType} :
  ([set: option T] `&` ~` [set None] = Some @` [set: T])%classic.
Proof.
  apply/seteqP; split=> o.
  - by case: o => [x|] /= [_ H]; [exists x | case: (H erefl)].
  - by move=> [x _ <-].
Qed.

Lemma esummable_option {R : realType} {T : choiceType} (S : option T ->  \bar R) :
  esummable [set: option T] S -> esummable [set: T] (S \o some ).
Proof.
rewrite !esummableE.
rewrite (esumID [set None] [set: option T]); first by move=> ? _; exact: abse_ge0.
rewrite setTI esum_set1 hset esum_image; first by move=> x y _ _ [->].
by rewrite fin_numD => /andP[].
Qed.

Lemma esum_option {R : realType} {T : choiceType} (S : option T -> \bar R) :
  esummable [set: option T] S ->
  esum [set: option T] S = esum [set: T] (S \o some) + (S None).
Proof.
move=> hS.
pose f1 := fun i : option T => if i \in ([set None])%classic then S i else 0.
pose f2 := fun i : option T => if i \in (~` [set None])%classic then S i else 0.
have hf1 : esummable [set: option T] f1.
  rewrite esummableE /f1.
  under eq_esum => i _ do rewrite (fun_if abse) abse0.
  rewrite -esum_mkcondr setTI esum_set1 abse_fin_num.
  by rewrite fin_num_abs; apply: (esummable_pinfty hS).
have hf2 : esummable [set: option T] f2.
  rewrite esummableE /f2.
  under eq_esum => i _ do rewrite (fun_if abse) abse0.
  rewrite -esum_mkcondr hset esum_image; first by move=> x y _ _ [->].
  have : esummable [set: T] (S \o some) by apply/esummable_option.
  by rewrite esummableE.
have e1 : esum [set: option T] f1 = S None.
  by rewrite /f1 -esum_mkcondr setTI esum_set1.
have e2 : esum [set: option T] f2 = esum [set: T] (S \o some).
  rewrite /f2 -esum_mkcondr hset esum_image; first by move=> x y _ _ [->].
  by [].
have hsum : esum [set: option T] S
  = (esum [set: option T] f1 + esum [set: option T] f2)%E.
  rewrite -(esummable_esumD hf1 hf2).
  apply: eq_esum => i _; rewrite /f1 /f2 in_setC.
  by case: (i \in ([set None])%classic); rewrite /= (adde0, add0e).
by rewrite hsum e1 e2 addeC.
Qed.

(* ==================================================================== *)
(* Real-valued sums, replacing [realsum]'s [psum].                       *)
(*                                                                      *)
(* [rsum f] reads the [esum] of [f] back into [R].  For a non-negative   *)
(* [f] this agrees with [psum] even off the summable case: there         *)
(* [esum f = +oo] and [fine +oo = 0], matching [psum_out].               *)
(* The converse of [esummable_option].  It needs an [EFin]-valued family: *)
(* for a general [S] the value [S None] could be infinite, which defeats  *)
(* summability on [option T] while leaving it intact on [T].              *)
Lemma esummable_optionT {R : realType} {T : choiceType} (f : option T -> R) :
  esummable [set: T] (EFin \o (f \o some)) ->
  esummable [set: option T] (EFin \o f).
Proof.
rewrite !esummableE.
rewrite (esumID [set None] [set: option T]); first by move=> ? _; exact: abse_ge0.
rewrite setTI esum_set1 hset esum_image; first by move=> x y _ _ [->].
by move=> h; rewrite fin_numD; apply/andP; split.
Qed.

(* Scaling commutes with [fine] unconditionally: on every non-finite     *)
(* value both sides are [0].  [fineM] instead needs both arguments to be  *)
(* [fin_num], which is what [rsumZ] must avoid in order to match          *)
(* [realsum]'s hypothesis-free [psumZ].                                   *)
Lemma fineMl {R : realType} (c : R) (x : \bar R) :
  fine (c%:E * x) = c * fine x.
Proof.
case: x => [r||] /=; first by [].
+ rewrite mulr0; case: (ltgtP c 0) => [c0|c0|->]; last by rewrite mul0e.
  * by rewrite muleC (lt0_mulye (x := c%:E)) // lte_fin.
  * by rewrite muleC (gt0_mulye (x := c%:E)) // lte_fin.
+ rewrite mulr0; case: (ltgtP c 0) => [c0|c0|->]; last by rewrite mul0e.
  * by rewrite (lt0_muleNy (x := c%:E)) // lte_fin.
  * by rewrite (gt0_muleNy (x := c%:E)) // lte_fin.
Qed.

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

(* the workhorse: on a summable family [rsum] is the honest [esum] *)
Lemma rsumE f : esummable [set: T] (EFin \o f) ->
  (rsum f)%:E = \esum_(x in [set: T]) (f x)%:E.
Proof.
move=> sf; rewrite /rsum fineK //.
by apply: (esummable_esum_fin_num sf).
Qed.

(* a uniform bound on the finite subsums bounds the whole [esum] *)
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

(* conversely, every finite subsum is below [rsum] *)
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

(* no summability needed, matching [realsum]'s [psumZ] *)
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

End RSum.

(* -------------------------------------------------------------------- *)
(* On a [finType] an [rsum] is an ordinary finite sum.  Replaces         *)
(* [realsum]'s [psum_fin], without its absolute values.                  *)
Lemma rsum_fin {R : realType} {I : finType} (f : I -> R) :
  (forall i, 0 <= f i) -> rsum f = \sum_i f i.
Proof.
move=> f0; rewrite /rsum (esum_fset finite_finset).
- by move=> i _; rewrite lee_fin.
by rewrite sum_eq_set sumEFin.
Qed.

(* -------------------------------------------------------------------- *)
(* [realsum]'s [psum_finseq]: a family supported on a finite [r] sums    *)
(* to the plain finite sum over [r].                                     *)
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

(* -------------------------------------------------------------------- *)
(* [realsum]'s [le1_mu], in [rsum] form *)
Lemma le1_rsum {R : realType} {T : choiceType} (mu : {distr T / R}) :
  rsum mu <= 1.
Proof.
by rewrite -lee_fin (rsumE (summable_mu mu)); exact: le1_mu.
Qed.

(* -------------------------------------------------------------------- *)
(* [pr] as an [rsum], so that the [rsum] theory applies to it *)
Lemma prE_rsum {R : realType} {T : choiceType}
    (mu : {distr T / R}) (E : pred T) :
  \P_[mu] E = rsum (fun x => (E x)%:R * mu x).
Proof. by []. Qed.

(* [realseq]'s [ncvgZ] / [ncvgMl] for a constant scalar *)
Lemma cvgZl {R : realType} (u : nat -> R) (l c : R) :
  (u @ \oo --> l)%classic -> ((fun n => c * u n) @ \oo --> c * l)%classic.
Proof. by move=> hu; apply: cvgM => //; exact: cvg_cst. Qed.

(* [cvgD] / [cvgB] stated on an explicit lambda rather than on the       *)
(* pointwise ring structure of [nat -> R]: the latter lives in           *)
(* [mathcomp.classical.functions], which the client files do not import. *)
Lemma cvgnD {R : realType} (u v : nat -> R) (a b : R) :
     (u @ \oo --> a)%classic -> (v @ \oo --> b)%classic
  -> ((fun n => u n + v n) @ \oo --> a + b)%classic.
Proof. move=> hu hv; exact (cvgD hu hv). Qed.

Lemma cvgnB {R : realType} (u v : nat -> R) (a b : R) :
     (u @ \oo --> a)%classic -> (v @ \oo --> b)%classic
  -> ((fun n => u n - v n) @ \oo --> a - b)%classic.
Proof. move=> hu hv; exact (cvgB hu hv). Qed.

(* -------------------------------------------------------------------- *)
(* [counting_distr]'s [dlim] is [limn_einf]-based, so it only agrees     *)
(* with the pointwise limit on convergent sequences -- which is exactly  *)
(* the situation [strassen]'s [strcvg] produces (convergent, but not     *)
(* monotone, so [dlim_limE] does not apply).                            *)
Lemma dlimE_cvg {R : realType} {T : choiceType}
    (f : nat -> {distr T / R}) x :
  cvgn (fun n => f n x) -> dlim f x = limn (fun n => f n x).
Proof.
move=> cf; rewrite dlimE.
have hE : ((EFin \o (fun n => f n x)) @ \oo
             --> (limn (fun n => f n x))%:E)%classic.
+ by apply: cvg_EFin; [apply: nearW | exact: cf].
have -> : limn_einf (fun n => (f n x)%:E) = (limn (fun n => f n x))%:E.
+ rewrite is_cvg_limn_einfE; first by apply: cvgP hE.
  by apply: cvg_lim hE.
by [].
Qed.

(* -------------------------------------------------------------------- *)
(* scaling preserves summability (real scalar) *)
Lemma esummableZ {R : realType} {T : choiceType} (f : T -> R) (c : R) :
  esummable [set: T] (EFin \o f) ->
  esummable [set: T] (EFin \o (fun x => c * f x)).
Proof.
move=> sf; apply: (eq_esummable (f := fun x => (c%:E * (f x)%:E)%E)).
+ by move=> x _ /=; rewrite EFinM.
by apply: esummableZl => //; exact: sf.
Qed.

(* -------------------------------------------------------------------- *)
(* marginals as [rsum]s -- the shape [rsum] lemmas can act on *)
Lemma dfstE_rsum {R : realType} {T U : choiceType}
    (mu : {distr (T * U)%type / R}) x :
  dfst mu x = rsum (fun y => mu (x, y)).
Proof. by rewrite dfstE. Qed.

Lemma dsndE_rsum {R : realType} {T U : choiceType}
    (mu : {distr (T * U)%type / R}) y :
  dsnd mu y = rsum (fun x => mu (x, y)).
Proof. by rewrite dsndE. Qed.

(* -------------------------------------------------------------------- *)
(* finType marginals as ordinary finite sums *)
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

(* -------------------------------------------------------------------- *)
(* [realsum]'s [nboundedP], in the [bounded_fun] vocabulary that         *)
(* [bolzano_weierstrass] expects.                                        *)
Lemma bounded_funP {R : realType} (u : nat -> R) (M : R) :
  (forall n, `|u n| <= M) -> bounded_fun u.
Proof.
move=> h.
have PF : ProperFilter (globally [set: nat]).
+ by apply: (globally_properfilter (a := 0%N)).
have [_ hh] := ex_bound u (F := globally [set: nat]).
by apply: hh; exists M => n _; exact: h.
Qed.

(* -------------------------------------------------------------------- *)
(* [realsum]'s [iscvg_sub]: convergence is stable under passing to a     *)
(* subsequence.                                                          *)
Lemma cvg_homo_oo (s : nat -> nat) :
  {homo s : x y / (x < y)%N} -> (s @ \oo --> \oo)%classic.
Proof.
move=> homo_s; apply/cvgnyPge => N; near=> n.
by apply: (leq_trans _ (homo_geidfun homo_s n)); near: n; apply: nbhs_infty_ge.
Unshelve. all: end_near. Qed.

Lemma cvgn_subseq {R : realType} (u : nat -> R) (s : nat -> nat) :
  {homo s : x y / (x < y)%N} -> cvgn u -> cvgn (u \o s).
Proof.
move=> homo_s cu; apply: cvgP.
by apply: (cvg_comp s u (cvg_homo_oo homo_s) cu).
Qed.

(* [realsum]'s [iscvg_eq] -- trivial with [funext] *)
Lemma cvgn_eq {R : realType} (u v : nat -> R) : u =1 v -> cvgn v -> cvgn u.
Proof. by move=> /funext ->. Qed.

(* [realsum]'s [iscvg_shift]; not in mathcomp-analysis, which only has  *)
(* the [--> l] form [cvg_shiftn].                                        *)
Lemma is_cvg_shiftn {R : realType} (N : nat) (u : nat -> R) :
  cvgn (fun n => u (n + N)%N) = cvgn u.
Proof.
rewrite propeqE; split=> /cvg_ex[l hl]; apply/cvg_ex; exists l;
  by move: hl; rewrite (cvg_shiftn N u (nbhs l)).
Qed.

(* -------------------------------------------------------------------- *)
(* reindexing along an injection whose image carries the whole family;   *)
(* replaces [realsum]'s [reindex_psum]                                   *)
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

(* -------------------------------------------------------------------- *)
(* replaces [realsum]'s [psum_pair]; only slice summability is needed    *)
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

(* -------------------------------------------------------------------- *)
(* replaces [realsum]'s [psum_pair_swap] *)
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

(* -------------------------------------------------------------------- *)
Lemma rsum_option {R : realType} {T : choiceType} (f : option T -> R) :
  esummable [set: option T] (EFin \o f) ->
  rsum f = rsum (f \o some) + f None.
Proof.
move=> sf; have sfs := esummable_option sf.
rewrite /rsum (esum_option sf) fineD //.
by apply: (esummable_esum_fin_num sfs).
Qed.

(* -------------------------------------------------------------------- *)
Lemma esummable_condl {R : realType} {T : choiceType}
    (f : T -> R) (P : pred T) :
  esummable [set: T] (EFin \o f) ->
  esummable [set: T] (EFin \o (fun x => (P x)%:R * f x)).
Proof.
move=> sf.
apply: (eq_esummable (f := ((fun x => ((P x)%:R)%:E) \* (EFin \o f))%E)).
+ by move=> x _ /=; rewrite EFinM.
apply: esummableMl; last exact: sf.
exists 1%:E => [x|]; last by [].
by rewrite gee0_abs ?lee_fin ?ler0n// lern1 leq_b1.
Qed.

(* -------------------------------------------------------------------- *)
(* Was provided by [realsum]; pure [sup] fact, no distribution content.  *)
Lemma max_sup {R : realType} x (E : set R) :
  (E `&` ubound E)%classic x -> sup E = x.
Proof.
case=> /= xE xubE; have nzE: nonempty E by exists x.
apply/eqP; rewrite eq_le ge_sup //=.
have : has_sup E by split; exists x.
by move/sup_upper_bound/ubP; apply.
Qed.

(* -------------------------------------------------------------------- *)
(* [counting_distr] builds distributions by declaring an [HB.instance]   *)
(* on a named function, which is a command and so unusable inside a      *)
(* proof.  The [Distribution] structure is a plain record with exposed   *)
(* constructors, so the term-level builder of the old [distr] library    *)
(* is recoverable.                                                       *)
Definition mkdistr {R : realType} {T : choiceType} (f : T -> R) (h : isdistr f)
  : {distr T / R} := Distribution.Pack (Distribution.Class (@mkdistrd R T f h)).

Lemma mkdistrE {R : realType} {T : choiceType} (f : T -> R) (h : isdistr f) :
  mkdistr h =1 f.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma dinsupp_dlim {R : realType } {T: choiceType} (μ : nat -> {distr T / R}) x :
  x \in dinsupp (dlim μ) ->
        exists K, forall n, (K <= n)%N -> x \in dinsupp (μ n).
Proof.
rewrite in_dinsupp => nz; pose u := fun n : nat => (μ n x)%:E.
have supE : sequences.limn_einf u = ereal_sup (range (sequences.einfs u)).
  rewrite sequences.limn_einf_lim.
  by apply/cvg_lim => //; exact: sequences.cvg_einfs_sup.
have [K gtK] : exists K, (0 < sequences.einfs u K)%E.
  have /ereal_sup_gt[y [K _ <-] gtK] :
      (0 < ereal_sup (range (sequences.einfs u)))%E.
    by rewrite -supE /u -dlim_EFin lte_fin lt0r nz (ge0_dlim μ x).
  by exists K.
exists K => n leKn; apply/dinsuppP => eq0.
have un0 : u n = 0%E by rewrite /u eq0.
by move: (einfs_le u leKn); rewrite un0 leNgt gtK.
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
