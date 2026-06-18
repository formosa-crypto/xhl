(* -------------------------------------------------------------------- *)
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp           Require Import all_boot all_order.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
(* ----------------- *) Require Import inhabited passn pwhile.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.

Section BigExtra.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).

Lemma bigD1_seq_cond (I : eqType) (r : seq I) j (P : pred I) F :
    j \in r -> uniq r ->
  \big[op/idx]_(i <- r | P i) F i
	=	if P j then
			op (F j) (\big[op/idx]_(i <- r | P i && (i != j)) F i)
		else
			\big[op/idx]_(i <- r | P i && (i != j)) F i.
Proof.
move=> H1 H2.
by rewrite (big_rem_AC _ _ _ _ H1) !rem_filter // !big_filter_cond big_andbC.
Qed.

Lemma partition_big_seq {I J : eqType} (h : I -> J) (P Q : pred _) F (s : seq I) (s' : seq J):
	uniq s'
	-> (forall x, x \in s -> P x -> (h x) \in s' /\ Q (h x))
	-> \big[op/idx]_(i <- s | P i) F i = \big[op/idx]_(j <- s' | Q j) \big[op/idx]_(i <- s | P i && (h i == j)) F i.
Proof.
move=> uq_s'.
elim: s=> /= [|x xs ih] hm.
+ rewrite big_nil.
	under eq_bigr=> j _ do rewrite big_nil.
	by rewrite [RHS]big1_eq.
rewrite big_cons. 
case: ifPn=> /= [Px|/negP PxN]; last first.
+ rewrite ih //.
	+ apply eq_bigr=> i _.
		rewrite big_cons.
		case: ifPn=> //.
		by move=> /andP [].
	move=> y y_xs.
	apply hm.
	by rewrite in_cons y_xs orbT.
have := hm x.
rewrite Px in_cons eq_refl /==> - []// s'_px Qpx.
apply Logic.eq_sym.
rewrite (bigD1_seq_cond _ _ s'_px uq_s') Qpx /= big_cons /= Px /= eq_refl.
rewrite -Monoid.mulmA.
congr (op _ _).
apply Logic.eq_sym.
rewrite ih; first last.
+ move=> y y_xs.
	apply hm.
	by rewrite in_cons y_xs orbT.
rewrite (bigD1_seq_cond _ _ s'_px uq_s') Qpx /=.
congr (op _ _).
apply eq_bigr=> j /andP [] Qj.
rewrite eq_sym=> /eqP ne_pxj.
rewrite big_cons.
case: ifPn=> //. 
by move=> /andP [] _ /eqP.
Qed.

End BigExtra.

Section SeqExtra.

Lemma mem_pair {T S : choiceType} (s : seq (T * S)) x: (x \in s) -> (x.1 \in unzip1 s) && (x.2 \in unzip2 s).
Proof.
elim: s.
+ move=> /=.
	by rewrite in_nil.
move=> y ys H.
rewrite in_cons.
case /orP.
+ move=> /eqP -> /=.
	by rewrite !in_cons !eq_refl.
move=> /H /andP [].
rewrite /= !in_cons=> -> -> /=.
by rewrite !orbT.
Qed.

End SeqExtra.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope mem_scope.

Notation ROHS := (X in X <= _)%pattern.
Notation LOHS := (X in _ <= X)%pattern.

Declare Scope sem_scope.

(* -------------------------------------------------------------------- *)
Module Ad.
Definition dlet_lim := @__admitted__dlet_lim.
Definition dlim_let := @__admitted__dlim_let.
End Ad.
Import Ad.

(* -------------------------------------------------------------------- *)
Axiom funext : forall {T U : Type} (f g : T -> U),
  (forall x, f x = g x) -> f = g.

Lemma funext2 : forall {T U V : Type} (f g : T -> U -> V),
  (forall x y, f x y = g x y) -> f = g.
Proof. by move=> T U V f g eq; apply/funext=> x; apply/funext. Qed.

(* -------------------------------------------------------------------- *)
Lemma distr_eqP {T : choiceType} (f1 f2 : Distr T): 
  f1 =1 f2 <-> f1 = f2.
Proof. 
split=> [|->] //; case: f1 f2 => [mu1 ge0_1 s1 le1_1] [mu2 ge0_2 s2 le1_2].
move/funext => /= eq_mu; have PI (A : Prop): A \/ ~ A by case: (asboolP A); auto.
by subst; f_equal; apply proof_irrelevance_cci.
Qed.

(* -------------------------------------------------------------------- *)
Section DistrRecast.
Variables (T U V : choiceType) (f g : T -> Distr U) (mu nu : Distr T).

Lemma dlet_null : \dlet_(i <- dnull) f i = dnull.
Proof. by apply/distr_eqP/dlet_null. Qed.

Lemma dlet_unit x : \dlet_(i <- dunit x) f i = f x.
Proof. by apply/distr_eqP/dlet_unit. Qed.

Lemma dlet_if b :
    \dlet_(t <- if b then mu else nu) f t
  =  if b then \dlet_(t <- mu) f t else \dlet_(t <- nu) f t.
Proof. by case:ifP. Qed.

Lemma dlet_dlet (f1 : T -> Distr U) (f2 : U -> Distr V) :
    \dlet_(x <- \dlet_(y <- mu) f1 y) f2 x
  = \dlet_(y <- mu) \dlet_(x <- f1 y) f2 x.
Proof. by apply/distr_eqP/dlet_dlet. Qed.

Lemma eq_in_dlet :
  {in dinsupp mu, f =1 g} -> mu = nu ->
  \dlet_(i <- mu) f i = \dlet_(i <- nu) g i.
Proof.
by move=> eqf <-; apply/distr_eqP/eq_in_dlet=>// x /eqf ->.
Qed.

Lemma eq_dlim (fn gn : nat -> Distr T):
  fn =1 gn -> \dlim_(n) fn n = \dlim_(n) gn n.
Proof. by move=> eq_fg; apply/distr_eqP/eq_dlim=> ??; rewrite eq_fg. Qed.

Lemma dlet_dmargin (f1 : T -> U) (g1 : U -> Distr V):
       \dlet_(u <- dmargin f1 mu) g1 u = \dlet_(t <- mu) g1 (f1 t).
Proof. apply /distr_eqP/dlet_dmargin. Qed.

Lemma dmargin_dlet (f1 : U -> V) (g1 : T -> Distr U):
       dmargin f1 (\dlet_(t <- mu) g1 t) = \dlet_(t <- mu) dmargin f1 (g1 t).
Proof. apply /distr_eqP/dmargin_dlet. Qed.

Lemma dmargin_dunit (t : T) (f1 : T -> U):
   @dmargin R _ _ f1 (dunit t) = dunit (f1 t).
Proof. apply /distr_eqP/dmargin_dunit. Qed.

Lemma dlet_dunit_id : \dlet_(t <- mu) (dunit t) = mu :> Distr T.
Proof. by apply/distr_eqP/dlet_dunit_id. Qed.

Lemma dlim_let (h : nat -> T -> Distr U) (d : Distr T) :
  (forall x n m, (n <= m)%N -> h n x <=1 h m x) ->
    \dlim_(n) \dlet_(x <- d) (h n x) =
      \dlet_(x <- d) \dlim_(n) (h n x).
Proof. by move=> ?; apply/distr_eqP/dlim_let. Qed.

Lemma dlimC: \dlim_(_) mu = mu.
Proof. by apply/distr_eqP/dlimC. Qed.
End DistrRecast.

(* -------------------------------------------------------------------- *)
Section DLimRecast.
Variables (T U : choiceType).
Variables (f : nat -> {distr T / R}) (h : T -> {distr U / R}).

Lemma dlet_lim : (forall n m, (n <= m)%N -> f n <=1 f m) ->
  \dlet_(x <- \dlim_(n) f n) h x = \dlim_(n) \dlet_(x <- f n) h x.
Proof. by move=> ?; apply/distr_eqP/dlet_lim. Qed.
End DLimRecast.

(* -------------------------------------------------------------------- *)
Section DProj.
Context {T : choiceType} (mu : Distr (T * T)).

Lemma dprojE s x :
  dmargin (fst, snd)#s mu x =
    psum (fun y => mu ((x, y)#s, (y, x)#s)).
Proof. by case: s => /=; rewrite ?(dfstE, dsndE). Qed.

Lemma summable_proj s x1 :
  summable (fun x2 => mu ((x1, x2)#s, (x2, x1)#s)).
Proof. by case: s => /=; [apply/summable_fst | apply/summable_snd]. Qed.
End DProj.


(* -------------------------------------------------------------------- *)
Section DProd.
Context {T S: choiceType}.

Definition mprod (mu1 : {distr T / R}) (mu2 : {distr S / R}) v := mu1 v.1 * mu2 v.2.

Lemma isd_mprod mu1 mu2: isdistr (mprod mu1 mu2).
Proof.
split=> [x|s uqs].
+ by apply/mulr_ge0; apply/ge0_mu.
rewrite (@partition_big_seq _ _ _ _ _ fst _ predT _ _ (undup (unzip1 s))); first last.
+ move=> x /mem_pair /andP [] + _ _ /=.
	by rewrite mem_undup => ->.
+ by apply undup_uniq.
rewrite /prod /=.
rewrite (@eq_bigr _ _ _ _ _ _ _ (fun j => mu1 j * \sum_(i <- s | i.1 == j) mu2 i.2)); last first.
+ move=> x _.
	by rewrite mulr_sumr; apply/eq_bigr=> -[v w] /= /eqP <-.
apply (@le_trans _ _ (\sum_(i <- undup (unzip1 s)) `| mu1 i |)); first last.
+ apply (@le_trans _ _ (psum mu1)); last by apply le1_mu.
	apply ger_big_psum.
	+ by apply undup_uniq.
	by apply summable_mu.
apply ler_sum=> x _.
rewrite ger0_norm; last by apply ge0_mu.
apply ler_piMr; first by apply ge0_mu.
rewrite -big_filter.
rewrite -(@big_map _ _ _ _ _ snd _ predT).
apply (@le_trans _ _ (psum mu2)); last by apply le1_mu.
under eq_bigr=> i _.
+ rewrite -(@ger0_norm _ (mu2 i)); last by apply ge0_mu.
	by over.
apply ger_big_psum; last by apply summable_mu.
rewrite map_inj_in_uniq ?filter_uniq //.
case=> [a1 b1] [c1 d1].
by rewrite !mem_filter /==> - /andP [/eqP <- _] /andP [/eqP -> _] ->.
Qed.

Definition dprod mu1 mu2 := locked (mkdistr (isd_mprod mu1 mu2)).

Lemma dprodE mu1 mu2 x: (dprod mu1 mu2) x = mu1 x.1 * mu2 x.2.
Proof.
by unlock dprod.
Qed.
End DProd.

Section DProdLemmas.

Lemma dprod_dlet {T S : choiceType} (mu1 : {distr T / R}) (mu2 : {distr S / R}): dprod mu1 mu2 = \dlet_(x <- mu1) \dlet_(y <- mu2) dunit (x, y).
Proof.
apply distr_eqP=> - [u v].
rewrite dprodE dletE /=.
under eq_psum=> x.
+ rewrite dletE.
	under eq_psum=> y do rewrite dunit1E.
	rewrite -psumZ; last by apply ge0_mu.
	rewrite (@eq_psum _ _ _ (fun y => mu1 u * mu2 v * (x == u)%:R * (y == v)%:R)); first by over.
	move=> y /=.
	have [] := eqVneq (x, y) (u, v).
	+ rewrite pair_equal_spec=> - [-> ->].
		by rewrite !eq_refl !mulr1.
	move=> /eqP.
	rewrite pair_equal_spec not_andP.
	case=> /eqP.
	+ case: (x == u)=> //=.
		by rewrite !mulr0 mul0r.
	case: (y == v)=> //=.
	by rewrite !mulr0.
rewrite psum_sum; first last.
+ move=> x.
	apply ge0_psum.
under eq_sum=> x.
+ rewrite psum_sum; first last.
	+ move=> y.
		apply mulr_ge0.
  	+	apply mulr_ge0.
			+ by apply mulr_ge0; apply ge0_mu.
			by case: (x == u).
		by case: (y == v).
	rewrite sumZ (sum_seq1 v).
	+ rewrite eq_refl mulr1.
		by over.
	move=> y.
	rewrite [y == v]eq_sym.
	case: (v == y)=> //.
	by rewrite eq_refl.
rewrite sumZ (sum_seq1 u).
+ by rewrite eq_refl mulr1.
move=> x.
rewrite [x == u]eq_sym.
case: (u == x)=> //.
by rewrite eq_refl.
Qed.

Lemma dlet_swap {T U V: choiceType} (d1 : {distr T / R}) (d2 : {distr U / R}) (F : T -> U -> {distr V / R}):
    \dlet_(x1 <- d1) (\dlet_(x2 <- d2) F x1 x2)
  = \dlet_(x2 <- d2) (\dlet_(x1 <- d1) F x1 x2).
Proof.
apply distr_eqP=> c; rewrite !dletE.
pose G ab := (dprod d1 d2 ab) * (fun v => F v.1 v.2) ab c.
under eq_psum=> x.
+ rewrite dletE -psumZ; last by apply ge0_mu.
	rewrite (@eq_psum R U _ (fun y => G (x, y))); first by over.
	move=> y /=.
	by rewrite /G /= mulrA dprodE.
under [RHS]eq_psum=> y.
+ rewrite dletE -psumZ; last by apply ge0_mu.
	rewrite (@eq_psum R T _ (fun x => G (x, y))); first by over.
	move=> x /=.
	by rewrite /G dprodE /= mulrA [d2 y * _]mulrC.
have sumG : summable G.
+ by apply summable_mlet.
by rewrite -psum_pair // -psum_pair_swap.
Qed.

Lemma dprod_dnull1 {T S : choiceType} (mu : {distr S / R}): dprod (dnull : {distr T / R}) mu = dnull.
Proof. by rewrite dprod_dlet dlet_null. Qed.

Lemma dprod_dnull2 {T S : choiceType} (mu : {distr T / R}): dprod mu (dnull : {distr S / R}) = dnull.
Proof. by rewrite dprod_dlet dlet_swap dlet_null. Qed.

End DProdLemmas.

Section DGlue.
Context {T S U: choiceType}.

Definition mglue (mu12 : {distr (T * S) / R}) (mu23 : {distr (S * U) / R}) (mu2 : {distr S / R}) (v : T * S * U)
	:= if mu2 v.1.2 != 0 then mu12 v.1 * mu23 (v.1.2, v.2) / mu2 v.1.2 else 0.

Lemma isd_mglue mu12 mu23 mu2: dsnd mu12 = mu2 -> dfst mu23 = mu2 -> isdistr (mglue mu12 mu23 mu2).
Proof.
move=> cpl1 cpl2.
split=> [x|s uqs].
+ rewrite /mglue.
	case: ifPn=> // /eqP neq0.
	apply mulr_ge0.
	+ by apply mulr_ge0; apply ge0_mu.
	rewrite invr_ge0.
	by apply ge0_mu.
rewrite /mglue.
rewrite -big_mkcond /=.
rewrite (@partition_big_seq _ _ _ _ _ (fun v => v.1.2) _ predT _ _ (undup (unzip2 (unzip1 s)))); first last.
+ move=> x /mem_pair /andP [] + _ _ /=.
	move=> /mem_pair /andP [] _.
	by rewrite mem_undup => ->.
+ by apply undup_uniq.
rewrite /=.
rewrite (@eq_bigr _ _ _ _ _ _ _ (fun j => (\sum_(i <- s | (mu2 j != 0) && (i.1.2 == j)) mu12 (i.1.1, j) * mu23 (j, i.2) / mu2 j))); last first.
+ move=> x _.
	apply eq_big.
	+ move=> [] [] u v w /=.
		by have [-> |] := eqVneq v x; rewrite ?andbF ?andbT.
	by move=> [] [] u v w /andP [_ /eqP <-].
apply (@le_trans _ _ (\sum_(i <- undup (unzip2 (unzip1 s))) `| mu2 i |)); first last.
+ apply (@le_trans _ _ (psum mu2)); last by apply le1_mu.
	apply ger_big_psum.
	+ by apply undup_uniq.
	by apply summable_mu.
apply ler_sum=> x _.
rewrite ger0_norm; last by apply ge0_mu.
case H: (mu2 x != 0)=> /=; move: H=> /eqP H; first last.
+	by rewrite big_pred0_eq H.
rewrite -mulr_suml ler_pdivrMr; first last.
+ rewrite lt0r ge0_mu.
	by move: H=> /eqP ->.
rewrite (@partition_big_seq _ _ _ _ _ (fun v => v.1.1) _ predT _ _ (undup (unzip1 (unzip1 s)))); first last.
+ move=> y /mem_pair /andP [] + _ _ /=.
	move=> /mem_pair /andP [].
	by rewrite mem_undup => ->.
+ by apply undup_uniq.
rewrite (@eq_bigr _ _ _ _ _ _ _ (fun j => mu12 (j, x) * (\sum_(i <- s | (i.1.2 == x) && (i.1.1 == j)) mu23 (x, i.2)))); last first.
+ move=> y _.
	rewrite mulr_sumr.
	apply eq_bigr.
	by move=> [] [] u v w /andP [_ /eqP <-].
move: H=> /eqP H.
apply (@le_trans _ _ ((\sum_(i <- undup (unzip1 (unzip1 s))) `| mu12 (i, x) |) * mu2 x)); first last.
+ rewrite -ler_pdivrMr; last by rewrite lt0r ge0_mu H.
	rewrite -mulrA divff // mulr1.
	rewrite -cpl1 dsndE.
	apply ger_big_psum.
	+ by apply undup_uniq.
	by apply summable_snd.
rewrite mulr_suml.
apply ler_sum=> y _.
rewrite ger0_norm; last by apply ge0_mu.
have [-> | H2] := eqVneq (mu12 (y, x)) 0.
+ by rewrite !mul0r.
+ rewrite -ler_pdivrMl; last by rewrite lt0r ge0_mu H2.
	rewrite mulrA [_ * mu12 _]mulrC divff // mul1r.
	rewrite -cpl2 dfstE.
rewrite (@partition_big_seq _ _ _ _ _ (fun v => v.2) _ predT _ _ (undup (unzip2 s))); first last.
+ move=> z /mem_pair /andP [] _ /=.
	by rewrite mem_undup => ->.
+ by apply undup_uniq.
apply (@le_trans _ _ ((\sum_(i <- undup (unzip2 s)) `| mu23 (x, i) |))); first last.
	apply ger_big_psum.
	+ by apply undup_uniq.
	by apply summable_fst.
apply ler_sum=> z _.
rewrite ger0_norm; last by apply ge0_mu.
rewrite big_seq_cond /=.
case H3: ((y, x, z) \in [seq i <- s | (i.1.2 == x) && (i.1.1 == y) & i.2 == z]); first last.
+ move: H3.
	rewrite mem_filter !eq_refl /=.
	move=> H3.
	rewrite (@eq_bigl _ _ _ _ _  _ pred0).
	+ by rewrite big_pred0_eq.
	move=> [[]] v1 v2 v3 /=.
	have [->|] := eqVneq v2 x; last by rewrite /= andbF.
	have [->|] := eqVneq v1 y; last by rewrite /= andbF.
	have [->|] := eqVneq v3 z; last by rewrite /= andbF.
	by rewrite H3.
rewrite -big_seq_cond.
rewrite -big_filter.
rewrite (@bigD1_seq _ _ _ _ _ (y, x, z)) //=.
rewrite big_filter_cond.
rewrite big_pred0.
+ by rewrite addr0.
	move=> [[]] v1 v2 v3 /=.
	have [->|//] := eqVneq v2 x.
	have [->|//] := eqVneq v1 y.
	have [->|//] := eqVneq v3 z.
	by rewrite eq_refl.
by apply filter_uniq.
Qed.

Variables  (mu12 : {distr (T * S) / R}) (mu23 : {distr (S * U) / R}) (mu2 : {distr S / R}).
Hypothesis (cpl1 : dsnd mu12 = mu2) (cpl2 : dfst mu23 = mu2).

Definition dglue := locked (mkdistr (isd_mglue cpl1 cpl2)).
Lemma dglueE v: dglue v = if mu2 v.1.2 != 0 then mu12 v.1 * mu23 (v.1.2, v.2) / mu2 v.1.2 else 0.
Proof.
by unlock dglue.
Qed.

Lemma proj_glue1 : dfst mu12 = dfst (dmargin (fun v => (v.1.1, v.2)) dglue).
Proof.
apply distr_eqP=> v.
rewrite dfstE /= !dmarginE /= !dlet_dlet dletE /=.
rewrite psum_pair; first last.
+ by apply summable_mlet.
under [RHS]eq_psum.
move=> x.
under eq_psum.
move=> y.
rewrite dlet_unit dglueE dunit1E /=.
over.
have ->: psum (fun y : U => (if mu2 x.2 != 0 then mu12 x * mu23 (x.2, y) / mu2 x.2 else 0) * (x.1 == v)%:R)
				=	mu12 x * ((mu2 x.2 != 0) && (x.1 == v))%:R.
+ case H: ((mu2 x.2 != 0) && (x.1 == v)); move: H; first last.
	+ move /negP/negP.
		rewrite negb_and=> /orP.
		case.
		+ move=> /negbNE/eqP ->.
			by rewrite mulr0 eq_refl psum_eq0 //= mul0r.
		case: (x.1 == v)=> //=.
		rewrite mulr0 psum_eq0 //.
		by move=> w; rewrite mulr0.
	move=> /andP [/[dup] neq0mu2 -> ->] /=.
	under eq_psum=> w do rewrite mulr1.
	rewrite mulr1 -[RHS]mulr1.
	have <- := divff neq0mu2.
	rewrite mulrA -{2}cpl2 dfstE.
	rewrite -psumZ; last by apply ge0_mu.
	rewrite -psumZr; first last.
	+ rewrite invr_ge0.
		by apply ge0_mu.
	by apply eq_psum.
over.
rewrite psum_pair_swap /=; last by apply/summable_condr/summable_mu.
apply eq_psum=> w.
have [|neq0] /= := eqVneq (mu2 w) 0.
+ rewrite psum_eq0 //; last	by move=> ?; rewrite mulr0.
	rewrite -cpl1 dsndE.
	move=> /(eq0_psum (summable_snd mu12 w)).
	by move=> /(_ v).
rewrite psum_sum; first last.
+ move=> x.
	apply mulr_ge0.
	+ by apply ge0_mu.
	by case: (x == v).
rewrite (@sum_seq1 _ _ _ v).
+ by rewrite eq_refl mulr1.
move=> y.
have [] // := eqVneq y v.
by rewrite mulr0 eq_refl.
Qed.

Lemma proj_glue2 : dsnd mu23 = dsnd (dmargin (fun v => (v.1.1, v.2)) dglue).
Proof.
apply distr_eqP=> v.
rewrite dsndE /= !dmarginE /= !dlet_dlet dletE /=.
rewrite psum_pair; first last.
+ by apply summable_mlet.
under [RHS]eq_psum.
move=> x.
under eq_psum.
move=> y.
rewrite dlet_unit dglueE dunit1E /=.
over.
rewrite psum_sum; first last.
+ move=> w.
	case: (w == v); rewrite ?mulr0 ?mulr1 //.
	case: ifP=> //.
	move=> neq0.
	apply mulr_ge0.
	+ by apply mulr_ge0; apply ge0_mu.
	by rewrite invr_ge0; apply ge0_mu.
rewrite (@sum_seq1 _ _ _ v); first last.
+ move=> y.
	rewrite [y == v]eq_sym.
	case: (v == y)=> //.
	by rewrite mulr0 eq_refl.
rewrite eq_refl mulr1.
rewrite -mulrA.
over.
have -> : psum (fun x => if mu2 x.2 != 0 then mu12 x * (mu23 (x.2, v) / mu2 x.2) else 0)
				=	psum (fun x => mu12 x * ((mu23 (x.2, v) / mu2 x.2) * (mu2 x.2 != 0)%:R)).
+ apply eq_psum=> x.
	by case : ifPn; rewrite ?mulr0 ?mulr1.
rewrite psum_pair_swap; first last.
+ Search summable.
	apply summable_mu_wgtd.
	move=> [x y] /=.
	case H: (mu2 y == 0); rewrite ?mulr0 ?mulr1.
	+ by rewrite le_refl ler01.
	apply /andP.
	split.
	+ apply mulr_ge0; first by apply ge0_mu.
		rewrite invr_ge0.
		by apply ge0_mu.
	rewrite ler_pdivrMr; last first.
	+ by rewrite lt0r ge0_mu H.
	rewrite mul1r -cpl2 dfstE.
Search psum.
	apply (@le_trans _ _ (psum (fun w => mu23 (y, w) * (v == w)%:R))).
	+ rewrite psum_sum.
		+ rewrite (@sum_seq1 _ _ _ v).
			+ by rewrite eq_refl mulr1.
			move=> w.
			by case: (v == w)=> //; rewrite mulr0 eq_refl.
		move=> w.
		apply mulr_ge0; first by apply ge0_mu.
		by case: (v == w).
	by apply /le_psum_condr/summable_fst.
apply eq_psum=> w /=.
have [|neq0] /= := eqVneq (mu2 w) 0.
+ rewrite psum_eq0 //; last by move=> ?; rewrite mulrA mulr0.
	rewrite -cpl2 dfstE.
	move=> /(eq0_psum (summable_fst mu23 w)).
	by move=> /(_ v).
rewrite !psumZr // mulr1; first last.
+ apply mulr_ge0; first by apply ge0_mu.
	rewrite invr_ge0.
	by apply ge0_mu.
by rewrite -dsndE cpl1 [_ / _]mulrC mulrA divff // mul1r.
Qed.

End DGlue.

(* -------------------------------------------------------------------- *)
Section DScalar.
Context {R : realType} {T : choiceType}.

Definition mscalar (k : R) (mu : {distr T / R}) :=
  fun x => k * (mu x).

Lemma isd_mscalar k mu:
  0 <= k <= (dweight mu)^-1 -> isdistr (mscalar k mu).
Proof.
move=> /= /andP [ge0_k le_k_Vmu].
split.
+ by move=> x; rewrite /mscalar /= mulr_ge0.
rewrite /mscalar /=.
move=> J uq_J.
rewrite -mulr_sumr -(pr_mem _ uq_J).
have [-> //=| nz_k] := eqVneq k 0.
+ by rewrite mul0r ler01.
have [| nz_mu] := eqVneq (\P_[mu] predT) 0.
+ move=> /pr_eq0 H.
	suff -> : \P_[mu] [pred x in J] = 0.
	+ by rewrite mulr0 ler01.
	rewrite -(@eq_in_pr _ _ pred0).
	+ by apply pr_pred0.
	move=> x /dinsuppP.
	by rewrite -(H x).
have {ge0_k nz_k} lt0_k : 0 < k.
+ by rewrite lt0r nz_k ge0_k.
rewrite -ler_pdivlMl // mulr1.
move: le_k_Vmu=> /[dup] le_k_Vmu le_mu_Vk.
rewrite invf_pge // in le_mu_Vk; first last.
+ rewrite posrE.
rewrite lt0r ge0_pr.
+ by apply /andP.
apply (@le_trans _ _ (\P_[mu] predT)); last by [].
by apply subset_pr.
Qed.

Variable (k : R) (mu : {distr T / R}).
Hypothesis (bndk: 0 <= k <= (dweight mu)^-1).

Definition dscalar := locked (mkdistr (isd_mscalar bndk)).

Lemma dscalarE x: dscalar x = k * mu x.
Proof.
by unlock dscalar.
Qed.

End DScalar.

Section DScale.

Context {T : choiceType} (mu : {distr T / R}).

Lemma ge0_mu_leweight : 0 <= (dweight mu)^-1 <= (dweight mu)^-1.
Proof.
apply /andP.
split.
+ by rewrite invr_ge0 ge0_pr.
by apply le_refl.
Qed.

Definition dscale := dscalar ge0_mu_leweight. 

End DScale.


Section DCond.

Context {T : choiceType} (P : pred T) (mu : {distr T / R}).

Definition dcond := dscale (drestr P mu).

End DCond.

Lemma eq_pair (T S : eqType) (x : T) (y : S) u v : (x, y) == (u, v) = (x == u) && (y == v).
Proof.
have [] := eqVneq (x, y) (u, v).
+ rewrite pair_equal_spec=> - [] -> ->.
  by rewrite !eq_refl.
move=> /eqP/pair_equal_spec/not_andP.
case.
+ by have [] := eqVneq x u.
have [] // := eqVneq y v.
by rewrite andbF.
Qed.

Section DCondLemma.
Context {T S : choiceType}.

Lemma resampling (d : {distr T / R}) (f : T -> S) :
	\dlet_(x <- d) dunit (x, f x)
	= \dlet_(y <- \dlet_(x <- d) dunit (f x)) \dlet_(x <- dcond (fun v => f v == y) d) dunit (x, y).
Proof.
rewrite dlet_dlet.
apply distr_eqP.
move=> [vx vfx].
rewrite !dletE psum_sum; first last.
+ by move=> x; apply mulr_ge0; apply ge0_mu.
under [RHS]eq_psum=> x.
rewrite dlet_unit dletE.
under eq_psum=> x' do rewrite /GRing.mull_fun dunit1E eq_pair /dcond /dscale dscalarE drestrE.
rewrite psum_sum; first last.
+ move=> x'.
	apply mulr_ge0; last by [].
	apply mulr_ge0; last by case: (f x' == f x).
	by rewrite invr_ge0 ge0_pr.
rewrite (@sum_seq1 _ _ _ vx); last first.
+ move=> x'.
	rewrite [x' == vx]eq_sym.
	case: (vx == x')=> //=.
	by rewrite mulr0 eq_refl.
rewrite eq_refl andTb.
rewrite /pr /= !mulrA.
under eq_psum=> x'.
rewrite mul1r drestrE.
over.
rewrite -mulrA [(d x / _) * _]mulrC !mulrA.
over.
rewrite (@sum_seq1 _ _ _ vx); last first.
+ move=> y. rewrite dunit1E eq_pair [y == vx]eq_sym.
	case: (vx == y)=> //=.
	by rewrite mulr0 eq_refl.
have [-> | /eqP H] := eqVneq (d vx) 0.
+ rewrite mul0r.
	apply /Logic.eq_sym/psum_eq0.
	move=> x.
	by case: ifPn; rewrite !mul0r.
rewrite dunit1E eq_pair eq_refl andTb.
case H1: (f vx == vfx); rewrite (mulr1, mulr0); first last.
apply /Logic.eq_sym/psum_eq0.
move=> x.
move: H1.
have [-> ->|] := eqVneq (f x) vfx.
+ by rewrite !mul0r.
by rewrite mulr0 !mul0r.
move: H1=> /eqP <-.
pose F := fun x => (if f x == f vx then d x else 0) * d vx / psum (fun x' => if f x' == f vx then d x' else 0).
rewrite -(@eq_psum _ _ F).
rewrite /F.
rewrite !psumZr.
rewrite -mulrA [d vx / _]mulrC mulrA divff.
+ by rewrite mul1r.
apply /eqP.
have [| /eqP //] := eqVneq (psum (fun x : T => if f x == f vx then d x else 0)) 0.
have H2 : summable (fun x : T => if f x == f vx then d x else 0).
+ apply (@eq_summable _ _ (fun x => (f x == f vx)%:R * d x)).
	+ move=> x.
		by case: ifPn; rewrite (mul1r, mul0r).
	by apply /summable_condl/summable_mu.
move=> /(eq0_psum H2) /(_ vx).
by rewrite eq_refl.
by apply ge0_mu.
by rewrite invr_ge0 ge0_psum.
move=> x.
rewrite /F.
case: ifPn; last by rewrite mulr0 !mul0r.
move=> /eqP ->.
by rewrite eq_refl mulr1 [d x * _]mulrC.
Qed.

End DCondLemma.

(* -------------------------------------------------------------------- *)
Fixpoint ubn {A : choiceType} (f : A -> Distr A) (t : pred A) n := fun a =>
  if n is n.+1 return Distr A then
    if t a then \dlet_(x <- f a) ubn f t n x else dunit a
  else dnull.

(* -------------------------------------------------------------------- *)
Reserved Notation "m .[ x <- v ]"
  (at level 1, x, v at level 200, format "m .[ x  <-  v ]").

(* -------------------------------------------------------------------- *)
Notation "m .[ x ]"      := (@mget _ _ (vtype x%V) m (vname x%V)) : mem_scope.
Notation "m .[ x <- v ]" := (@mset _ _ (vtype x%V) m (vname x%V) v) : mem_scope.

(* -------------------------------------------------------------------- *)
Section Semantics.
Context {X : eqType} {cmem: memType X}.

Notation vars    := (@vars_ X).
Notation expr    := (@expr_ X cmem).
Notation cmd     := (@cmd_  X cmem).
Notation bexpr   := (expr bool).
Notation dexpr T := (expr (Distr T)).

Notation mdistr := (Distr cmem.(mheap)).
Notation mnull  := (@dnull R cmem.(mheap)).

(* -------------------------------------------------------------------- *)
Fixpoint esem {T : Type} (e : expr T) (m : cmem) : T :=
  match e in expr_ _ _ T return T with
  | var_ T x => m.[x]
  | cst_ T c => c
  | prp_ P   => P m
  | app_ T U e1 e2 => (esem e1 m) (esem e2 m)
  end.

(* -------------------------------------------------------------------- *)
Fixpoint ssem_aux (s : cmd) (m : cmem) : mdistr :=
  match s with
  | abort => mnull
  | skip  => dunit m

  | x <<- e =>
      dunit (m.[x <- esem e m])

  | x <$- e =>
      \dlet_(v <- esem e m) (dunit m.[x <- v])

  | If e then c1 else c2 =>
      match esem e m with
      | true  => ssem_aux c1 m
      | false => ssem_aux c2 m
      end

  | While e Do c =>
      dlim (fun n => ubn (ssem_aux c) (esem e) n m)

  | seqc c1 c2 =>
     \dlet_(m' <- ssem_aux c1 m) (ssem_aux c2 m')
  end.

Definition ssem_r s m := ssem_aux s m.

(* -------------------------------------------------------------------- *)
Fact ssem_key : unit. Proof. by []. Qed.
Definition ssem_ := locked_with ssem_key ssem_r.
Canonical ssem_unlockable := [unlockable fun ssem_].

(* -------------------------------------------------------------------- *)
Implicit Types (m : cmem) (c : cmd).

Notation ssem := ssem_.
Notation prp  := prp_.

Lemma sem_eqP c1 c2 :
  (forall m, ssem c1 m = ssem c2 m) <-> ssem c1 = ssem c2.
Proof. by split=> [|->//] eq; apply/funext=> m. Qed.

Fixpoint whilen e c n :=
  if n is n.+1 then
    (If e then (c;; whilen e c n) else skip)
  else abort.

Lemma ssem_abortE m : ssem abort m = mnull.
Proof. by rewrite unlock. Qed.

Lemma ssem_skipE m : ssem skip m = dunit m.
Proof. by rewrite unlock. Qed.

Lemma ssem_assnE {T} (x : vars T) (e : expr T) m :
  ssem (x <<- e) m = dunit (m.[x <- esem e m]).
Proof. by rewrite unlock. Qed.

Lemma ssem_rndE {T} (x : vars T) (e : dexpr T) m :
  ssem (x <$- e) m = \dlet_(v <- esem e m) (dunit m.[x <- v]).
Proof. by rewrite unlock. Qed.

Lemma ssem_ifE e c1 c2 m :
  ssem (If e then c1 else c2) m =
    if esem e m then ssem c1 m else ssem c2 m.
Proof. by rewrite unlock. Qed.

Lemma ssem_seqE c1 c2 m :
  ssem (c1 ;; c2) m = \dlet_(m' <- ssem c1 m) (ssem c2 m').
Proof. by rewrite unlock. Qed.

Lemma esem_varE {T : IhbType.type} (x : vars T) m : 
   esem (@var_ _ _ T x) m = m.[x].
Proof. by []. Qed.

Lemma esem_cstE {T : Type} (c : T) m : esem (cst_ c) m = c.
Proof. by []. Qed.

Lemma esem_prpE (P : pred cmem) m : esem (prp_ P) m = P m.
Proof. by []. Qed.

Lemma esem_appE {T U : Type} (e1 : expr (T -> U)) (e2 : expr T) m :
  esem (app_ e1 e2) m = (esem e1 m) (esem e2 m).
Proof. by []. Qed.

Lemma ssem_whileE e c m :
  ssem (While e Do c) m = dlim (fun n => ssem (whilen e c n) m).
Proof.
rewrite {1}unlock /=; apply/eq_dlim=> n /=.
elim: n m => /= [|n ih] m; first by rewrite ssem_abortE.
rewrite ssem_ifE; case: (esem e m); last by rewrite ssem_skipE.
rewrite ssem_seqE /=;apply/eq_in_dlet => //.
by rewrite unlock.
Qed.

Lemma ssem_while_ubn e c m :
  ssem (While e Do c) m = dlim (fun n => ubn (ssem c) (esem e) n m).
Proof. by rewrite unlock. Qed.

Definition semE :=
  (ssem_abortE, ssem_skipE, @ssem_assnE, @ssem_rndE,
   ssem_ifE   , ssem_seqE , ssem_whileE).

Definition bsemE := locked (
  funext ssem_abortE,
  funext ssem_skipE,
  fun T (x : vars T) (e : expr _) => funext (ssem_assnE x e),
  fun T (x : vars T) (e : expr _) => funext (ssem_rndE x e),
  fun e c1 c2 => funext (ssem_ifE e c1 c2),
  fun c1 c2 => funext (ssem_seqE c1 c2),
  fun e c => funext (ssem_whileE e c)).

Lemma sem_seqA c1 c2 c3 :
  ssem ((c1 ;; c2) ;; c3) = ssem (c1 ;; (c2 ;; c3)).
Proof. by apply/sem_eqP=> m; rewrite !bsemE dlet_dlet. Qed.

Lemma sem_ifseq e ct cf c :
    ssem ((If e then ct else cf) ;; c)
  = ssem (If e then (ct ;; c) else (cf ;; c)).
Proof. by apply/sem_eqP=> m; rewrite !bsemE; case: ifP. Qed.

Lemma sem_seql c1 c1' c2 :
  ssem c1 =1 ssem c1' -> ssem (c1 ;; c2) = ssem (c1' ;; c2).
Proof. by move/sem_eqP=> eq; rewrite !bsemE eq. Qed.

Lemma sem_seqr c1 c2 c2' :
  ssem c2 =1 ssem c2' -> ssem (c1 ;; c2) = ssem (c1 ;; c2').
Proof. by move/sem_eqP=> eq; rewrite !bsemE eq. Qed.

Lemma sem_ift e ct ct' cf : ssem ct =1 ssem ct' ->
  ssem (If e then ct else cf) = ssem (If e then ct' else cf).
Proof. by move=> /sem_eqP eq; rewrite !bsemE eq. Qed.

Lemma sem_iff e ct cf cf' : ssem cf =1 ssem cf' ->
  ssem (If e then ct else cf) = ssem (If e then ct else cf').
Proof. by move=> /sem_eqP eq; rewrite !bsemE eq. Qed.

Lemma sem_whileb e c c' :
  ssem c =1 ssem c' -> ssem (While e Do c) = ssem (While e Do c').
Proof.
 move=> /sem_eqP eq;apply/sem_eqP=> m;rewrite !semE.
 apply/eq_dlim=> /= n; elim: n m => //= n /sem_eqP ih m.
 by rewrite !bsemE ih eq .
Qed.

(* -------------------------------------------------------------------- *)
Lemma dlim_seql (C : nat -> cmd) (c : cmd) m :
     (forall m n p, (n <= p)%N -> ssem (C n) m <=1 ssem (C p) m)
  -> \dlim_(n) (ssem (C n ;; c) m)
   = \dlet_(m' <- \dlim_(n) ssem (C n) m) ssem c m'.
Proof.
move=> leC; rewrite dlet_lim; last by apply/leC.
by apply/eq_dlim=> n; rewrite semE.
Qed.

Lemma dlim_seqr (C : nat -> cmd) (c : cmd) m :
     (forall m n p, (n <= p)%N -> ssem (C n) m <=1 ssem (C p) m)
  -> \dlim_(n) (ssem (c ;; C n) m)
   = \dlet_(m' <- ssem c m) \dlim_(n) (ssem (C n) m').
Proof.
move=> leC; rewrite -dlim_let //.
by apply/eq_dlim => n; rewrite semE.
Qed.

Lemma dlim_ift (e : expr bool) (C : nat -> cmd) (c : cmd) m :
    \dlim_(n) (ssem (If e then C n else c) m)
  = if esem e m then \dlim_(n) ssem (C n) m else ssem c m.
Proof.
pose F n := if esem e m then ssem (C n) m else ssem c m.
rewrite -(@eq_dlim _ F) {}/F => [|k]; last by rewrite !semE.
by case: ifPn => _; rewrite ?dlimC.
Qed.

Lemma dlim_iff (e : expr bool) (C : nat -> cmd) (c : cmd) m :
    \dlim_(n) (ssem (If e then c else C n) m)
  = if esem e m then ssem c m else \dlim_(n) ssem (C n) m.
Proof.
pose F n := if esem e m then ssem c m else ssem (C n) m.
rewrite -(@eq_dlim _ F) {}/F => [|k]; last by rewrite !semE.
by case: ifPn => _; rewrite ?dlimC.
Qed.

(* -------------------------------------------------------------------- *)
Definition iterc n (c : cmd) :=
  nosimpl (iterop n seqc c skip).

Arguments iterc : simpl never.

Lemma iterc0 c : iterc 0 c = skip.
Proof. by []. Qed.

Lemma itercS n c : iterc n.+1 c = iter n (seqc c) c.
Proof. by rewrite /iterc iteropS. Qed.

(* -------------------------------------------------------------------- *)
Lemma homo_ssem (mu1 mu2 : Distr cmem) c :
  mu1 <=1 mu2 -> \dlet_(m <- mu1) ssem c m <=1 \dlet_(m <- mu2) ssem c m.
Proof. by move=> le_mu m; apply/le_dlet. Qed.

Lemma sem_seq_le c1 c2 c1' c2' :
     ssem c1 <=2 ssem c1'
  -> ssem c2 <=2 ssem c2'
  -> ssem (c1 ;; c2) <=2 ssem (c1' ;; c2').
Proof. by move=> le1 le2 m1 m2; rewrite !semE; apply/le_dlet. Qed.

Lemma le_whilen (n : nat) (e : expr bool) (c : cmd) m m' :
  ssem (whilen e c n) m m' <= ssem (whilen e c n.+1) m m'.
Proof.
elim: n m m' => /= [|n ih] m m'.
  by rewrite ssem_abortE dnullE ge0_mu.
rewrite !ssem_ifE; case: (esem e m) => //.
rewrite !ssem_seqE; apply/le_in_dlet.
by move=> {m'} m _ m'; apply/ih.
Qed.

Lemma homo_whilen e c m n p : (n <= p)%N ->
  ssem (whilen e c n) m <=1 ssem (whilen e c p) m.
Proof.
elim: p n => [|p ih] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le_np m'.
by apply/(le_trans (ih _ le_np m'))/le_whilen.
Qed.

Lemma dcvg_whilen e c m : dcvg (fun n => ssem (whilen e c n) m).
Proof.
move=> m'; set u := fun n : nat => _; case: (@ncvg_mono_bnd _ u).
+ by move=> n p le_np; apply/homo_whilen.
+ apply/asboolP/nboundedP; exists 2%:R => // n.
  apply/(@le_lt_trans _ _ 1%:R); rewrite ?ltr1n //.
  by rewrite ger0_norm (ge0_mu, le1_mu1).
by move=> l ul; exists l%:E.
Qed.

Lemma unroll_while_w (e e' : expr bool) c m :
     (forall m, esem e' m -> esem e m)
  -> ssem (While e Do c) m =
     ssem (IfT e' then c ;; While e Do c) m.
Proof.
move=> impe; apply/distr_eqP=> m'; rewrite !semE.
case: ifPn => h; last by rewrite dlet_unit -semE.
rewrite -dlim_bump /= -ssem_seqE dlim_ift.
rewrite dlim_seqr; last by apply/homo_whilen.
rewrite impe // semE; apply/distr_eqP: m'.
by apply/eq_in_dlet=> // m' _; rewrite semE.
Qed.

Lemma unroll_while (e : expr bool) c m :
  ssem (While e Do c) m =
  ssem (IfT e then c ;; While e Do c) m.
Proof. by apply/unroll_while_w. Qed.

Lemma unroll_while_in (e : expr bool) c m :
  ssem (While e Do c) m =
  ssem (IfT e then (c ;; While e Do c)) m.
Proof.
rewrite unroll_while !semE; case: ifP => // h.
rewrite dlet_unit semE; apply/distr_eqP=> m'.
by rewrite -dlim_bump /= dlim_ift h semE.
Qed.

Lemma ssem_while0 (e : expr bool) c m : ~~ esem e m ->
  ssem (While e Do c) m = dunit m.
Proof. by rewrite unroll_while_in !semE => /negbTE ->. Qed.

Lemma ssem_whileS (e : expr bool) c m : esem e m ->
  ssem (While e Do c) m = ssem (c ;; While e Do c) m.
Proof. by rewrite unroll_while_in !semE => ->. Qed.

Lemma unrolls_while_w (e e' : expr bool) c m :
     (forall m, esem e' m -> esem e m)
  -> ssem (While e Do c) m =
     ssem (While e' Do c;; While e Do c) m.
Proof.
move=> impe; apply/distr_eqP=> m'; apply/eqP.
rewrite eq_le andbC; apply/andP; split.
  rewrite ssem_seqE (ssem_whileE e') dlet_lim; last first.
    apply/homo_whilen.
  apply/leub_dlim => n {}m'; rewrite -ssem_seqE.
  elim: n m m' => [|n ihn] m m' /=.
    by rewrite !semE dlet_null; apply/lef_dnull.
  rewrite sem_ifseq ssem_ifE; case: ifPn => [/impe em|].
    by rewrite ssem_whileS // sem_seqA; apply/sem_seq_le.
  by rewrite 2!semE dlet_unit.
rewrite ssem_whileE; apply/leub_dlim; move: {m'} m => [:a] m n m'.
case/asboolP: (esem e' m) => [|/negP]; last first.
  abstract: a n m m' => h; rewrite ssem_seqE (@ssem_while0 e') //.
  rewrite dlet_unit semE; apply/dlim_ub=> {m'} k p le_kp m'.
  by apply/homo_whilen.
elim: n m m' => [|n ihn] m m' h.
  by rewrite ssem_abortE; apply/lef_dnull.
rewrite ssem_ifE impe // !ssem_seqE ssem_whileS //.
rewrite ssem_seqE dlet_dlet; apply/le_in_dlet=> {h m'} m _ m'.
rewrite -ssem_seqE; case/asboolP: (esem e' m) => [|/negP h].
  by move/ihn. by apply/a.
Qed.

Lemma split_while (e1 e2 : expr bool) c:
     ssem (While e1 Do c)
   = ssem (While (e1 && e2) Do c ;; While e1 Do c).
Proof. by apply/funext=> m; apply/unrolls_while_w => {}m /= /andP[]. Qed.

Lemma prpP (P : pred cmem) m : reflect (P m) (esem (prp_ P) m).
Proof. by apply/idP. Qed.
End Semantics.

(* -------------------------------------------------------------------- *)
Section EqCmd.
Context {I : eqType} {M : memType I}.

Local Notation cmd := (cmd_ I M).

Definition eqcmd (c1 c2 : cmd) := 
  forall m, ssem_ c1 m = ssem_ c2 m.

Global Instance eqcmd_R : Equivalence eqcmd.
Proof. 
constructor=> //.
+ by move=> f1 f2 eq s; rewrite eq.
+ by move=> f1 f2 f3 eq1 eq2 s; rewrite eq1.
Qed.

Notation "c1 '=C' c2" := (eqcmd c1 c2) (at level 70, no associativity).

Notation CLHS := (X in X =C _)%pattern.
Notation CRHS := (X in _ =C X)%pattern.

Lemma seq_abort_r (c : cmd): (c ;; abort) =C abort.
Proof.
move=> m.
rewrite !semE.
apply distr_eqP=> v.
under eq_in_dlet=> [? _|] do [rewrite ssem_abortE|].
by rewrite dletC dnullE mulr0.
Qed.

Lemma seq_abort_l (c : cmd): (abort ;; c) =C abort.
Proof. by move=> m; rewrite !semE dlet_null. Qed.

Lemma seq_skip_l (c : cmd) : (skip ;; c) =C c.
Proof. by move=> m;rewrite !semE dlet_unit. Qed.

Lemma seq_skip_r (c : cmd) : (c ;; skip) =C c.
Proof.
move=> m; rewrite semE -[X in _ = X]dlet_dunit_id;
by apply eq_in_dlet => // ??; rewrite semE.
Qed.

Lemma seqA (c1 c2 c3 : cmd) : (c1 ;; (c2 ;; c3)) =C (c1 ;; c2 ;; c3).
Proof.
move=> m;rewrite !semE dlet_dlet.
by apply eq_in_dlet=> // m' _;rewrite semE.
Qed.

Lemma iter_seq_out n c c1 c2 :
  iter n (seqc c) (c1 ;; c2) =C (iter n (seqc c) c1 ;; c2).
Proof.
by elim: n => //= n ih m; rewrite -seqA !ssem_seqE; apply/eq_in_dlet.
Qed.

Lemma iter_seq_swap n c : iter n (seqc^~ c) c =C iter n (seqc c) c.
Proof.
elim: n => // n ih m; rewrite [in RHS]iterSr.
by rewrite iter_seq_out !ssem_seqE; apply/eq_in_dlet.
Qed.

Lemma itercSl n c: iterc n.+1 c =C (c ;; iterc n c).
Proof. by move=> m; case: n => [|n] //=; rewrite seq_skip_r. Qed.

Lemma itercSr n c: iterc n.+1 c =C (iterc n c ;; c).
Proof.
move=> m; case: n => [|n]; first by rewrite iterc0 seq_skip_l.
rewrite !itercS /= -iterS -iter_seq_swap /=.
by rewrite !ssem_seqE; apply/eq_in_dlet=> //; apply/iter_seq_swap.
Qed.

Global Instance seq_m : Proper (eqcmd ==> eqcmd ==> eqcmd) seqc.
Proof. by move=> ?? H1 ?? H2 m;rewrite !semE; apply eq_in_dlet. Qed.

Global Instance while_m : Proper (eq ==> eqcmd ==> eqcmd) while.
Proof. 
move=> ?? H1 ?? H2 m; rewrite !ssem_while_ubn H1; apply/eq_dlim=> n.
by elim: n m => //= n ih m; case: ifP => // _; apply eq_in_dlet.
Qed.

Global Instance cond_m : Proper (eq ==> eqcmd ==> eqcmd ==> eqcmd) cond.
Proof. by move=> ?? H1 ?? H2 ?? H3 m; rewrite !semE H1; case: ifP. Qed. 

Fixpoint mk_seqr (c1 c2 : cmd) := 
  match c2 with
  | skip        => c1
  | seqc c2 c2' => mk_seqr (mk_seqr c1 c2) c2'
  | _           => seqc c1 c2
  end.

Definition mk_seq (c1 c2 : cmd) := 
  if c1 is skip then c2 else  mk_seqr c1 c2.
 
Fixpoint normc (c : cmd) :=
  match c with
  | abort | skip | assign _ _ _ | random _ _ _ => c
  | cond e c1 c2 => cond e (normc c1) (normc c2)
  | while e c    => while e (normc c)
  | seqc c1 c2   => mk_seq (normc c1) (normc c2)
  end.

Lemma mk_seqrP (c1 c2 : cmd) : mk_seqr c1 c2 =C seqc c1 c2.
Proof. 
elim:c2 c1=> //= [|c2 H1 c3 H2] c1;first by rewrite seq_skip_r.
by rewrite seqA H2 H1.
Qed.

Lemma mk_seqP (c1 c2 : cmd) : mk_seq c1 c2 =C seqc c1 c2.
Proof. by case:c1 => //= *;rewrite ?mk_seqrP // seq_skip_l. Qed.

Lemma normcP (c : cmd) : c =C normc c.
Proof.
by elim: c=> //= [?? H1 ? H2|?? H1|? H1 ? H2];
rewrite ?mk_seqP [in CLHS]H1 ?[in CLHS]H2. 
Qed.

(* -------------------------------------------------------------------- *)
Lemma ssem_iterop_iter n c :
  iterc n c =C iter n (seqc c) skip.
Proof.
case: n => // n; rewrite itercS /=; elim: n => [|n ih] /=.
  by rewrite seq_skip_r. by rewrite ih.
Qed.

Lemma ssem_iterop_iterrev n c :
  iterc n c =C iter n (seqc^~ c) skip.
Proof.
rewrite ssem_iterop_iter; elim: n=> // n ih.
rewrite iterSr iterS -{}ih; elim: n => /= [|n ih].
- by rewrite seq_skip_l seq_skip_r.
- by rewrite ih seqA.
Qed.

Lemma whilen_iterc n b c :
  whilen b c n.+1 =C (iterc n (IfT b then c) ;; (IfT b then abort)).
Proof.
rewrite ssem_iterop_iter; elim: n => [|n ihn] /=.
  rewrite seq_skip_l => m; rewrite !semE; case: ifP=> // _.
  by rewrite bsemE; apply/distr_eqP=> m'; rewrite dletC dnullE mulr0.
rewrite -seqA -ihn /= => m; rewrite !semE; case: ifP => // bm.
by rewrite dlet_unit !semE bm.
Qed.

End EqCmd.

Notation "c1 '=C' c2" := (eqcmd c1 c2) (at level 70, no associativity).

(* -------------------------------------------------------------------- *)
Lemma unrolln_while n (e : expr bool) c :
  (While e Do c) =C (iterc n (IfT e then c) ;; While e Do c).
Proof.
rewrite ssem_iterop_iter; elim: n => [|n ih] /=.
  by rewrite seq_skip_l.
by rewrite -seqA -ih => m; rewrite unroll_while.
Qed.

(* -------------------------------------------------------------------- *)
Lemma if_same (e : expr bool) c : If e then c else c =C c.
Proof. by move=> m; rewrite !semE; case: (esem _ _). Qed.

(* -------------------------------------------------------------------- *)
Lemma if_seq (e : expr bool) c c1 c2 :
  (If e then c1 else c2 ;; c) =C If e then (c1 ;; c) else (c2 ;; c).
Proof. by move=> m; rewrite !semE; case: ifPn. Qed.

(* -------------------------------------------------------------------- *)
Lemma le_while (e : expr bool) c1 c2 m :
     (forall m, esem e m -> ssem_ c1 m <=1 ssem_ c2 m)
  -> ssem_ (While e Do c1) m <=1 ssem_ (While e Do c2) m.
Proof.
move=> lec m'; rewrite !semE; apply/le_dlim/dcvg_whilen => n.
elim: n m => //= n ihn m {}m'; rewrite !semE.
by case: ifP => // hem; apply/le_dlet => {} m' //; apply: lec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xsplit_while (e e1 e2 : expr bool) c:
     (forall m, esem e2 m -> esem e m)
  -> (forall m, esem e m -> ~~ esem e1 m -> esem e2 m)
  -> (While e Do c) =C (While e Do (If e1 then c else While e2 Do c)).
Proof.
move=> h1 h2 m; apply/distr_eqP => m'.
rewrite (rwP eqP) eq_le -(rwP andP); split; last first.
  rewrite semE; apply: leub_dlim => {m'} n m'.
  elim: n m m' => /= [|n ihn] m m'; first by rewrite !semE lef_dnull.
  rewrite semE; case: ifP => hem; last first.
    by rewrite unroll_while_in ssem_ifE hem.
  rewrite if_seq ssem_ifE; case: ifPn => he1m.
    by rewrite unroll_while_in ssem_ifE hem !ssem_seqE le_dlet.
  by rewrite (unrolls_while_w _ _ h1) !ssem_seqE le_dlet.
rewrite ssem_whileE; apply: leub_dlim => {m'} n m'.
elim: n m m' => /= [|n ihn] m m'; first by rewrite !semE lef_dnull.
rewrite semE; case: ifP => hem; last first.
  by rewrite unroll_while_in ssem_ifE hem.
rewrite unroll_while_in ssem_ifE hem 2![in X in _ <= X]semE.
case: ifPn => he1m; first by rewrite !ssem_seqE le_dlet.
rewrite unroll_while -!ssem_seqE -seqA 2![in X in _ <= X]semE.
rewrite (h2 _ hem he1m) ssem_seqE le_dlet => // {m' hem he1m} m _ m'.
rewrite 2!semE dlet_lim; last by apply: homo_whilen.
apply: (le_trans _ (dlim_ub n _ _)); last first.
  move=> k1 k2 le_k1k2 {}m'; apply: le_dlet => //.
  by move=> {}m'; apply: homo_whilen.
elim: n m m' ihn => /= [|k ihk] m m' ihn; first by rewrite semE lef_dnull.
rewrite !ssem_ifE; case: ifP => hem; last first.
  case: ifPn => [/h1|he2m]; first by rewrite hem.
  by rewrite -ssem_seqE seq_skip_l unroll_while_in ssem_ifE hem.
case: ifPn => he2m; rewrite -!ssem_seqE.
  rewrite -seqA 2!ssem_seqE le_dlet => // {m' hem he2m} m _ m'.
  rewrite ssem_seqE; apply: ihk => {m'} m m'.
  by apply: (le_trans (le_whilen _ _ _ _ _)) => /=.
rewrite seq_skip_l unroll_while_in ssem_ifE hem.
rewrite 2![in X in _ <= X]semE; case: ifPn => [he1m|]; last first.
  by move/(h2 _ hem); rewrite (negbTE he2m).
rewrite ssem_seqE le_dlet => // {m' hem he1m he2m} m _ m'.
by apply: (le_trans (le_whilen _ _ _ _ _)).
Qed.

(* -------------------------------------------------------------------- *)
Notation ssem   := (@ssem_ _ cmem).
Notation mdistr := (Distr cmem).
Notation mnull  := (@dnull R cmem.(mheap)).

Arguments ssem_ X cmem s%_S m%_M.
Arguments esem X cmem T e%_X m%_M.

Notation "e `_ m" := (@esem _ _ _ e%X m%M) : sem_scope.

(* -------------------------------------------------------------------- *)
Definition dssem c mu := (\dlet_(m <- mu) ssem c m).

Instance dsem_m : Proper (@eqcmd _ _ ==> eq ==> eq) dssem.
Proof. by move=> c1 c2 eqc /= mu _ <-; apply/eq_in_dlet. Qed.

(* -------------------------------------------------------------------- *)
Lemma dssem_abortE mu : dssem abort mu = mnull.
Proof.
by apply/distr_eqP=> m; rewrite /dssem bsemE dletC dnullE mulr0.
Qed.

Lemma dssem_skipE mu : dssem skip mu = mu.
Proof.
by apply/distr_eqP=> m; rewrite /dssem bsemE dlet_dunit_id.
Qed.

Lemma dssem_seqE c1 c2 mu :
  dssem (c1 ;; c2) mu = dssem c2 (dssem c1 mu).
Proof.
by apply/distr_eqP=> m; rewrite /dssem bsemE dlet_dlet.
Qed.

(* -------------------------------------------------------------------- *)
Definition lossless (P : assn) c :=
  forall m, m \in P -> dweight (ssem c m) = 1.

Definition dlossless (P : dassn) c :=
  forall mu, mu \in P -> dweight (dssem c mu) = 1.

(* -------------------------------------------------------------------- *)
Reserved Notation "m .[ x @ s <- v ]"
  (at level 1, x, s, v at level 200, format "m .[ x @ s  <-  v ]").

Reserved Notation "m .[~1 x <- v ]"
  (at level 1, x, v at level 200, format "m .[~1  x  <-  v ]").

Reserved Notation "m .[~2 x <- v ]"
  (at level 1, x, v at level 200, format "m .[~2  x  <-  v ]").

Notation rsem    := (@ssem_ _ rmem).
Notation rmdistr := (Distr rmem.(mheap)).
Notation rmnull  := (@dnull R rmem.(mheap)).

Notation "m .[ x @ s <- v ]" := m.[x # s <- v].
Notation "m .[~1 x <- v ]"   := m.[x @ '1 <- v].
Notation "m .[~2 x <- v ]"   := m.[x @ '2 <- v].

Lemma mselect_mset T s s' (m : rmem) (x : vars T) (v : T) :
  m.[x @ s <- v] # s' = if s == s' then (m#s).[x <- v] else m#s'.
Proof. by case: s s' x => [] [] []. Qed.

Lemma esem_iE T s (e : expr T) (m : rmem) : esem (e#s) m = esem e m#s.
Proof. by elim: e => {T} /= [ ?[?]| | | ??? -> ? ->]. Qed.

Lemma esem_1E T (e : expr T) (m : rmem): esem (e#'1) m = esem e m.1.
Proof. by rewrite esem_iE. Qed.

Lemma esem_2E T (e : expr T) (m : rmem): esem (e#'2) m = esem e m.2.
Proof.  by rewrite esem_iE. Qed.

Definition esemE := (@esem_appE, @esem_cstE, esem_1E, esem_2E).

Definition ssemE := (esemE, @semE).

Lemma mget_iE {T : IhbType.type} (m : rmem) (x : vars T) s :
  m.[irvar s x] = (m#s).[x].
Proof. by case:s x=> -[]. Qed.

Lemma mset_iE {T : IhbType.type} (m : rmem) (x : vars T) (v : T) s :
  m.[x#s <- v] = 
  (((m#'1).[x <- v], m.1)#s, (m.2, (m#'2).[x <- v])#s)%M.
Proof. by case:x m s => xid [m1 m2] []. Qed.

Lemma ssem_iE s c (m : rmem): rsem (ircmd s c) m = 
  \dlet_(m' <- ssem c m#s) dunit ((m', m.1)#s, (m.2, m')#s)%M.
Proof.
elim: c m => [||T v e|T v e|e c1 Hc1 c2 Hc2|e c Hc|c1 Hc1 c2 Hc2] [m1 m2].
+ by rewrite !ssemE dlet_null.
+ by rewrite !ssemE dlet_unit; case:s.
+ by rewrite !ssemE esem_iE dlet_unit mset_iE;case:s.
+ rewrite !ssemE esem_iE dlet_dlet; apply eq_in_dlet => // t _.
  by rewrite dlet_unit mset_iE;case: s.
+ by rewrite !ssemE esem_iE;case:ifP.
+ rewrite !ssemE dlet_lim; last by apply/homo_whilen.
  apply eq_dlim=> n; elim: n (m1,m2)=> [ | n Hn] m /=.
  + by rewrite !ssemE dlet_null.
  rewrite !ssemE esem_iE;case:ifP => _.
  + rewrite Hc !dlet_dlet;apply eq_in_dlet=>// m' _.
    by rewrite dlet_unit Hn;case s.
  by rewrite dlet_unit;case: m s {Hc Hn}=> ?? [].
rewrite !ssemE Hc1 !dlet_dlet;apply eq_in_dlet=>// m _.
by rewrite !dlet_unit Hc2;apply eq_in_dlet =>[? _|];case s.
Qed.

Lemma ssem_1E (m : rmem) c :
  rsem (c#'1) m = \dlet_(m1 <- ssem c m.1) (dunit (m1, m.2)).
Proof. by apply ssem_iE. Qed.

Lemma ssem_2E (m : rmem) c :
  rsem (c#'2) m = \dlet_(m2 <- ssem c m.2) (dunit (m.1, m2)).
Proof. by apply ssem_iE. Qed.

(* -------------------------------------------------------------------- *)
Notation "`[{ e }]" := (@esem _ _ _ e%X) (at level 2, format "`[{ e }]").

(* -------------------------------------------------------------------- *)
Ltac diff_v := try (right; (assumption || rewrite eq_sym; assumption)).

Notation SET := ((_.[_ <- _].[_])%pattern) (only parsing).

Ltac mem_t := rewrite ?mget_iE ![SET](mget_eq, mget_neq); diff_v.
