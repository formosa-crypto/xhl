(* -------------------------------------------------------------------- *)
From Stdlib.Logic Require Import FunctionalExtensionality.
From Stdlib             Require Import Setoid Morphisms.
From mathcomp           Require Import all_boot all_order all_algebra.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import contra boolp classical_sets.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope sem_scope.
Local Open Scope mem_scope.

(* -------------------------------------------------------------------- *)
Section TOMOVE.

Lemma mem_ext (m1 m2 : cmem): (forall T (x : vars T), m1.[x] = m2.[x]) -> m1 = m2.
Proof.
move: m1 m2.
unlock cmem.
move=> [m1] [m2] H.
congr (CoreMem).
extensionality T.
extensionality x.
by move: (H T (Var T x)).
Qed.

Lemma vars_neq {T : IhbType.type} (x : vars T) (y : vars T):
	x != y
	-> vname x != vname y.
Proof.
move: x y.
unlock vars=> - [x] [y].
have [->|] //= := eqVneq x y.
by rewrite eq_refl.
Qed.

End TOMOVE.

(* -------------------------------------------------------------------- *)
Section Disjoint.

Context {T : Type}.
Implicit Types A B C D : set T.

Lemma disjointUr A B C:
	[disjoint A & B `|` C]
	<-> [disjoint A & B] /\ [disjoint A & C].
Proof.
by rewrite -!(rwP disj_set2P) setIUr setU_eq0.
Qed.

Lemma disjointUl A B C:
	[disjoint A `|` B &  C]
	<-> [disjoint A & C] /\ [disjoint B & C].
Proof.
by rewrite disj_set_sym disjointUr disj_set_sym [disj_set C B]disj_set_sym.
Qed.

Lemma disjoint1 x A:
	[disjoint [set x] & A]
	<-> x \notin A.
Proof.
rewrite -(rwP disj_set2P) set1I.
case: ifPn=> _ //=.
split; last by [].
rewrite -(in_set0 x)=> <-.
by rewrite mem_set.
Qed.

End Disjoint.


(* -------------------------------------------------------------------- *)
Section PreCouplings.
Context {A B : choiceType} (v1 : Distr A) (v2 : Distr B)
  (f1: A -> Distr A) (f2: B -> Distr B).

Definition isprecoupling (ν : Distr (A * B)) :=
  \dlet_(m' <- dfst ν) (f1 m') = v1
  /\ \dlet_(m' <- dsnd ν) (f2 m') = v2.

End PreCouplings.

Section PreCouplingsTheory.

Lemma isprecoupling_eq {A B : choiceType} (u1 u2 u1' u2' : Distr _) (ν : Distr (A * B)) (f1 f2 : _ -> Distr _) :
  u1 =1 u1' -> u2 =1 u2' -> isprecoupling u1 u2 f1 f2 ν -> isprecoupling u1' u2' f1 f2 ν.
Proof. by do 2! move=> /distr_eqP->. Qed.

Lemma isprecoupling_dnull {A B : choiceType} (f1 f2 : _ -> Distr _):
	@isprecoupling A B dnull dnull f1 f2 dnull.
Proof.
by split; rewrite dmarginE !dlet_null.
Qed.

Lemma isprecoupling_dunit {A B : choiceType} (f1 f2 : _ -> Distr _) m':
@isprecoupling A B (f1 m'.1) (f2 m'.2) f1 f2 (dunit m').
Proof.
by split; rewrite dmarginE !dlet_unit.
Qed.

Lemma isprecoupling_swap {A : choiceType} (u1 u2 : Distr A) (ν : Distr (A * A)) (f1 f2 : _ -> Distr _):
  isprecoupling u1 u2 f1 f2 ν -> isprecoupling u2 u1 f2 f1 (dswap ν).
Proof.
case=> <- <-; split.
+ apply eq_in_dlet=> //.
  apply distr_eqP=> m.
	by rewrite dfst_dswap.
apply eq_in_dlet=> //.
apply distr_eqP=> m.
by rewrite dsnd_dswap.
Qed.

Lemma isprecoupling_dlet {A B C D: choiceType}
  (u1 u2 : Distr _) (f1 f2 : _ -> Distr _) (u: Distr (A * B))
  (v1 v2 : _ -> Distr _) (g1 g2 : _ -> Distr _) (v: _ -> Distr (C * D)) :
  isprecoupling u1 u2 f1 f2 u
  -> (forall x, x \in dinsupp u ->
    isprecoupling (\dlet_(y <- f1 x.1) (v1 y)) (\dlet_(y <- f2 x.2) (v2 y)) g1 g2 (v x))
    -> isprecoupling
      (\dlet_(x <- u1) (v1 x))
      (\dlet_(x <- u2) (v2 x))
      g1 g2
      (\dlet_(x <- u) (v x)).
Proof.
move=> [eq1 eq2] hC.
subst u1 u2.
split.
+ rewrite dlet_dmargin !dlet_dlet.
  apply: eq_in_dlet => // y /hC [+ _].
  by rewrite dlet_dmargin dlet_unit.
rewrite dlet_dmargin !dlet_dlet.
apply: eq_in_dlet => // y /hC [_ +].
by rewrite dlet_dmargin dlet_unit.
Qed.

Lemma isprecoupling_dlim {A B: choiceType}
  (μ1 μ2 : nat -> Distr _) (f1 f2 : _ -> Distr _) (ν : nat -> Distr (A * B)) :

     (forall n, isprecoupling (μ1 n) (μ2 n) f1 f2 (ν n))
  -> (forall n m, (n <= m)%N -> ν n <=1 ν m)
  -> isprecoupling (dlim μ1) (dlim μ2) f1 f2 (dlim ν).
Proof.
move=> hC mono.
rewrite /isprecoupling !dmarginE !dlet_lim //.
+ move=> n m /mono H x.
  rewrite -!dmarginE.
  rewrite !dfstE.
  apply le_psum; last by apply summable_fst.
  move=> w.
  move: (H (x, w))=> ->.
  by rewrite ge0_mu.
+ move=> n m /mono H x.
  rewrite -!dmarginE.
  rewrite !dsndE.
  apply le_psum; last by apply summable_snd.
  move=> w.
  move: (H (w, x))=> ->.
  by rewrite ge0_mu.
by split; apply/eq_dlim => n; case: (hC n); rewrite -dmarginE.
Qed.

End PreCouplingsTheory.

Section Variables.

Context {ident : eqType} {mem : memType ident}.
Local Notation vars := (vars_ ident).
Local Notation expr := (expr_ _ mem).
Local Notation cmd := (cmd_ _ mem).
Local Notation ssem := (@ssem_ _ mem).

Fixpoint fv_ {T : Type} (e : expr T) :=
  match e with
  | var_ T x => set1 (vname x)
  | cst_ _ _ => set0
  | prp_ p => [set x | exists S m (v : vars S) y, (vname v = x) /\ p m <> p m.[v <- y]]
  | app_ _ _ l r => fv_ l `|` fv_ r
  end.

Fixpoint write_ (c : cmd) :=
  match c with
  | abort => set0
  | skip => set0
  | assign _ x _ => set1 (vname x)
  | random _ x _ => set1 (vname x)
  | cond _ c1 c2 => write_ c1 `|` write_ c2
  | while _ c => write_ c
  | seqc c1 c2 => write_ c1 `|` write_ c2
  end.

Fixpoint read_ (c : cmd) :=
  match c with
  | abort => set0
  | skip => set0
  | assign _ _ e => fv_ e
  | random _ _ d => fv_ d
  | cond b c1 c2 => fv_ b `|` read_ c1 `|` read_ c2
  | while b c1 => fv_ b `|` read_ c1
  | seqc c1 c2 => read_ c1 `|` (read_ c2 `\` write_ c1) 
  end.

Lemma disjoint_exp {T : Type} {S : IhbType.type} (e : expr T) (x : vars S) m u:
  (vname x) \notin (fv_ e)
  -> `[{e}] m = `[{e}] m.[x <- u].
Proof.
move: m u.
elim e.
+ move=> R y m u.
	rewrite notin_setE=> H.
	apply /Logic.eq_sym/mget_neq.
	by move: H=> /eqP H; right.
+ by [].
+ move=> p m u.
	rewrite notin_setE /=.
  rewrite -forallNE=> /(_ (vtype x)).
  rewrite -forallNE=> /(_ m).
	rewrite -forallNE=> /(_ x).
	rewrite -forallNE=> /(_ u).
	rewrite not_andP /=.
	rewrite not_notE.
	rewrite -implyE.
	by move=> /(_ Logic.eq_refl) ->.
move=> U V e1 + e2 + m u /=.
move=> + /[swap].
move=> /[swap].
by rewrite -disjoint1 disjointUr !disjoint1=> - [-> ->] <- // <-.
Qed.

Lemma eq_exp_mem {T : Type} (e : expr T) m m':
	(forall S (x : vars S), vname x \in fv_ e -> m.[x] = m'.[x])
  -> `[{e}] m = `[{e}] m'.
Proof.
elim e.
+ move=> S y /= H.
	apply H.
	by rewrite in_set1.
+ by [].
+	admit.
move=> U V e1 + e2 + /= H.
move=> <-.
+ move=> S x x_in.
	apply H.
	by rewrite in_setU x_in.
move=> <- //.
move=> S x x_in.
apply H.
by rewrite in_setU x_in orbT.
Admitted.

Lemma disjoint_cmd {T : Type} (c : cmd) (e : expr T):
  [disjoint (write_ c) & (fv_ e)]
  -> forall (m m': mem), m' \in dinsupp (ssem c m)
  -> `[{e}] m = `[{e}] m'.
Proof.
elim c.
+ move=> _ m m'.
  rewrite ssem_abortE.
  move=> /dinsuppP.
  by rewrite dnullE.
+ move=> _ m m'.
  rewrite ssem_skipE.
  by move=> /in_dunit ->.
+ move=> t.
  move=> y e1 /=.
  move=> /disjoint1 H m m'.
  rewrite ssem_assnE.
  move=> /in_dunit ->.
  exact /disjoint_exp/H.
+ move=> t. 
  move=> y e1.
  move=> /disjoint1 H m m'.
  rewrite ssem_rndE.
  move=> /dinsupp_dlet [u] _.
  move=> /in_dunit ->.
  exact /disjoint_exp/H.
+ move=> e1 c0 Hl c1 Hr /=.
	rewrite disjointUl=> - [] {}/Hl Hl {}/Hr Hr m m'.
	rewrite ssem_ifE.
	case: ifPn=> _.
	+ by move=> /Hl.
	by move=> /Hr.
+ move=> e1 c0 /= H.
  move=> {}/H H m m'.
  rewrite ssem_whileE.
  move=> /dinsupp_dlim [k].
  case k.
  + move=> /=.
    rewrite ssem_abortE.
    move=> /dinsuppP.
    by rewrite dnullE.
  move=> n.
  rewrite whilen_iterc.
  rewrite ssem_seqE.
  move=> /dinsupp_dlet [m1].
  rewrite ssem_ifE ssem_abortE ssem_skipE -in_dinsupp.
	case: ifPn.
  + move=> _ _ /dinsuppP.
    by rewrite dnullE.
 	move=> _ + /in_dunit ->.
  move: m1.
  elim n.
  + move=> m1.
    rewrite iterc0 ssem_skipE.
    by move=> /in_dunit ->.
  move=> n0 IH2 m1.
  rewrite itercSr ssem_seqE.
  move=> /dinsupp_dlet [m2] /IH2 H2.
  rewrite ssem_ifE -in_dinsupp ssem_skipE.
  case (`[{e1}] m2); last first.
  + by move=> /in_dunit ->.
  rewrite {}H2.
  by apply H.
move=> c0 Hl c1 Hr /=.
rewrite disjointUl=> - [] {}/Hl Hl {}/Hr Hr m m'.
rewrite ssem_seqE.
move=> /dinsupp_dlet [m1] /Hl m1v.
rewrite -in_dinsupp=> /Hr <-.
exact (m1v).
Qed.

Lemma disjoint_cond (c ct cf : cmd) (e : expr bool):
  [disjoint (write_ c) & (fv_ e)]
  -> forall m,
   ssem (c ;; (If e then ct else cf)) m = (if `[{e}] m then ssem (c ;; ct) m else ssem (c ;; cf) m).
Proof.
move=> /disjoint_cmd + m.
rewrite !ssem_seqE.
case: ifPn=> He /(_ m) H.
+ apply eq_in_dlet; last done.
  move=> m' {}/H.
	by rewrite ssem_ifE He=> <-.
apply eq_in_dlet; last done.
move=> m' {}/H.
by rewrite ssem_ifE (negbTE He)=> <-.
Qed.

End Variables.

Notation fv := (@fv_ _ cmem).
Notation write := (@write_ _ cmem).
Notation read := (@read_ _ cmem).
Notation rfv := (@fv_ _ rmem).
Notation rwrite := (@write_ _ rmem).

Section Swapping.

Lemma mset_swap {S T : IhbType.type} (m : cmem) (x : vars T) (y : vars S) e u:
	vname x != vname y
	-> (m.[x <- e]).[y <- u] = (m.[y <- u]).[x <- e].
Proof.
move=> neqxy.
apply mem_ext=> R.
have [/[dup] _ <- z | /eqP neqSR] := eqVneq S R; last first.
+ have [/[dup] eqTR <- z | /eqP neqTR z] := eqVneq T R.
	+ have [eqxz|neqxz] := eqVneq x z.
		+ rewrite -eqxz mget_eq mget_neq.
			+ by right; rewrite eq_sym.
			by rewrite mget_eq.
		move: x e neqxy z neqxz.
		rewrite eqTR=> x e _ z /vars_neq neqxz.
		rewrite !mget_neq /vtype //=.
		+ by left.
		+ by right.
		+ by right.
		by left.
	by rewrite !mget_neq /vtype //=; left.
move: x y e u neqxy z.
have [<- | /eqP neqTS] := eqVneq T S.
+ move=> x y e u neqxy z.
	have [eqxz|/vars_neq neqxz] := eqVneq x z.
		+ rewrite -eqxz mget_eq mget_neq.
			+ by right; rewrite eq_sym.
			by rewrite mget_eq.
		have [eqyz|/vars_neq neqyz] := eqVneq y z.
		+ rewrite -eqyz mget_eq mget_neq.
			+ by right. 
			by rewrite mget_eq.
		by rewrite !mget_neq /vtype //; right.
move=> x y e u neqxy z.
have [eqyz|/vars_neq neqyz] := eqVneq y z.
+ rewrite -eqyz mget_eq mget_neq.
	+ by right. 
	by rewrite mget_eq.
rewrite !mget_neq /vtype //.
+ by right.
+ by left.
+ by left.
by right.
Qed.

Lemma swap_abort (c : cmd):
	(abort ;; c) =C (c ;; abort).
Proof. by rewrite seq_abort_l seq_abort_r. Qed.

Lemma swap_skip (c : cmd):
	(skip ;; c) =C (c ;; skip).
Proof. by rewrite seq_skip_l seq_skip_r. Qed.

Lemma swap_asgn_asgn {S T : IhbType.type} (x : vars T) (y : vars S) e (u : expr S):
	vname x <> vname y
	-> vname x \notin fv u
	-> vname y \notin fv e
	-> (x <<- e ;; y <<- u) =C (y <<- u ;; x <<- e).
Proof.
move=> /eqP H1 H2 H3 m.
rewrite !ssemE !dlet_unit !ssemE.
congr dunit.
have <-: `[{u}] m = `[{u}] m.[x <- `[{e}] m] by apply disjoint_exp.
have <-: `[{e}] m = `[{e}] m.[y <- `[{u}] m] by apply disjoint_exp.
by apply mset_swap.
Qed.

Lemma swap_samp_asgn {S T : IhbType.type} (x : vars T) (y : vars S) d (e : expr S):
	vname x <> vname y
	-> vname x \notin fv e
	-> vname y \notin fv d
	-> (x <$- d ;; y <<- e) =C (y <<- e ;; x <$- d).
Proof.
move=> /eqP H1 H2 H3 m.
rewrite !ssemE dlet_unit dlet_dlet !ssemE.
have H4: forall i, `[{e}] m = `[{e}] m.[x <- i] by move=> i; apply disjoint_exp.
under eq_in_dlet=> [m' _ |] do [rewrite dlet_unit ssemE -H4|].
have <-: `[{d}] m = `[{d}] m.[y <- `[{e}] m] by apply disjoint_exp.
apply eq_in_dlet=> //.
move=> v _.
congr dunit.
by apply mset_swap.
Qed.

Lemma dlet_swap (T U V: choiceType) (d1 : {distr T / R}) (d2 : {distr U / R}) (F : T -> U -> {distr V / R}):
    \dlet_(x1 <- d1) (\dlet_(x2 <- d2) F x1 x2)
  = \dlet_(x2 <- d2) (\dlet_(x1 <- d1) F x1 x2).
Proof.
apply distr_eqP=> c; rewrite !dletE.
pose G ab := (dprod d1 d2 ab) * (fun v => F v.1 v.2) ab c.
under eq_psum=> x.
+ rewrite dletE -psumZ.
	+ by apply ge0_mu.
	rewrite (@eq_psum R U _ (fun y => G (x, y))).
	+ move=> y /=.
		by rewrite /G /= mulrA dprodE.
	over.
under [RHS]eq_psum=> y.
+ rewrite dletE -psumZ.
	+ by apply ge0_mu.
	rewrite (@eq_psum R T _ (fun x => G (x, y))).
	+ move=> x /=.
	  by rewrite /G dprodE /= mulrA [d2 y * _]mulrC.
	over.
have sumG : summable G.
+ by apply summable_mlet.
by rewrite -psum_pair // -psum_pair_swap.
Qed.

Lemma swap_samp_samp {S T : IhbType.type} (x : vars T) (y : vars S) d1 d2:
	vname x <> vname y
	-> vname x \notin fv d2
	-> vname y \notin fv d1
	-> (x <$- d1 ;; y <$- d2) =C (y <$- d2 ;; x <$- d1).
Proof.
move=> /eqP H1 H2 H3 m.
rewrite !ssemE !dlet_dlet.
have H4: forall i, `[{d2}] m = `[{d2}] m.[x <- i] by move=> i; apply disjoint_exp.
have H5: forall i, `[{d1}] m = `[{d1}] m.[y <- i] by move=> i; apply disjoint_exp.
under eq_in_dlet=> [m' _|] do [rewrite dlet_unit ssemE -H4|].
under [RHS]eq_in_dlet=> [m' _ |] do [rewrite dlet_unit ssemE -H5|].
rewrite dlet_swap.
apply eq_in_dlet=> //.
move=> v _.
apply eq_in_dlet=> //.
move=> u _.
congr dunit.
by apply mset_swap.
Qed.

Lemma swap_if e c ct cf:
	(ct ;; c) =C (c ;; ct)
	-> (cf ;; c) =C (c ;; cf)
	-> [disjoint write c & fv e]
	-> (If e then ct else cf ;; c) =C (c ;; If e then ct else cf).
Proof.
move=> Hct Hcf /disjoint_cond Hcond m.
by rewrite Hcond if_seq -Hct -Hcf ssemE.
Qed.

Lemma swap_while e c ct:
	(ct ;; c) =C (c ;; ct)
	-> [disjoint write c & fv e]
	-> (While e Do ct ;; c) =C (c ;; While e Do ct).
Proof.
move=> Hct Hcond m.
rewrite !ssemE.
under [RHS]eq_in_dlet=> [v _|] do [rewrite ssemE|].
rewrite -dlim_let.
+ by apply homo_whilen.
rewrite dlet_lim.
+ by apply homo_whilen.
apply eq_dlim=> n.
rewrite -!ssem_seqE.
elim: n m.
+ move=> /=.
	by apply swap_abort.
move=> /= n H.
apply swap_if=> //; last by apply swap_skip.
rewrite seqA -Hct.
move=> m.
rewrite -seqA ssem_seqE.
under eq_in_dlet=> [m' _|] do [rewrite H|].
by rewrite -ssem_seqE seqA.
Qed.

Lemma swap_cmd c1 c2:
	[disjoint (write c1) & (read c2 `|` write c2)]
	-> [disjoint (write c2) & (read c1)]
	-> (c1 ;; c2) =C (c2 ;; c1).
Proof.
elim c1.
+	by rewrite swap_abort.
+ by rewrite swap_skip.
+ move=> T x e /=.
	elim c2.
	+	by rewrite swap_abort.
	+ by rewrite swap_skip.
	+ move=> S y u /=.
		rewrite disjointUr !disjoint1=> - [H1].
		rewrite notin_setE /= => H2 H3.
		by apply swap_asgn_asgn.
	+ move=> S y u /=.
		rewrite disjointUr !disjoint1=> - [H1].
		rewrite notin_setE /= => H2 H3 m.
		apply /Logic.eq_sym/swap_samp_asgn=> //.
		apply /eqP.
		rewrite eq_sym.
		by move: H2=> /eqP.
	+ move=> b ct Hct cf Hcf /=.
		rewrite -!setUA.
	  rewrite disjointUr=> - [] Hdx.
		rewrite [write ct `|` _]setUC [read cf `|` _]setUA [_ `|` write ct]setUC [read ct `|` _]setUA.
		rewrite disjointUr=> - [] {}/Hct Hct {}/Hcf Hcf.
		rewrite disjointUl=> - [] {}/Hcf Hcf {}/Hct Hct.
		move=> m.
		by apply /Logic.eq_sym/swap_if.
	+ move=> b ct Hct /=.
		rewrite -!setUA.
	  rewrite disjointUr=> - [] Hdx {}/Hct Hct.
		move=> {}/Hct Hct.
		move=> m.
		by apply /Logic.eq_sym/swap_while.
	move=> d1 /= + d2  +/=.
	rewrite !disjointUr !disjointUl=> Hd1 Hd2 - [] [H1 H2] [H3 H4] [H5 H6].
	rewrite seqA Hd1 //.
	rewrite -seqA Hd2 //; last by rewrite seqA.
	split; last by exact H4.
	have := disjointUr (set1 (vname x)) (write d1) (read d2 `\` write d1).
	rewrite {}H3 {}H2 (rwP andP) /=.
	rewrite setUDr setDv setD0.
	move=> [] _ /implyP /=.
	by rewrite disjointUr=> - [] _.
+ move=> T x d /=.
	elim c2.
	+	by rewrite swap_abort.
	+ by rewrite swap_skip.
	+ move=> S y u /=.
		rewrite disjointUr !disjoint1=> - [H1].
		rewrite notin_setE /= => H2 H3.
		by apply swap_samp_asgn.
	+ move=> S y u /=.
		rewrite disjointUr !disjoint1=> - [H1].
		rewrite notin_setE /= => H2 H3 m.
		apply /Logic.eq_sym/swap_samp_samp=> //.
		apply /eqP.
		rewrite eq_sym.
		by move: H2=> /eqP.
	+ move=> b ct Hct cf Hcf /=.
		rewrite -!setUA.
	  rewrite disjointUr=> - [] Hdx.
		rewrite [write ct `|` _]setUC [read cf `|` _]setUA [_ `|` write ct]setUC [read ct `|` _]setUA.
		rewrite disjointUr=> - [] {}/Hct Hct {}/Hcf Hcf.
		rewrite disjointUl=> - [] {}/Hcf Hcf {}/Hct Hct.
		move=> m.
		by apply /Logic.eq_sym/swap_if.
	+ move=> b ct Hct /=.
		rewrite -!setUA.
	  rewrite disjointUr=> - [] Hdx {}/Hct Hct.
		move=> {}/Hct Hct.
		move=> m.
		by apply /Logic.eq_sym/swap_while.
	move=> d1 /= + d2  +/=.
	rewrite !disjointUr !disjointUl=> Hd1 Hd2 - [] [H1 H2] [H3 H4] [H5 H6].
	rewrite seqA Hd1 //.
	rewrite -seqA Hd2 //; last by rewrite seqA.
	split; last by exact H4.
	have := disjointUr (set1 (vname x)) (write d1) (read d2 `\` write d1).
	rewrite {}H3 {}H2 (rwP andP) /=.
	rewrite setUDr setDv setD0.
	move=> [] _ /implyP /=.
	by rewrite disjointUr=> - [] _.
+ move=> e ct Hct cf Hcf /=.
	rewrite disjointUl=> - [] {}/Hct Hct {}/Hcf Hcf.
	rewrite !disjointUr=> - [[]] /disjoint_cond Hcond {}/Hct Hct {}/Hcf Hcf m.
	by rewrite Hcond if_seq -Hct -Hcf ssemE.
+ move=> e ct /= Hct.
	move=> {}/Hct Hct.
	rewrite disjointUr=> - [] /[swap] /Hct.
	by apply swap_while.
move=> d1 Hd1 d2 Hd2 /=. 
rewrite disjointUl=> - [] /[dup] + {}/Hd1 Hd1 {}/Hd2 Hd2.
rewrite disjointUr=> - [_ Hdw1].
rewrite disj_set_sym in Hdw1.
rewrite disjointUr=> - [] {}/Hd1 Hd1 Hdw2.
have := disjointUr (write c2) (write d1) (read d2 `\` write d1).
rewrite {}Hdw1 {}Hdw2.
rewrite (rwP andP) /=.
rewrite setUDr setDv setD0.
move=> [] _.
move=> /implyP /=.
rewrite disjointUr=> - [] _ {}/Hd2 Hd2.
by rewrite -seqA Hd2 seqA Hd1 seqA.
Qed.

End Swapping.

(*
Section Prod.

Definition edprod {T S : IhbType.type} := @cst_ ident cmem _ (fun d1 d2 => dprod d1 d2).

Lemma sem_dprod {T S : IhbType.type} (x : vars T) (y : vars S) v d1 d2:
	(x <$- d1 ;; y <$- d2 ;; v <<- app2_ (pair %:S) ` x ` y) =C (v <$- app2_ edprod d1 d2 ;; x <<- app_ (fst %:S) ` v ;; y <<- app_ (snd %:S) ` v).
Proof.
move=> m.
rewrite !ssem_seqE !ssem_rndE /= dprod_dlet !dlet_dlet.
apply eq_in_dlet=> //.
move=> u usupp.
rewrite dlet_unit ssem_rndE !dlet_dlet.
apply eq_in_dlet; last first.

End Prod.
*)

(* -------------------------------------------------------------------- *)
(* Judgement Definition *)
(* -------------------------------------------------------------------- *)

Implicit Types P Q R I : rassn.
Implicit Types c r s t : cmd.

Definition dprhl P r1 r2 c1 c2 s1 s2 Q :=
  forall m : rmem, P m
	-> exists2 ν,
  		isprecoupling
    	(ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2)
    	(ssem s1) (ssem s2)
    	ν
  		& range Q ν.

(* -------------------------------------------------------------------- *)
Lemma dprhlw P r1 r2 c1 c2 s1 s2 Q m :
  dprhl P r1 r2 c1 c2 s1 s2 Q
	-> P m
	-> { ν | isprecoupling (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2) (ssem s1) (ssem s2) ν & range Q ν }.
Proof.
move=> h Pm.
have: exists ν, 
  isprecoupling (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2) (ssem s1) (ssem s2) ν
  /\ range Q ν.
+ by case: (h _ Pm) => ν h1 h2; exists ν; split.
by case/cid=> ν [h1 h2]; exists ν.
Qed.


(* -------------------------------------------------------------------- *)
Lemma dprhl_sem P r1 r2 r'1 r'2 c1 c2 c'1 c'2 s1 s2 s'1 s'2 Q :
  r1 =C r'1
  -> r2 =C r'2
  -> c1 =C c'1
  -> c2 =C c'2
  -> s1 =C s'1
  -> s2 =C s'2
  -> dprhl P r'1 r'2 c'1 c'2 s'1 s'2 Q
  -> dprhl P r1 r2 c1 c2 s1 s2 Q.
Proof.
move=> eq1 eq2 eq3 eq4 eq5 eq6 h m Pm.
case: (h _ Pm).
move=> x.
rewrite !ssemE /isprecoupling !dlet_dmargin eq1 eq2.
move=> [hCl hCr hR].
exists x => //.
rewrite !dlet_dmargin.
under [\dlet_(m' <- ssem r'1 _) _]eq_in_dlet => [? _ |] do [rewrite eq3|].
under [\dlet_(m' <- ssem r'2 _) _]eq_in_dlet => [? _ |] do [rewrite eq4|].
under eq_in_dlet => [? _ |] do [rewrite eq5|].
under [X in _ /\ X = _]eq_in_dlet => [? _ |] do [rewrite eq6|].
by [].
Qed.

(* -------------------------------------------------------------------- *)
(* Synchronous Rules *)
(* -------------------------------------------------------------------- *)


Lemma dprhl_skip P r1 r2 Q:
	dprhl Q r1 r2 skip skip r1 r2 Q.
Proof.
move=> m H.
exists (dunit m).
+ by split; rewrite dmargin_dunit dlet_unit seq_skip_r.
by apply/range_dunit/H.
Qed.

Lemma dprhl_sample {T U : IhbType.type} P r1 r2 (x1 : vars T) d1 (x2 : vars U) d2 Q:
  [disjoint (write r1) & ((vname x1) |` (fv d1))]
	-> [disjoint (write r2) & ((vname x2) |` (fv d2))]
	-> (vname x1) \notin (read r1)
	-> (vname x2) \notin (read r2)
	-> (forall m, P m -> exists mu,
		dfst mu = `[{d1}] m.1
		/\ dsnd mu = `[{d2}] m.2
		/\ (forall u v, (u, v) \in dinsupp mu -> Q (m.[~1 x1 <- u].[~2 x2 <- v])))
	-> dprhl P r1 r2 (x1 <$- d1) (x2 <$- d2) r1 r2 Q.
Proof.
rewrite !disjointUr=> - [] H1 H2 [] H3 H4 H5 H6.
move=> H m {}/H [mu [cplL [cplR cplS]]].
exists (\dlet_(w <- mu) dunit (m.[~1 x1 <- w.1].[~2 x2 <- w.2])); last first.
+ move=> m' /dinsupp_dlet [[u v]] /cplS Hq.
	rewrite dunit1E.
	have [] := eqVneq (m.[~1 x1 <- u]).[~2 x2 <- v] m'.
	+ move=> <- _.
		exact Hq.
	move=> _.
	by rewrite eq_refl.
rewrite swap_cmd.
+ by rewrite disjointUr H2 H1.
+ by rewrite disjoint1.
rewrite [r2 ;; _]swap_cmd.
+ by rewrite disjointUr H4 H3.
+ by rewrite disjoint1.
rewrite !ssemE !dlet_dlet -cplL -cplR.
split.
+ rewrite !dlet_dmargin.
	apply eq_in_dlet=> //.
	move=> v _. 
	by rewrite dlet_unit -/(mselect '1 _) !mselect_mset.
rewrite !dlet_dmargin.
apply eq_in_dlet=> //.
move=> v _. 
by rewrite dlet_unit -/(mselect '2 _) !mselect_mset.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_seq P r1 r2 c1 c2 R t1 t2 c1' c2' s1 s2 Q:
  dprhl P r1 r2 c1 c2 t1 t2 R
  -> dprhl R t1 t2 c1' c2' s1 s2 Q
  -> dprhl P r1 r2 (c1 ;; c1') (c2 ;; c2') s1 s2 Q.
Proof.
move=> h1 h2 m Pm.
case: (h1 _ Pm) => ν hC hR.
pose f m :=
  if @idP (m \in dinsupp ν) is ReflectT Rm then
    tag (dprhlw h2 (hR _ Rm))
  else dnull.
exists (\dlet_(m <- ν) f m); last first.
+ apply: (range_dlet hR) => m' Rm'; rewrite /f.
  case: {-}_ / idP; first by move=> p; case: dprhlw.
  by move=> _ x /dinsuppP; rewrite dnullE.
rewrite 2!seqA ssem_seqE [ssem (r2 ;; c2 ;; c2') _]ssem_seqE. 
apply: isprecoupling_dlet; first exact hC.
move=> m' hm'; rewrite /f; case: {-}_ / idP => //.
move=> p; case: dprhlw.
by rewrite !ssemE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_if P e1 e2 c1 c'1 c2 c'2 Q r1 r2 s1 s2:
  [disjoint (write r1) & (fv e1)]
  -> [disjoint (write r2) & (fv e2)]
  -> dprhl (P /\ `[{    e1#'1 &&    e2#'2 }])%A r1 r2 c1  c2  s1 s2 Q
  -> dprhl (P /\ `[{ ~~ e1#'1 && ~~ e2#'2 }])%A r1 r2 c'1 c'2 s1 s2 Q
  -> dprhl (P /\ `[{ e1#'1 =b e2#'2 }])%A r1 r2
       (If e1 then c1 else c'1)
       (If e2 then c2 else c'2)
       s1 s2 Q.
Proof.
move=> /(disjoint_cond c1 c'1) eq1 /(disjoint_cond c2 c'2) eq2 h1 h2 m /andP [/= Pm /eqP].
rewrite eq1 eq2 ssemE ssemE => eqe.
rewrite -eqe.
case: ifPn => hc.
+ by apply/h1 => /=; rewrite Pm !ssemE -eqe hc.
+ by apply/h2 => /=; rewrite Pm !ssemE -eqe hc.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_while I e1 e2 c1 c2 r1 r2:
  [disjoint (write r1) & (fv e1)]
  -> [disjoint (write r2) & (fv e2)]
  -> (forall m : rmem, I m -> `[{ e1#'1 =b e2#'2 }] m)
  -> (dprhl (I /\ `[{ e1#'1 && e2#'2 }])%A r1 r2 c1 c2 r1 r2 I)
  ->
  dprhl
    I 
			r1 r2
      (While e1 Do c1)
      (While e2 Do c2)
			r1 r2
    (I /\ `[{ ~~ e1#'1}] /\ `[{ ~~ e2#'2 }])%A.
Proof.
set J := (I /\ _)%A => Hdisj1 Hdisj2 hs h.
pose ν1 m := if @idP (J m) is ReflectT Rm then tag (dprhlw h Rm) else dunit m.
pose νn := fix νn n m {struct n} :=
  if n is n.+1 then \dlet_(m' <- νn n m) ν1 m' else dunit m.
pose νe n m := \dlet_(m' <- νn n m) if esem e1 m'.1 then dnull else dunit m'.
move=> m Im; pose ν n := νe n m.
have rg_νn: forall n, range I (νn n m).
+ elim=> [|n ih] /=; first by apply/range_dunit.
  apply/(range_dlet ih) => {Im ν ih} m Im; rewrite /ν1.
  case: {-}_ / idP; first by move=> p; case: dprhlw.
  by move=> _; apply/range_dunit.
have mono_ν n : ν n <=1 ν n.+1.
+ move=> /= m'; rewrite /ν /νe dlet_dlet -/(νn _ _).
  apply/le_dlet => //= {}m' Im' m''.
  case: ifPn => [he1|hNe1]; first by apply/lef_dnull.
  rewrite dunit1E; case: eqP => /= [<-|_]; last by apply/ge0_mu.
  have /distr_eqP ->: ν1 m' =1 dunit m'.
  * rewrite /ν1; case: {-}_ / idP => // p; move: {-}p.
    by rewrite /J /= ssemE (negbTE hNe1) andbF.
  by rewrite dlet_unit (negbTE hNe1) dunit1E eqxx.
exists (dlim ν).
+ rewrite !ssemE.
  under eq_in_dlet => [i _|] do [rewrite ssemE -(iffLR (distr_eqP _ _) (dlim_bump (fun _ => _ i)))|].
  under [\dlet_(m' <- ssem r2 m.2) _ ]eq_in_dlet => [i _|] do [rewrite ssemE -(iffLR (distr_eqP _ _) (dlim_bump (fun _ => _ i)))|].
  rewrite -!dlim_let.
  + by move=> x n p Hm; apply/homo_whilen/Hm.
  + by move=> x n p Hm; apply/homo_whilen/Hm.
  apply/isprecoupling_dlim=> [n|n k le_nk]; last first.
  * move=> m'; rewrite -[k](subnK le_nk); elim: (_ - _)%N => //.
    by move=> n' ihn'; rewrite addSn; apply/(le_trans ihn').
  under eq_in_dlet => [i _|] do [rewrite !whilen_iterc !ssemE|].
  under [\dlet_(x <- ssem r2 m.2) _]eq_in_dlet => [i _|] do [rewrite !whilen_iterc !ssemE|].
  rewrite -!dlet_dlet.
  apply/(@isprecoupling_dlet _ _ _ _ _ _ (ssem r1) (ssem r2)) => /=; last first.
  * move=> m' Im'.
    rewrite -!ssem_seqE.
    move: Hdisj1 Hdisj2=> /(disjoint_cond abort skip) -> /(disjoint_cond abort skip) ->.
    rewrite !seq_skip_r !seq_abort_r !ssemE.
		move/rg_νn/hs: Im'.
    rewrite !ssemE => /eqP <-; case: ifPn => _.
    - by apply/isprecoupling_dnull.
    - by case: m' => a b; apply/isprecoupling_dunit.
  elim: n => /= [|n ihn].
  * rewrite !iterc0 -!ssem_seqE !seq_skip_r.
    by case: {+}m => a b; apply/isprecoupling_dunit.
  under eq_in_dlet => [i _|] do [rewrite itercSr !ssemE |].
  under [\dlet_(x <- ssem r2 _) _]eq_in_dlet => [i _|] do [rewrite itercSr !ssemE |].
  rewrite -!dlet_dlet.
  apply/(@isprecoupling_dlet _ _ _ _ _ _ (ssem r1) (ssem r2))=> //= m' /rg_νn Im'; move/hs: (Im').
  rewrite !ssemE => /eqP eqe.
  rewrite -!ssem_seqE.
    move: Hdisj1 Hdisj2=> /(disjoint_cond c1 skip) -> /(disjoint_cond c2 skip) ->.
  rewrite -eqe /ν1.
  case: {-}_ / idP => /= [p|]; first case/and3P: {+}p.
  * by rewrite !ssemE => _ -> _; case: dprhlw.
  rewrite !ssemE -eqe Im' /= andbb => /negP/negbTE => ->/=.
  rewrite -!ssem_seqE !seq_skip_r.
  by case: {+}m' => a b; apply/isprecoupling_dunit.  
+ apply/range_dlim => n; apply/(range_dlet (rg_νn n)) => m' Im'.
  case: ifPn => [he1|hNe1]; first by apply/range_dnull.
  apply/range_dunit=> /=; rewrite Im' /= !ssemE.
  by move: (hs _ Im'); rewrite !ssemE => /eqP <-; rewrite hNe1.
Qed.


(* -------------------------------------------------------------------- *)
(* Asynchronous Rules *)
(* -------------------------------------------------------------------- *)

Lemma dprhl_assignL {T : IhbType.type} Q r1 r2 (x : vars T) (e : expr T) :
  [disjoint (write r1) & ((vname x) |` (fv e))]
	->  (vname x) \notin (read r1)
  -> dprhl [pred m : rmem | Q m.[~1 x <- `[{ e }] m.1]] r1 r2 (x <<- e) skip r1 r2 Q.
Proof.
rewrite disjointUr=> - [] H1 H2 H3.
move=> m /= Qmxe; exists (dunit (m.[~1 x <- `[{ e }] m.1])); last first.
+ by apply/range_dunit.
rewrite swap_cmd.
+ by rewrite disjointUr H2 H1.
+ by rewrite disjoint1.
rewrite seq_skip_r.
split; first last.
+ by rewrite dlet_dmargin dlet_unit -/(mselect '2 _) mselect_mset.
rewrite dlet_dmargin dlet_unit -/(mselect '1 _) mselect_mset /=.
by rewrite !ssemE dlet_unit.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_rndL {t : IhbType.type} P (x : vars t) (d : dexpr t) r1 r2 Q :
  [disjoint (write r1) & ((vname x) |` (fv d))]
	->  (vname x) \notin (read r1)
	-> P =1 [pred m : rmem
       |  dweight (`[{ d }] m.1) == 1
       & `[< range [pred v | Q m.[~1 x <- v]] (`[{ d }] m.1) >]]
  -> dprhl P r1 r2 (x <$- d) skip r1 r2 Q.
Proof.
rewrite disjointUr disj_set_sym disjoint1=> - [] H1 H2 H3 HP.
move=> m.
rewrite (HP m)=> - /andP [/eqP d_ll /asboolP d_rng].
rewrite -swap_skip swap_cmd /=.
+ by rewrite disjointUr H2 disj_set_sym disjoint1.
+ by rewrite disjoint1.
exists (\dlet_(v <- `[{d}] m.1) dunit (m.[~1 x <- v])); last first.
+ move=> m' /dinsupp_dlet [v] vsupp /eqP/dinsuppP/in_dunit ->.
  by apply d_rng.
split.
+ rewrite !ssemE dmargin_dlet !dlet_dlet.
	apply eq_in_dlet=> //=. 
	move=> y ysupp.
	by rewrite dlet_dmargin !dlet_unit -/(mselect '1 _) mselect_mset.
apply distr_eqP=> m'.
rewrite seq_skip_l dmargin_dlet dlet_dlet -[RHS]mul1r -d_ll -dletC.
rewrite !dletE /vtype /=.
apply eq_psum=> v.
congr (_ * _).
by rewrite dlet_dmargin dlet_unit -/(mselect '2 _) mselect_mset.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_seqL1 P r1 r2 c1 c2 R t1 t2 c1' s1 s2 Q:
  dprhl P r1 r2 c1 skip t1 t2 R
  -> dprhl R t1 t2 c1' c2 s1 s2 Q
  -> dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q.
Proof.
move=> Htop Hbot.
apply: dprhl_sem; last first.
apply: dprhl_seq.
+ exact Htop.
+ exact Hbot.
+ by [].
+ by [].
+ by rewrite seq_skip_l.
+ by [].
+ by [].
by [].
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_seqL2 P r1 r2 c1 c2 R t1 t2 c1' s1 s2 Q:
  dprhl P r1 r2 c1 c2 t1 t2 R
  -> dprhl R t1 t2 c1' skip s1 s2 Q
  -> dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q.
Proof.
move=> Htop Hbot.
apply: dprhl_sem; last first.
apply: dprhl_seq.
+ exact Htop.
+ exact Hbot.
+ by [].
+ by [].
+ by rewrite seq_skip_r.
+ by [].
+ by [].
by [].
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_ifL P e c1 c2 c Q r1 r2 s1 s2:
  [disjoint (write r1) & (fv e)]
  -> dprhl (P /\ `[{    e#'1 }])%A r1 r2 c1 c s1 s2 Q
  -> dprhl (P /\ `[{ ~~ e#'1 }])%A r1 r2 c2 c s1 s2 Q
  -> dprhl P r1 r2 (If e then c1 else c2) c s1 s2 Q.
Proof.
move=> /(disjoint_cond c1 c2) eq h1 h2 m Pm; rewrite eq; case: ifPn => he.
+ by apply/h1 => /=; rewrite ssemE Pm.
+ by apply/h2 => /=; rewrite ssemE Pm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_whileL I e1 c1 r1 r2:
  [disjoint (write r1) & (fv e1)]
  -> (dprhl (I /\ `[{ e1#'1 }])%A r1 r2 c1 skip r1 r2 I)
	-> (forall m, I m -> dweight (ssem (While e1 Do c1) m.1) = 1)
	->
  dprhl
    I 
			r1 r2
      (While e1 Do c1)
      skip
			r1 r2
    (I /\ `[{ ~~ e1#'1}])%A.
Proof.
Admitted.

(* -------------------------------------------------------------------- *)
(* Structural Rules *)
(* -------------------------------------------------------------------- *)

Lemma dprhl_delayL Q r1 r2 c1 c2:
  dprhl Q r1 r2 c1 skip (r1 ;; c1) r2 Q.
Proof.
move=> m Qm.
exists (dunit m).
+ split; rewrite dmargin_dunit dlet_unit //.
  by rewrite seq_skip_r.
by apply: range_dunit.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_delaystarL P Q r1 r2 c1 s1:
	(forall m1 m2, Q (m1, m2) -> P (m1, m1))
  -> dprhl (P /\ [ pred m | m.1 == m.2 ])%A r1 skip c1 s1 skip skip [ pred m | m.1 == m.2 ]
  -> dprhl Q r1 r2 c1 skip s1 r2 Q.
Proof.
move=> Hp H [m1 m2 /[dup] Hq /Hp HP].
move: (H (m1, m1)).
rewrite /= eq_refl HP /=.
case; first done.
move=> v.
rewrite seq_skip_l.
move=> H2 /=.
exists (dunit (m1, m2)); last by apply range_dunit.
rewrite seq_skip_r.
split; rewrite dlet_dmargin dlet_unit //=.
move: H2=> [<- <-].
congr (\dlet_(_ <- _) _).
apply distr_eqP=> w. 
rewrite dfstE dsndE.
apply eq_psum=> m.
have [->|Hneq] := eqVneq m w.
+ by [].
suff : forall m, m.1 != m.2	-> v m = 0.
+ move=> H2.
	by rewrite !H2 //= eq_sym.
move=> m' neq.
apply /dinsuppPn.
Search dinsupp.
case Hin: (m' \in dinsupp v)=> //.
by move: (q m' Hin) neq=> //= ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_push_popL P r1 r2 c1 c1' c2 s1 s2 Q:
  dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q
  <->
  dprhl P (r1 ;; c1) r2 c1' c2 s1 s2 Q.
Proof.
by split; move=> H m {}/H; rewrite seqA.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_conseq P P' r1 r2 c1 c2 s1 s2 Q Q' :
     (forall m, P' m -> P  m)
  -> (forall m, Q  m -> Q' m)
  -> dprhl P  r1 r2 c1 c2 s1 s2 Q
  -> dprhl P' r1 r2 c1 c2 s1 s2 Q'.
Proof.
move=> hP hQ h m /hP /h [ν hC hR]; exists ν => //.
by apply/range_weaken/hQ: hR.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_case P e r1 r2 c1 c2 s1 s2 Q :
     dprhl (P /\   `[{e}])%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl (P /\ ~ `[{e}])%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl P r1 r2 c1 c2 s1 s2 Q.
Proof.
move=> he hNe m Pm. case/boolP: (`[{e}] m) => [em | Nem].
+ by apply/he; rewrite -(rwP andP).
+ by apply/hNe; rewrite -(rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_frame P r1 r2 c1 c2 s1 s2 Q e:
	(forall p, e <> prp_ p)
	-> [disjoint (rfv e) & (rwrite (r1#'1)%S `|` rwrite (r2#'2)%S `|` rwrite (c1#'1)%S `|` rwrite (c2#'2)%S `|` rwrite (s1#'1)%S `|` rwrite (s2#'2)%S)] 
	-> dprhl P r1 r2 c1 c2 s1 s2 Q
	-> dprhl (P /\ `[{e}])%A r1 r2 c1 c2 s1 s2 (Q /\ `[{e}])%A.
Proof.
move=> Hnp Hd Hw m /= /andP [] HP HR.
case: (Hw m HP)=> v vcpl vrng.
exists v; first by [].
move=> m' m'supp /=.
apply /andP.
split; first by apply vrng.
case: vcpl.
rewrite !dlet_dmargin.
admit.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma dprhl_swap P c1 c2 Q r1 r2 s1 s2:
  dprhl P r2 r1 c2 c1 s2 s1 Q <-> dprhl (pswap P) r1 r2 c1 c2 s1 s2 (pswap Q).
Proof.
move: P Q c1 c2 r1 r2 s1 s2 => [:hG] P Q c1 c2 r1 r2 s1 s2; split; last first.
+ move: P Q c1 c2 r1 r2 s1 s2; abstract: hG => P Q c1 c2 r1 r2 s1 s2 h -[m1 m2] Pm.
  case: (h (m2, m1))=> //= ν [hC1 hC2] hR; exists (dswap ν) => /=.
  * by apply/isprecoupling_swap.
  * by move/range_pswap: hR; apply/range_weaken; case.
+ by move=> h; apply/hG ; apply/dprhl_conseq: h; case.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_exfalso c1 c2 r1 r2 s1 s2 Q : dprhl pred0 r1 r2 c1 c2 s1 s2 Q.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_abort P r1 r2 c1 c2 s1 s2 Q : dprhl P r1 r2 abort abort s1 s2 Q.
Proof.
move=> m _; exists dnull; last by apply/range_dnull.
by rewrite !seq_abort_r !ssemE; split; rewrite dmarginE !dlet_null.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_trans P12 P23 r1 r2 r3 c1 c2 c3 s1 s2 s3 Q12 Q23:
	dprhl P12 r1 r2 c1 c2 s1 s2 Q12
	-> dprhl P23 r2 r3 c2 c3 s2 s3 Q23
	-> dprhl [pred m | `[<exists m', P12 (m.1, m') /\ P23 (m', m.2)>]] r1 r3 c1 c3 s1 s3 [pred m | `[<exists m', Q12 (m.1, m') /\ Q23 (m', m.2)>]].
Proof.
move=> H12 H23 [m1 m3] /= /asboolP [m2 [HP12 HP23]].
move: (H12 (m1, m2) HP12)=> [/= v12 pc12 rng12].
move: (H23 (m2, m3) HP23)=> [/= v23 pc23 rng23].
admit.
Admitted.
