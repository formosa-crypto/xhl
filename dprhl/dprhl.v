(* -------------------------------------------------------------------- *)
From Stdlib.Logic Require Import FunctionalExtensionality.
From mathcomp           Require Import all_boot all_order all_algebra.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.
From xhl.phl    Require Import phl.

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
apply funext=> x.
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

Lemma expD {T : choiceType} (mu : Distr T) (f g : T -> R) :
     (forall x, 0 <= f x) -> (forall x, 0 <= g x)
  -> \E?_[mu] f -> \E?_[mu] g
  -> \E_[mu] (fun x => f x + g x) = \E_[mu] f + \E_[mu] g.
Proof.
move=> ge0f ge0g hf hg.
have ge0w: forall (h : T -> R), (forall x, 0 <= h x) ->
    forall x, 0 <= h x * mu x.
+ by move=> h ge0h x; rewrite mulr_ge0 ?ge0_mu.
have ge0fg: forall x, 0 <= (f x + g x) * mu x.
+ by move=> x; rewrite mulr_ge0 ?ge0_mu ?addr_ge0.
rewrite /esp -(psum_sum (ge0w _ ge0f)) -(psum_sum (ge0w _ ge0g)) -(psum_sum ge0fg).
rewrite -(psumD (ge0w _ ge0f) (ge0w _ ge0g) hf hg).
by apply/eq_psum => x /=; rewrite mulrDl.
Qed.

Lemma exp_dlet_bd {T U : choiceType} (mu : Distr T) (f : T -> Distr U)
    (F : U -> R) (M : R) :
     (forall x, 0 <= F x) -> (forall x, F x <= M)
  -> \E_[\dlet_(x <- mu) f x] F = \E_[mu] (fun x => \E_[f x] F).
Proof.
move=> ge0F leM.
have hsm: forall nu : Distr U, summable (fun y => F y * nu y).
+ move=> nu; apply/summableMl; last by apply/summable_mu.
  by exists M => y; rewrite ger0_norm ?ge0F ?leM.
have hE: forall nu : Distr U, \E_[nu] F = psum (fun y => F y * nu y).
+ move=> nu; rewrite /esp -psum_sum // => y.
  by rewrite mulr_ge0 ?ge0F ?ge0_mu.
have ge0E: forall x : T, 0 <= \E_[f x] F.
+ by move=> x; rewrite hE; apply/ge0_psum.
have ge0R: forall x : T, 0 <= \E_[f x] F * mu x.
+ by move=> x; rewrite mulr_ge0 ?ge0E ?ge0_mu.
rewrite hE /esp -(psum_sum ge0R).
have h1: forall y : U, summable (fun x : T => F y * (mu x * f x y)).
+ by move=> y; apply/summableZ/summable_mlet.
have h2: summable (fun y : U => psum (fun x : T => F y * (mu x * f x y))).
+ apply: (eq_summable (S1 := fun y => F y * (\dlet_(x <- mu) f x) y)); last first.
  + by apply/hsm.
  by move=> y; rewrite dletE -psumZ ?ge0F.
transitivity (psum (fun y => psum (fun x => F y * (mu x * f x y)))).
+ by apply/eq_psum => y; rewrite dletE -psumZ ?ge0F.
rewrite (__admitted__interchange_psum h1 h2).
apply/eq_psum => x; have h3: 0 <= mu x by apply/ge0_mu.
rewrite hE mulrC -(psumZ _ h3).
by apply/eq_psum => y /=; rewrite mulrCA.
Qed.

Lemma exp_ge0 {T : choiceType} (mu : Distr T) (F : T -> R) :
  (forall x, 0 <= F x) -> 0 <= \E_[mu] F.
Proof.
move=> ge0F; have ge0w: forall x, 0 <= F x * mu x.
+ by move=> x; rewrite mulr_ge0 ?ge0_mu.
by rewrite /esp -(psum_sum ge0w); apply/ge0_psum.
Qed.

Lemma le_exp_supp {T : choiceType} (mu : Distr T) (f g : T -> R) :
     (forall x, 0 <= f x) -> (forall x, 0 <= g x) -> \E?_[mu] g
  -> (forall x, x \in dinsupp mu -> f x <= g x)
  -> \E_[mu] f <= \E_[mu] g.
Proof.
move=> ge0f ge0g hg le_fg.
have ge0w: forall (h : T -> R), (forall x, 0 <= h x) -> forall x, 0 <= h x * mu x.
+ by move=> h ge0h x; rewrite mulr_ge0 ?ge0_mu.
rewrite /esp -(psum_sum (ge0w _ ge0f)) -(psum_sum (ge0w _ ge0g)).
apply/le_psum => // x; rewrite (ge0w _ ge0f) /=.
have [hin|hout] := boolP (x \in dinsupp mu).
+ by rewrite ler_wpM2r ?ge0_mu ?(le_fg _ hin).
by move/dinsuppPn: hout => ->; rewrite !mulr0.
Qed.

Lemma pr_dnull {T : choiceType} (A : pred T) : \P_[dnull : Distr T] A = 0.
Proof. by apply/eq0_pr => x /dinsuppP; rewrite dnullE. Qed.

Lemma le1_natb (b : bool) : ((b : nat)%:R : R) <= 1.
Proof. by case: b; rewrite ?mulr0n ?mulr1n ?ler01 ?lexx. Qed.

Lemma has_exp_natb {T : choiceType} (mu : Distr T) (A : pred T) :
  \E?_[mu] (fun x => ((A x : nat))%:R).
Proof.
by apply/bounded_has_exp; exists 1 => x; rewrite ger0_norm ?ler0n ?le1_natb.
Qed.

Lemma dweight_dlet {T U : choiceType} (mu : Distr T) (f : T -> Distr U) :
  dweight (\dlet_(x <- mu) f x) <= dweight mu.
Proof.
rewrite pr_dlet -[X in _ <= X]mulr1 -exp_cst.
apply/le_exp; last by move=> x /=; apply/le1_pr.
+ by apply/bounded_has_exp; exists 1 => x; rewrite ger0_norm ?ge0_pr ?le1_pr.
by apply/has_expC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma le_dweight_eq {T : choiceType} (mu nu : Distr T) :
  mu <=1 nu -> dweight mu = dweight nu -> mu = nu.
Proof.
move=> le_mn eqw; pose f (x : T) := nu x - mu x.
have ge0f: forall x, 0 <= f x by move=> x; rewrite subr_ge0.
have smf: summable f.
+ apply/(le_summable (F2 := nu)); last by apply/summable_mu.
  by move=> x; rewrite ge0f /= lerBlDl lerDr ge0_mu.
have hpsum: psum nu = psum mu + psum f.
+ rewrite -psumD // ?ge0_mu ?summable_mu //.
  by apply/eq_psum => x /=; rewrite /f addrCA subrr addr0.
have psum0: psum f = 0.
+ apply/esym; move: hpsum; rewrite -!pr_predT eqw.
  by rewrite -{1}[\P_[nu] predT]addr0; apply/addrI.
apply/distr_eqP => x; apply/eqP; rewrite eq_le le_mn andTb.
rewrite -subr_le0 -[_ - _]/(f x) -psum0.
by rewrite -[f x]ger0_norm ?ge0f // ger1_psum.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lt_psum_seq {T : choiceType} (S : T -> R) (l : R) :
     summable S -> l < psum S
  -> exists2 J : seq T, uniq J & l < \sum_(j <- J) `|S j|.
Proof.
move=> smS ltl; apply: contrapT => hN.
have le_l: psum S <= l.
+ apply/psum_le => J uqJ; rewrite leNgt; apply/negP => hlt.
  by apply/hN; exists J.
by move: ltl; rewrite ltNge le_l.
Qed.

(* -------------------------------------------------------------------- *)
(* Monotone convergence: the weight of an increasing limit is approached *)
(* by the weights of its approximants.                                   *)
Lemma dweight_dlim {T : choiceType} (mu : nat -> Distr T) (eps : R) :
     (forall n m, (n <= m)%N -> mu n <=1 mu m)
  -> 0 < eps
  -> exists n, dweight (\dlim_(n) mu n) - eps <= dweight (mu n).
Proof.
move=> mono gt0eps.
have cvg: forall x, iscvg (mu^~ x).
+ by move=> x; case: (dcvgP (dcvg_homo mono) x) => l _ h; exists l.
rewrite !pr_predT.
have h1: psum (\dlim_(n) mu n) - eps < psum (\dlim_(n) mu n).
+ by rewrite ltrBlDr ltrDl.
case: (lt_psum_seq (summable_mu _) h1) => J uqJ hJ.
have hcv: forall i : T, i \in J -> iscvg (fun n => mu n i).
+ by move=> i _; apply/cvg.
have iscvg_s: iscvg (fun n => \sum_(j <- J) mu n j).
+ by apply/iscvg_sum => j _; apply/cvg.
have hs: ncvg (fun n => \sum_(j <- J) mu n j)
    (\sum_(j <- J) (\dlim_(n) mu n) j)%:E.
+ have ->: (\sum_(j <- J) (\dlim_(n) mu n) j)%:E
         = nlim (fun n => \sum_(j <- J) mu n j).
  - rewrite (nlim_sumR (u := fun j n => mu n j) hcv).
    by congr (_%:E); apply/eq_bigr => j _; rewrite dlimE.
  by apply/nlim_ncvg; case: iscvg_s => l hl; exists l%:E.
have lt_s: ((psum (\dlim_(n) mu n) - eps)%:E
    < (\sum_(j <- J) (\dlim_(n) mu n) j)%:E)%E.
+ rewrite lte_fin; apply/(lt_le_trans hJ)/ler_sum => j _.
  by rewrite ger0_norm ?ge0_mu.
case: (ncvg_gt lt_s hs) => K /(_ K (leqnn K)); rewrite lte_fin => hK.
exists K; rewrite pr_predT; apply/ltW/(lt_le_trans hK).
apply/(@le_trans _ _ (\sum_(j <- J) `|mu K j|)).
+ by apply/ler_sum => j _; rewrite ger0_norm ?ge0_mu.
by apply: (gerfinseq_psum uqJ (summable_mu _)).
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
Section PartialCouplings.
Context {A B : choiceType} (v1 : Distr A) (v2 : Distr B)
  (f1: A -> Distr A) (f2: B -> Distr B).

Definition ispartialcoupling (ν : Distr (A * B)) :=
  \dlet_(m' <- dfst ν) (f1 m') = v1
  /\ \dlet_(m' <- dsnd ν) (f2 m') = v2.

End PartialCouplings.

Section PartialCouplingsTheory.

Lemma ispartialcoupling_dnull {A B : choiceType} (f1 f2 : _ -> Distr _):
	@ispartialcoupling A B dnull dnull f1 f2 dnull.
Proof.
by split; rewrite dmarginE !dlet_null.
Qed.

Lemma ispartialcoupling_dunit {A B : choiceType} (f1 f2 : _ -> Distr _) m':
@ispartialcoupling A B (f1 m'.1) (f2 m'.2) f1 f2 (dunit m').
Proof.
by split; rewrite dmarginE !dlet_unit.
Qed.

Lemma ispartialcoupling_swap {A : choiceType} (u1 u2 : Distr A) (ν : Distr (A * A)) (f1 f2 : _ -> Distr _):
  ispartialcoupling u1 u2 f1 f2 ν -> ispartialcoupling u2 u1 f2 f1 (dswap ν).
Proof.
case=> <- <-; split.
+ apply eq_in_dlet=> //.
  apply distr_eqP=> m.
	by rewrite dfst_dswap.
apply eq_in_dlet=> //.
apply distr_eqP=> m.
by rewrite dsnd_dswap.
Qed.

Lemma ispartialcoupling_dlet {A B C D: choiceType}
  (u1 u2 : Distr _) (f1 f2 : _ -> Distr _) (u: Distr (A * B))
  (v1 v2 : _ -> Distr _) (g1 g2 : _ -> Distr _) (v: _ -> Distr (C * D)) :
  ispartialcoupling u1 u2 f1 f2 u
  -> (forall x, x \in dinsupp u ->
    ispartialcoupling (\dlet_(y <- f1 x.1) (v1 y)) (\dlet_(y <- f2 x.2) (v2 y)) g1 g2 (v x))
    -> ispartialcoupling
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

Lemma ispartialcoupling_dlim {A B: choiceType}
  (μ1 μ2 : nat -> Distr _) (f1 f2 : _ -> Distr _) (ν : nat -> Distr (A * B)) :

     (forall n, ispartialcoupling (μ1 n) (μ2 n) f1 f2 (ν n))
  -> (forall n m, (n <= m)%N -> ν n <=1 ν m)
  -> ispartialcoupling (dlim μ1) (dlim μ2) f1 f2 (dlim ν).
Proof.
move=> hC mono.
rewrite /ispartialcoupling !dmarginE !dlet_lim //.
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

End PartialCouplingsTheory.

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

(* A command that commutes with every atomic command commutes with every  *)
(* command, by induction on the latter.                                   *)
Lemma swap_atomL (a c : cmd):
     [disjoint (write a) & (read c `|` write c)]
  -> [disjoint (write c) & (read a)]
  -> (forall S (y : vars S) (u : expr S),
          [disjoint (write a) & (fv u `|` set1 (vname y))]
       -> [disjoint (set1 (vname y)) & (read a)]
       -> (a ;; y <<- u) =C (y <<- u ;; a))
  -> (forall S (y : vars S) (d : dexpr S),
          [disjoint (write a) & (fv d `|` set1 (vname y))]
       -> [disjoint (set1 (vname y)) & (read a)]
       -> (a ;; y <$- d) =C (y <$- d ;; a))
  -> (a ;; c) =C (c ;; a).
Proof.
move=> + + Hasgn Hrnd; elim: c.
+	by rewrite swap_abort.
+ by rewrite swap_skip.
+ by move=> S y u /=; apply: Hasgn.
+ by move=> S y d /=; apply: Hrnd.
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
have := disjointUr (write a) (write d1) (read d2 `\` write d1).
rewrite {}H3 {}H2 (rwP andP) /=.
rewrite setUDr setDv setD0.
move=> [] _ /implyP /=.
by rewrite disjointUr=> - [] _.
Qed.

Lemma swap_cmd c1 c2:
	[disjoint (write c1) & (read c2 `|` write c2)]
	-> [disjoint (write c2) & (read c1)]
	-> (c1 ;; c2) =C (c2 ;; c1).
Proof.
elim c1.
+	by rewrite swap_abort.
+ by rewrite swap_skip.
+ move=> T x e /= Hd1 Hd2; apply: (@swap_atomL (x <<- e) c2 Hd1 Hd2).
	+ move=> S y u.
		rewrite disjointUr !disjoint1=> - [H1].
		rewrite notin_setE /= => H2 H3.
		by apply swap_asgn_asgn.
	move=> S y u.
	rewrite disjointUr !disjoint1=> - [H1].
	rewrite notin_setE /= => H2 H3 m.
	apply /Logic.eq_sym/swap_samp_asgn=> //.
	apply /eqP.
	rewrite eq_sym.
	by move: H2=> /eqP.
+ move=> T x d /= Hd1 Hd2; apply: (@swap_atomL (x <$- d) c2 Hd1 Hd2).
	+ move=> S y u.
		rewrite disjointUr !disjoint1=> - [H1].
		rewrite notin_setE /= => H2 H3.
		by apply swap_samp_asgn.
	move=> S y u.
	rewrite disjointUr !disjoint1=> - [H1].
	rewrite notin_setE /= => H2 H3 m.
	apply /Logic.eq_sym/swap_samp_samp=> //.
	apply /eqP.
	rewrite eq_sym.
	by move: H2=> /eqP.
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

(* -------------------------------------------------------------------- *)
(* Judgement Definition *)
(* -------------------------------------------------------------------- *)

Implicit Types P Q R I : rassn.
Implicit Types c r s t : cmd.

Definition dprhl P r1 r2 c1 c2 s1 s2 Q :=
  forall m : rmem, P m
	-> exists2 ν,
  		ispartialcoupling
    	(ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2)
    	(ssem s1) (ssem s2)
    	ν
  		& range Q ν.

(* -------------------------------------------------------------------- *)
Lemma dprhlw P r1 r2 c1 c2 s1 s2 Q m :
  dprhl P r1 r2 c1 c2 s1 s2 Q
	-> P m
	-> { ν | ispartialcoupling (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2) (ssem s1) (ssem s2) ν & range Q ν }.
Proof.
move=> h Pm.
have: exists ν,
  ispartialcoupling (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2) (ssem s1) (ssem s2) ν
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
rewrite !ssemE /ispartialcoupling !dlet_dmargin eq1 eq2.
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
(* Delaying, and the Synchronous Rules *)
(* -------------------------------------------------------------------- *)

(* Nothing happens now; the whole of [c1] is postponed to the delayed    *)
(* left-hand side.                                                       *)
Lemma dprhl_delayL Q r1 r2 c1:
  dprhl Q r1 r2 c1 skip (r1 ;; c1) r2 Q.
Proof.
move=> m Qm; exists (dunit m); last by apply: range_dunit.
by split; rewrite dmargin_dunit dlet_unit ?seq_skip_r.
Qed.

(* -------------------------------------------------------------------- *)
(* ... of which [dprhl_skip] is the empty-body instance.                 *)
Lemma dprhl_skip r1 r2 Q:
	dprhl Q r1 r2 skip skip r1 r2 Q.
Proof.
apply: (dprhl_sem _ _ _ _ _ _ (dprhl_delayL r1 r2 skip)) => //.
by rewrite seq_skip_r.
Qed.

(* -------------------------------------------------------------------- *)
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
apply: ispartialcoupling_dlet; first exact hC.
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
  apply/ispartialcoupling_dlim=> [n|n k le_nk]; last first.
  * move=> m'; rewrite -[k](subnK le_nk); elim: (_ - _)%N => //.
    by move=> n' ihn'; rewrite addSn; apply/(le_trans ihn').
  under eq_in_dlet => [i _|] do [rewrite !whilen_iterc !ssemE|].
  under [\dlet_(x <- ssem r2 m.2) _]eq_in_dlet => [i _|] do [rewrite !whilen_iterc !ssemE|].
  rewrite -!dlet_dlet.
  apply/(@ispartialcoupling_dlet _ _ _ _ _ _ (ssem r1) (ssem r2)) => /=; last first.
  * move=> m' Im'.
    rewrite -!ssem_seqE.
    move: Hdisj1 Hdisj2=> /(disjoint_cond abort skip) -> /(disjoint_cond abort skip) ->.
    rewrite !seq_skip_r !seq_abort_r !ssemE.
		move/rg_νn/hs: Im'.
    rewrite !ssemE => /eqP <-; case: ifPn => _.
    - by apply/ispartialcoupling_dnull.
    - by case: m' => a b; apply/ispartialcoupling_dunit.
  elim: n => /= [|n ihn].
  * rewrite !iterc0 -!ssem_seqE !seq_skip_r.
    by case: {+}m => a b; apply/ispartialcoupling_dunit.
  under eq_in_dlet => [i _|] do [rewrite itercSr !ssemE |].
  under [\dlet_(x <- ssem r2 _) _]eq_in_dlet => [i _|] do [rewrite itercSr !ssemE |].
  rewrite -!dlet_dlet.
  apply/(@ispartialcoupling_dlet _ _ _ _ _ _ (ssem r1) (ssem r2))=> //= m' /rg_νn Im'; move/hs: (Im').
  rewrite !ssemE => /eqP eqe.
  rewrite -!ssem_seqE.
    move: Hdisj1 Hdisj2=> /(disjoint_cond c1 skip) -> /(disjoint_cond c2 skip) ->.
  rewrite -eqe /ν1.
  case: {-}_ / idP => /= [p|]; first case/and3P: {+}p.
  * by rewrite !ssemE => _ -> _; case: dprhlw.
  rewrite !ssemE -eqe Im' /= andbb => /negP/negbTE => ->/=.
  rewrite -!ssem_seqE !seq_skip_r.
  by case: {+}m' => a b; apply/ispartialcoupling_dunit.  
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
apply: (dprhl_sem _ _ _ _ _ _ (dprhl_seq Htop Hbot)) => //.
by rewrite seq_skip_l.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_seqL2 P r1 r2 c1 c2 R t1 t2 c1' s1 s2 Q:
  dprhl P r1 r2 c1 c2 t1 t2 R
  -> dprhl R t1 t2 c1' skip s1 s2 Q
  -> dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q.
Proof.
move=> Htop Hbot.
apply: (dprhl_sem _ _ _ _ _ _ (dprhl_seq Htop Hbot)) => //.
by rewrite seq_skip_r.
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
Lemma dprhl_gendelayL P r1 r2 c1 s1 Q:
  dprhl P r1 skip c1 skip s1 skip Q
  -> dprhl P r1 r2 c1 skip s1 r2 Q.
Proof.
move=> h m /h [v [hL hR] rg]; exists v; last exact: rg.
split=> //; move: hR; rewrite !seq_skip_r.
under eq_in_dlet => [x _|] do [rewrite ssem_skipE|].
by rewrite dlet_dunit_id => ->; rewrite ssem_skipE dlet_unit.
Qed.

(* -------------------------------------------------------------------- *)
(* Approximants of a one-sided loop coupling: [cwhilen f n m] iterates   *)
(* the one-step coupling [f] n times starting from [m], and              *)
(* [cwhilee e f n m] keeps only the states that have already left the    *)
(* loop guarded by [e].                                                  *)
Fixpoint cwhilen (f : rmem -> Distr rmem) n m :=
  if n is n.+1 then \dlet_(w <- cwhilen f n m) f w else dunit m.

Definition cwhilee (e : expr bool) f n m :=
  \dlet_(u <- cwhilen f n m) (if `[{ e }] u.1 then dnull else dunit u).

(* -------------------------------------------------------------------- *)
(* The common core of the one-sided while rules.  Everything here is     *)
(* independent of *why* the loop terminates: from one step [ν1] of the   *)
(* coupling, the limit of the [cwhilee] approximants is a partial        *)
(* coupling for the whole loop as soon as the mass still running the     *)
(* loop after [n] steps can be made arbitrarily small.  The three rules  *)
(* below differ only in how they bound that mass.                        *)
Section WhileLCore.
Context (I : rassn) (e1 : expr bool) (c1 r1 r2 : cmd)
        (ν1 : rmem -> Distr rmem).

Local Notation νn := (cwhilen ν1).
Local Notation νe := (cwhilee e1 ν1).

Hypothesis Hdisj : [disjoint (write r1) & (fv e1)].
Hypothesis ν1_id : forall w, ~~ `[{ e1 }] w.1 -> ν1 w = dunit w.
Hypothesis ν1_rg : forall w, I w -> range I (ν1 w).
Hypothesis ν1_L  : forall w, I w ->
  \dlet_(u <- ν1 w) ssem r1 u.1 = ssem (r1 ;; IfT e1 then c1) w.1.
Hypothesis ν1_R  : forall w,
  \dlet_(u <- ν1 w) ssem r2 u.2 = ssem r2 w.2.

(* -- the invariant is preserved all along the iteration -- *)
Lemma cwhilen_rg m : I m -> forall n, range I (νn n m).
Proof using ν1_rg.
by move=> Im; elim=> [|n ih] /=; [apply/range_dunit | apply/(range_dlet ih)].
Qed.

Lemma cwhilee_rg m : I m -> forall n, range (I /\ `[{ ~~ e1#'1 }])%A (νe n m).
Proof using ν1_rg.
move=> Im n u /dinsupp_dlet [w hw] /=; case: (boolP (`[{ e1 }] w.1)) => he.
- by rewrite dnullE eqxx.
move=> /in_dunit eq; rewrite eq.
by apply/andP; split; [exact: (cwhilen_rg Im hw) | rewrite /= ssemE].
Qed.

(* -- the two marginals of the finite approximants -- *)
Lemma cwhilen_L m : I m -> forall n,
    \dlet_(u <- νn n m) ssem r1 u.1
  = \dlet_(w <- ssem r1 m.1) ssem (iterc n (IfT e1 then c1)) w.
Proof using ν1_L ν1_rg.
move=> Im; elim=> [|n ih] /=.
- rewrite dlet_unit iterc0.
  by under eq_in_dlet => [w _|] do [rewrite ssem_skipE|]; rewrite dlet_dunit_id.
rewrite dlet_dlet.
transitivity (\dlet_(u <- νn n m) ssem (r1 ;; IfT e1 then c1) u.1).
- by apply/eq_in_dlet => // u /(cwhilen_rg Im) Iu; apply/ν1_L.
under eq_in_dlet => [u _|] do [rewrite ssem_seqE|].
rewrite -dlet_dlet ih dlet_dlet.
apply/eq_in_dlet => // y _.
by rewrite (itercSr n (IfT e1 then c1) y) ssem_seqE.
Qed.

Lemma cwhilen_R m : forall n, \dlet_(u <- νn n m) ssem r2 u.2 = ssem r2 m.2.
Proof using ν1_R.
elim=> [|n ih] /=; first by rewrite dlet_unit.
rewrite dlet_dlet.
by under eq_in_dlet => [u _|] do [rewrite ν1_R|]; rewrite ih.
Qed.

Lemma cwhilee_L m : I m -> forall n,
    \dlet_(u <- νe n m) ssem r1 u.1
  = \dlet_(w <- ssem r1 m.1) ssem (whilen e1 c1 n.+1) w.
Proof using Hdisj ν1_L ν1_rg.
move=> Im n; rewrite /cwhilee dlet_dlet.
transitivity (\dlet_(u <- νn n m) ssem (r1 ;; IfT e1 then abort) u.1).
- apply/eq_in_dlet => // u _; rewrite (disjoint_cond abort skip Hdisj).
  case: ifPn => he; last by rewrite dlet_unit seq_skip_r.
  by rewrite dlet_null seq_abort_r ssem_abortE.
under eq_in_dlet => [u _|] do [rewrite ssem_seqE|].
rewrite -dlet_dlet (cwhilen_L Im) dlet_dlet.
apply/eq_in_dlet => // w _.
by rewrite (whilen_iterc n e1 c1 w) ssem_seqE.
Qed.

(* -- the cut-off couplings increase, and stay below the uncut ones -- *)
Lemma le_cwhilee m : forall n, νe n m <=1 νn n m.
Proof using Type.
move=> n u; rewrite /cwhilee.
apply/(@le_trans _ _ ((\dlet_(w <- νn n m) dunit w) u)); last first.
- by rewrite dlet_dunit_id.
apply: (le_in_dlet _ u) => w _ u'.
by case: ifPn => // _; rewrite dnullE ge0_mu.
Qed.

Lemma mono_cwhilee m : forall n k, (n <= k)%N -> νe n m <=1 νe k m.
Proof using ν1_id.
have le1: forall j, νe j m <=1 νe j.+1 m.
+ move=> j; rewrite /cwhilee /= dlet_dlet.
  apply/le_in_dlet => w _ u; case: (boolP (`[{ e1 }] w.1)) => he.
  - by rewrite dnullE ge0_mu.
  by rewrite (ν1_id he) dlet_unit (negbTE he).
move=> n k le_nk u; rewrite -(subnK le_nk).
elim: (k - n)%N => [|j ih]; first by rewrite add0n.
by rewrite addSn; apply/(le_trans ih)/le1.
Qed.

(* -- the left marginal of the limit is the loop itself -- *)
Lemma cwhilee_limL m : I m ->
  \dlet_(u <- \dlim_(n) νe n m) ssem r1 u.1 = ssem (r1 ;; While e1 Do c1) m.1.
Proof using Hdisj ν1_L ν1_id ν1_rg.
move=> Im; rewrite (dlet_lim _ (@mono_cwhilee m)).
transitivity (\dlim_(n) \dlet_(w <- ssem r1 m.1) ssem (whilen e1 c1 n.+1) w).
- by apply/eq_dlim => n; rewrite (cwhilee_L Im).
transitivity (\dlim_(n) \dlet_(w <- ssem r1 m.1) ssem (whilen e1 c1 n) w).
- by apply/distr_eqP/dlim_bump.
have mono_wn: forall x n k, (n <= k)%N ->
    ssem (whilen e1 c1 n) x <=1 ssem (whilen e1 c1 k) x.
+ by move=> x n k le_nk; apply/homo_whilen.
rewrite (dlim_let _ mono_wn) ssem_seqE.
by apply/eq_in_dlet => // w _; rewrite ssem_whileE.
Qed.

(* -------------------------------------------------------------------- *)
(* Once the mass still running the loop after [n] steps can be made      *)
(* arbitrarily small, the limit coupling is total on the right.          *)
Lemma whileL_core m :
     I m
  -> (forall eps : R, 0 < eps ->
        exists n, \P_[νn n m] [pred u : rmem | `[{ e1 }] u.1] <= eps)
  -> exists2 ν,
         ispartialcoupling (ssem (r1 ;; While e1 Do c1) m.1)
           (ssem (r2 ;; skip) m.2) (ssem r1) (ssem r2) ν
       & range (I /\ `[{ ~~ e1#'1 }])%A ν.
Proof using All.
move=> Im small_a; pose a n := \P_[νn n m] [pred u : rmem | `[{ e1 }] u.1].
exists (\dlim_(n) νe n m); last by apply/range_dlim => n; apply/(cwhilee_rg Im).
split; first by rewrite dlet_dmargin (cwhilee_limL Im).
rewrite dlet_dmargin seq_skip_r.
have leA: \dlet_(u <- \dlim_(n) νe n m) ssem r2 u.2 <=1 ssem r2 m.2.
+ rewrite (dlet_lim _ (@mono_cwhilee m)); apply/leub_dlim => n.
  by rewrite -(cwhilen_R m n); apply/le_mu_dlet/(@le_cwhilee m).
apply/(le_dweight_eq leA); apply/eqP; rewrite eq_le.
apply/andP; split; first by apply/le_mu_pr => x _ _; apply/leA.
(* -- the deficit of the [n]-th approximant is bounded by [a n] -- *)
have leAn: forall n, dweight (ssem r2 m.2)
    <= dweight (\dlet_(u <- \dlim_(n) νe n m) ssem r2 u.2) + a n.
+ move=> n.
  have leAe: dweight (\dlet_(u <- νe n m) ssem r2 u.2)
          <= dweight (\dlet_(u <- \dlim_(n) νe n m) ssem r2 u.2).
  - apply/le_mu_pr => x _ _; apply/le_mu_dlet => u.
    by apply/(dlim_ub n (@mono_cwhilee m)).
  apply/(le_trans _ (lerD leAe (lexx (a n)))).
  have hAe: \dlet_(u <- νe n m) ssem r2 u.2
      = \dlet_(u <- νn n m) (if `[{ e1 }] u.1 then dnull else ssem r2 u.2).
  - rewrite /cwhilee dlet_dlet; apply/eq_in_dlet => // u _.
    by case: ifPn => he; rewrite ?dlet_null ?dlet_unit.
  have ge0f: forall u : rmem,
      0 <= \P_[if `[{ e1 }] u.1 then dnull else ssem r2 u.2] predT.
  - by move=> u; apply/ge0_pr.
  have le1f: forall u : rmem,
      \P_[if `[{ e1 }] u.1 then dnull else ssem r2 u.2] predT <= 1.
  - by move=> u; apply/le1_pr.
  have ge0k: forall u : rmem, 0 <= ((`[{ e1 }] u.1 : nat))%:R :> R.
  - by move=> u; apply/ler0n.
  have hasf: \E?_[νn n m]
      (fun u => \P_[if `[{ e1 }] u.1 then dnull else ssem r2 u.2] predT).
  - by apply/bounded_has_exp; exists 1 => u; rewrite ger0_norm ?ge0f ?le1f.
  have hask := has_exp_natb (νn n m) [pred u : rmem | `[{ e1 }] u.1].
  have hEf: dweight (\dlet_(u <- νe n m) ssem r2 u.2)
    = \E_[νn n m]
        (fun u => \P_[if `[{ e1 }] u.1 then dnull else ssem r2 u.2] predT).
  - by rewrite hAe pr_dlet.
  have hEk: a n = \E_[νn n m] (fun u : rmem => ((`[{ e1 }] u.1 : nat))%:R).
  - by rewrite /a pr_exp.
  have hEg: dweight (ssem r2 m.2)
    = \E_[νn n m] (fun u : rmem => \P_[ssem r2 u.2] predT).
  - by rewrite -(cwhilen_R m n) pr_dlet.
  rewrite hEf hEk hEg -(expD ge0f ge0k hasf hask).
  apply/le_exp.
  - by apply/bounded_has_exp; exists 1 => u; rewrite ger0_norm ?ge0_pr ?le1_pr.
  - apply/bounded_has_exp; exists (1 + 1) => u.
    by rewrite ger0_norm ?addr_ge0 ?ge0f ?ge0k // lerD ?le1f ?le1_natb.
  move=> u /=; case: (boolP (`[{ e1 }] u.1)) => he.
  - by rewrite pr_dnull mulr1n add0r le1_pr.
  by rewrite mulr0n addr0.
(* -- ... hence the deficit vanishes in the limit -- *)
rewrite leNgt; apply/negP => hlt.
pose d := dweight (ssem r2 m.2)
  - dweight (\dlet_(u <- \dlim_(n) νe n m) ssem r2 u.2).
have gt0d: 0 < d by rewrite subr_gt0.
have gt0d2: 0 < d / 2%:R by rewrite divr_gt0 ?ltr0n.
case: (small_a _ gt0d2) => n hn; move: (leAn n); rewrite leNgt => /negP; apply.
apply/(le_lt_trans (lerD (lexx _) hn)).
have ->: dweight (ssem r2 m.2)
       = dweight (\dlet_(u <- \dlim_(n) νe n m) ssem r2 u.2) + d.
+ by rewrite /d addrCA subrr addr0.
rewrite ltrD2l ltr_pdivrMr ?ltr0n // -[X in X < _]mulr1 ltr_pM2l //.
by rewrite ltr1n.
Qed.

(* -------------------------------------------------------------------- *)
(* Losslessness of the left program is one way of making that mass       *)
(* vanish.                                                               *)
Lemma whileL_ll m :
     I m
  -> dweight (ssem (r1 ;; While e1 Do c1) m.1) = 1
  -> forall eps : R, 0 < eps ->
       exists n, \P_[νn n m] [pred u : rmem | `[{ e1 }] u.1] <= eps.
Proof using All.
move=> Im Hll.
have wν: dweight (\dlim_(n) νe n m) = 1.
+ apply/eqP; rewrite eq_le le1_pr /=.
  by rewrite -Hll -(cwhilee_limL Im); apply/dweight_dlet.
have wge: forall n, dweight (νe n m)
  = dweight (νn n m) - \P_[νn n m] [pred u : rmem | `[{ e1 }] u.1].
+ move=> n; rewrite /cwhilee pr_dlet -pr_predC pr_exp.
  apply/eq_exp => u /=; case: (boolP (`[{ e1 }] u.1)) => he.
  - by rewrite pr_dnull mulr0n.
  by rewrite pr_dunit.
move=> eps gt0eps; case: (dweight_dlim (@mono_cwhilee m) gt0eps) => n hn.
exists n; have ->: \P_[νn n m] [pred u : rmem | `[{ e1 }] u.1]
                 = dweight (νn n m) - dweight (νe n m).
- by rewrite wge opprB addrCA subrr addr0.
apply/(@le_trans _ _ (1 - dweight (νe n m))).
- by rewrite lerD2r le1_pr.
by move: hn; rewrite wν lerBlDr addrC -lerBlDr.
Qed.

End WhileLCore.

(* -------------------------------------------------------------------- *)
(* One-sided while rule, with a variant bounding the number of           *)
(* iterations.  Termination being bounded, no losslessness side          *)
(* condition is needed.                                                  *)
Lemma dprhl_whileL_var I (v : expr nat) (e1 : expr bool) c1 r1 r2:
  [disjoint (write r1) & (fv e1)]
  -> (forall m : rmem, I m -> `[{ e1 }] m.1 -> (0 < `[{ v }] m.1)%N)
  -> (forall n : nat,
       dprhl (I /\ `[{ e1#'1 }] /\ [pred u : rmem | `[{ v }] u.1 == n])%A
         r1 r2 c1 skip r1 r2
         (I /\ [pred u : rmem | (`[{ v }] u.1 < n)%N])%A)
  ->
  dprhl
    I
      r1 r2
      (While e1 Do c1)
      skip
      r1 r2
    (I /\ `[{ ~~ e1#'1 }])%A.
Proof.
move=> Hdisj hvar h.
pose ν1 (w : rmem) :=
  if @idP ((I /\ `[{ e1#'1 }] /\ [pred u : rmem | `[{ v }] u.1 == `[{ v }] w.1])%A w)
  is ReflectT Rw then tag (dprhlw (h (`[{ v }] w.1)) Rw) else dunit w.
(* -- one step of the iteration -- *)
have ν1_J: forall w, I w -> `[{ e1 }] w.1 ->
    (I /\ `[{ e1#'1 }] /\ [pred u : rmem | `[{ v }] u.1 == `[{ v }] w.1])%A w.
+ move=> w Iw he; rewrite /=; apply/and3P; split; rewrite ?ssemE ?eqxx //.
have ν1_id: forall w, ~~ `[{ e1 }] w.1 -> ν1 w = dunit w.
+ move=> w he; rewrite /ν1; case: {-}_ / idP => // p.
  by case/and3P: {+}p => _; rewrite ssemE (negbTE he).
have ν1_dec: forall w, I w -> `[{ e1 }] w.1 ->
    range (I /\ [pred u : rmem | (`[{ v }] u.1 < `[{ v }] w.1)%N])%A (ν1 w).
+ move=> w Iw he; rewrite /ν1; case: {-}_ / idP => [p|]; first by case: dprhlw.
  by move=> /(_ (ν1_J _ Iw he)) [].
have ν1_rg: forall w, I w -> range I (ν1 w).
+ move=> w Iw; case: (boolP (`[{ e1 }] w.1)) => he; last first.
  - by rewrite (ν1_id _ he); apply/range_dunit.
  by apply/(range_weaken _ (ν1_dec _ Iw he)) => u /andP [].
have ν1_L: forall w, I w ->
    \dlet_(u <- ν1 w) ssem r1 u.1 = ssem (r1 ;; IfT e1 then c1) w.1.
+ move=> w Iw; rewrite /ν1; case: {-}_ / idP => [p|hn]; last first.
  - have he: ~~ `[{ e1 }] w.1 by apply/negP => he; apply/hn/ν1_J.
    by rewrite dlet_unit (disjoint_cond c1 skip Hdisj) (negbTE he) seq_skip_r.
  case/and3P: {+}p => _ he _; rewrite ssemE in he.
  rewrite (disjoint_cond c1 skip Hdisj) he.
  case: dprhlw => x cpl rg.
  transitivity (\dlet_(u <- x) ssem r1 u.1); first by [].
  by rewrite -(proj1 cpl) dlet_dmargin.
have ν1_R: forall w, \dlet_(u <- ν1 w) ssem r2 u.2 = ssem r2 w.2.
+ move=> w; rewrite /ν1; case: {-}_ / idP => [p|_]; last by rewrite dlet_unit.
  case: dprhlw => x cpl rg.
  transitivity (\dlet_(u <- x) ssem r2 u.2); first by [].
  have hr := proj2 cpl; rewrite seq_skip_r in hr.
  by rewrite -hr dlet_dmargin.
move=> m Im; apply: (whileL_core Hdisj ν1_id ν1_rg ν1_L ν1_R Im).
(* -- the variant bounds the number of iterations -- *)
have rg: forall n, range
    (I /\ [pred u : rmem | (`[{ v }] u.1 + n <= `[{ v }] m.1)%N || ~~ `[{ e1 }] u.1])%A
    (cwhilen ν1 n m).
+ elim=> [|n ih] /=.
  - by apply/range_dunit; apply/andP; split; rewrite //= addn0 leqnn.
  apply/(range_dlet ih) => w /andP [Iw]; rewrite /= => hw.
  case: (boolP (`[{ e1 }] w.1)) => he; last first.
  - rewrite (ν1_id _ he); apply/range_dunit; apply/andP; split=> //=.
    by rewrite he orbT.
  apply/(range_weaken _ (ν1_dec _ Iw he)) => u /andP [Iu]; rewrite /= => hu.
  apply/andP; split=> //=; apply/orP; left.
  case/orP: hw => [hw|]; last by rewrite he.
  by rewrite addnS -addSn; apply/(leq_trans _ hw); rewrite leq_add2r.
(* -- so after [`[{ v }] m.1] steps no mass is left in the loop -- *)
move=> eps gt0eps; exists (`[{ v }] m.1); rewrite eq0_pr ?ltW //.
move=> u /(rg (`[{ v }] m.1)) /andP [Iu]; rewrite !inE /= => hu.
case/orP: hu => [|//]; rewrite -{2}[`[{ v }] m.1]add0n leq_add2r leqn0 => /eqP h0.
by apply/negP => he; move: (hvar _ Iu he); rewrite h0.
Qed.

(* -------------------------------------------------------------------- *)

(* One-sided while rule.  The left-hand side, delayed prefix included,   *)
(* must be lossless on the invariant; nothing is asked of the right.     *)
(* The delayed right-hand side [r2] is arbitrary: the body only has to   *)
(* reproduce its distribution, which the limit coupling then inherits    *)
(* since the leftover mass vanishes with the left losslessness.          *)
Lemma dprhl_whileL I (e1 : expr bool) c1 r1 r2:
  [disjoint (write r1) & (fv e1)]
  -> (forall m : rmem, I m -> dweight (ssem (r1 ;; While e1 Do c1) m.1) = 1)
  -> dprhl (I /\ `[{ e1#'1 }])%A r1 r2 c1 skip r1 r2 I
  ->
  dprhl
    I
      r1 r2
      (While e1 Do c1)
      skip
      r1 r2
    (I /\ `[{ ~~ e1#'1 }])%A.
Proof.
move=> Hdisj Hll h.
pose ν1 (w : rmem) :=
  if @idP ((I /\ `[{ e1#'1 }])%A w) is ReflectT Rw then tag (dprhlw h Rw) else dunit w.
(* -- one step of the iteration -- *)
have ν1_J: forall w, I w -> `[{ e1 }] w.1 -> (I /\ `[{ e1#'1 }])%A w.
+ by move=> w Iw he; rewrite /=; apply/andP; split; rewrite ?ssemE.
have ν1_id: forall w, ~~ `[{ e1 }] w.1 -> ν1 w = dunit w.
+ move=> w he; rewrite /ν1; case: {-}_ / idP => // p.
  by case/andP: {+}p => _; rewrite ssemE (negbTE he).
have ν1_rg: forall w, I w -> range I (ν1 w).
+ move=> w Iw; case: (boolP (`[{ e1 }] w.1)) => he; last first.
  - by rewrite (ν1_id _ he); apply/range_dunit.
  rewrite /ν1; case: {-}_ / idP => [p|]; first by case: dprhlw.
  by move=> /(_ (ν1_J _ Iw he)) [].
have ν1_L: forall w, I w ->
    \dlet_(u <- ν1 w) ssem r1 u.1 = ssem (r1 ;; IfT e1 then c1) w.1.
+ move=> w Iw; rewrite /ν1; case: {-}_ / idP => [p|hn]; last first.
  - have he: ~~ `[{ e1 }] w.1 by apply/negP => he; apply/hn/ν1_J.
    by rewrite dlet_unit (disjoint_cond c1 skip Hdisj) (negbTE he) seq_skip_r.
  case/andP: {+}p => _ he; rewrite ssemE in he.
  rewrite (disjoint_cond c1 skip Hdisj) he.
  case: dprhlw => v cpl rg.
  transitivity (\dlet_(u <- v) ssem r1 u.1); first by [].
  by rewrite -(proj1 cpl) dlet_dmargin.
have ν1_R: forall w, \dlet_(u <- ν1 w) ssem r2 u.2 = ssem r2 w.2.
+ move=> w; rewrite /ν1; case: {-}_ / idP => [p|_]; last by rewrite dlet_unit.
  case: dprhlw => v cpl rg.
  transitivity (\dlet_(u <- v) ssem r2 u.2); first by [].
  have hr := proj2 cpl; rewrite seq_skip_r in hr.
  by rewrite -hr dlet_dmargin.
move=> m Im; apply: (whileL_core Hdisj ν1_id ν1_rg ν1_L ν1_R Im).
by apply: (whileL_ll Hdisj ν1_id ν1_rg ν1_L ν1_R Im); apply/Hll.
Qed.

(* -------------------------------------------------------------------- *)
(* ... and the same rule, for a body proved against a [skip] delayed     *)
(* right-hand side.                                                      *)
Lemma dprhl_whileL_gen I (e1 : expr bool) c1 r1 r2:
  [disjoint (write r1) & (fv e1)]
  -> (forall m : rmem, I m -> dweight (ssem (r1 ;; While e1 Do c1) m.1) = 1)
  -> dprhl (I /\ `[{ e1#'1 }])%A r1 skip c1 skip r1 skip I
  ->
  dprhl
    I
      r1 r2
      (While e1 Do c1)
      skip
      r1 r2
    (I /\ `[{ ~~ e1#'1 }])%A.
Proof. by move=> h1 h2 h; apply/(dprhl_whileL h1 h2)/dprhl_gendelayL. Qed.

(* -------------------------------------------------------------------- *)
(* One-sided while rule with a probabilistic variant: the body need only *)
(* decrease the variant with probability at least [p], which is a pHL    *)
(* side condition on the left-hand program.  As for [dprhl_whileL], the  *)
(* delayed right-hand side [r2] is arbitrary; the mass left in the loop  *)
(* after [n] steps is bounded through the variant, and vanishes.         *)
Lemma dprhl_whileL_phl I (J : assn) (v : expr nat) (e1 : expr bool) c1 r1 r2
    (p : R):
  [disjoint (write r1) & (fv e1)]
  -> [disjoint (write r1) & (fv v)]
  -> 0 < p
  -> (forall m : rmem, I m -> J m.1)
  -> (forall m : rmem, I m -> `[{ e1 }] m.1 -> (0 < `[{ v }] m.1)%N)
  -> (forall k : nat,
        phl (J /\ `[{ e1 }] /\ [pred m1 | `[{ v }] m1 == k])%A
          (r1 ;; c1) [pred m1 | (`[{ v }] m1 < k)%N] '>= p)
  -> (forall k : nat,
        dprhl (I /\ `[{ e1#'1 }] /\ [pred u : rmem | `[{ v }] u.1 == k])%A
          r1 r2 c1 skip r1 r2
          (I /\ [pred u : rmem | (`[{ v }] u.1 <= k)%N])%A)
  ->
  dprhl
    I
      r1 r2
      (While e1 Do c1)
      skip
      r1 r2
    (I /\ `[{ ~~ e1#'1 }])%A.
Proof.
move=> Hdisj Hdisjv gt0p HJ hpos hpr h.
pose ν1 (w : rmem) :=
  if @idP ((I /\ `[{ e1#'1 }] /\
       [pred u : rmem | `[{ v }] u.1 == `[{ v }] w.1])%A w)
  is ReflectT Rw then tag (dprhlw (h (`[{ v }] w.1)) Rw) else dunit w.
(* -- one step of the iteration -- *)
have ν1_J: forall w, I w -> `[{ e1 }] w.1 ->
    (I /\ `[{ e1#'1 }] /\ [pred u : rmem | `[{ v }] u.1 == `[{ v }] w.1])%A w.
+ by move=> w Iw he; rewrite /=; apply/and3P; split; rewrite ?ssemE ?eqxx.
have ν1_id: forall w, ~~ `[{ e1 }] w.1 -> ν1 w = dunit w.
+ move=> w he; rewrite /ν1; case: {-}_ / idP => // q.
  by case/and3P: {+}q => _; rewrite ssemE (negbTE he).
have ν1_dec: forall w, I w -> `[{ e1 }] w.1 ->
    range (I /\ [pred u : rmem | (`[{ v }] u.1 <= `[{ v }] w.1)%N])%A (ν1 w).
+ move=> w Iw he; rewrite /ν1; case: {-}_ / idP => [q|]; first by case: dprhlw.
  by move=> /(_ (ν1_J _ Iw he)) [].
have ν1_rg: forall w, I w -> range I (ν1 w).
+ move=> w Iw; case: (boolP (`[{ e1 }] w.1)) => he; last first.
  - by rewrite (ν1_id _ he); apply/range_dunit.
  by apply/(range_weaken _ (ν1_dec _ Iw he)) => u /andP [].
have ν1_L: forall w, I w ->
    \dlet_(u <- ν1 w) ssem r1 u.1 = ssem (r1 ;; IfT e1 then c1) w.1.
+ move=> w Iw; rewrite /ν1; case: {-}_ / idP => [q|hn]; last first.
  - have he: ~~ `[{ e1 }] w.1 by apply/negP => he; apply/hn/ν1_J.
    by rewrite dlet_unit (disjoint_cond c1 skip Hdisj) (negbTE he) seq_skip_r.
  case/and3P: {+}q => _ he _; rewrite ssemE in he.
  rewrite (disjoint_cond c1 skip Hdisj) he.
  case: dprhlw => x cpl rg.
  transitivity (\dlet_(u <- x) ssem r1 u.1); first by [].
  by rewrite -(proj1 cpl) dlet_dmargin.
have ν1_R: forall w, \dlet_(u <- ν1 w) ssem r2 u.2 = ssem r2 w.2.
+ move=> w; rewrite /ν1; case: {-}_ / idP => [q|_]; last by rewrite dlet_unit.
  case: dprhlw => x cpl rg.
  transitivity (\dlet_(u <- x) ssem r2 u.2); first by [].
  have hr := proj2 cpl; rewrite seq_skip_r in hr.
  by rewrite -hr dlet_dmargin.
(* -- the probabilistic variant, transported to the coupling -- *)
have ν1_pr: forall w, I w -> `[{ e1 }] w.1 ->
    p <= \P_[ν1 w] [pred u : rmem | (`[{ v }] u.1 < `[{ v }] w.1)%N].
+ move=> w Iw he.
  have hLw: \dlet_(u <- ν1 w) ssem r1 u.1 = ssem (r1 ;; c1) w.1.
  + by rewrite (ν1_L _ Iw) (disjoint_cond c1 skip Hdisj) he.
  have Pw: (J /\ `[{ e1 }] /\
      [pred m1 : cmem | `[{ v }] m1 == `[{ v }] w.1])%A w.1.
  + apply/and3P; split; rewrite //= ?eqxx //.
    exact: (HJ _ Iw).
  apply/(le_trans (hpr _ _ Pw)); rewrite -hLw pr_dlet [X in _ <= X]pr_exp.
  apply/le_exp.
  + by apply/bounded_has_exp; exists 1 => u; rewrite ger0_norm ?ge0_pr ?le1_pr.
  + by apply/(has_exp_natb _ [pred u : rmem | (`[{ v }] u.1 < `[{ v }] w.1)%N]).
  move=> u /=; case: (boolP ((`[{ v }] u.1 < `[{ v }] w.1)%N)) => hu.
  + by rewrite mulr1n le1_pr.
  have ->: \P_[ssem r1 u.1] [pred m1 : cmem | (`[{ v }] m1 < `[{ v }] w.1)%N] = 0.
  + apply/eq0_pr => m' hm'; rewrite !inE /= -(disjoint_cmd Hdisjv hm').
    exact: hu.
  by rewrite mulr0n.
move=> m Im; apply: (whileL_core Hdisj ν1_id ν1_rg ν1_L ν1_R Im).
pose N := `[{ v }] m.1.
(* -- the invariant, together with the (global) bound on the variant -- *)
have rgIv: forall n,
    range (I /\ [pred u : rmem | (`[{ v }] u.1 <= N)%N])%A (cwhilen ν1 n m).
+ elim=> [|n ih] /=.
  - by apply/range_dunit; apply/andP; split=> //; rewrite /= /N leqnn.
  apply/(range_dlet ih) => w /andP [Iw lew].
  case: (boolP (`[{ e1 }] w.1)) => he; last first.
  - by rewrite (ν1_id _ he); apply/range_dunit; apply/andP; split.
  apply/(range_weaken _ (ν1_dec _ Iw he)) => u /andP [Iu leu].
  by apply/andP; split=> //=; apply/(leq_trans leu).
have rgI: forall n, range I (cwhilen ν1 n m).
+ by move=> n; apply/(range_weaken _ (rgIv n)) => u /andP [].
(* -- the potential argument: [Phi] decreases by [p] per unit of mass    *)
(* left in the loop, and is bounded, so that mass has to vanish -- *)
pose Phi (u : rmem) := (minn (`[{ v }] u.1) N)%:R : R.
pose a n := \P_[cwhilen ν1 n m] [pred u : rmem | `[{ e1 }] u.1].
pose E n := \E_[cwhilen ν1 n m] Phi.
have ge0Phi: forall u, 0 <= Phi u by move=> u; apply/ler0n.
have leNPhi: forall u, Phi u <= N%:R by move=> u; rewrite ler_nat geq_minr.
have hasPhi: forall mu : Distr rmem, \E?_[mu] Phi.
+ by move=> mu; apply/bounded_has_exp; exists N%:R => u; rewrite ger0_norm.
have PhiE: forall u, (`[{ v }] u.1 <= N)%N -> Phi u = (`[{ v }] u.1)%:R.
+ by move=> u leu; rewrite /Phi (minn_idPl leu).
have hascb: forall (mu : Distr rmem) (A : pred rmem) (c : R), 0 <= c ->
    \E?_[mu] (fun w => c * ((A w : nat))%:R).
+ move=> mu A c ge0c; apply/bounded_has_exp; exists c => w.
  rewrite normrM !ger0_norm ?ler0n //.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l ?le1_natb.
have step: forall n, E n.+1 + p * a n <= E n.
+ move=> n.
  have ge0A: forall u : rmem, 0 <= \E_[ν1 u] Phi by move=> u; apply/exp_ge0.
  have ge0B: forall u : rmem, 0 <= p * ((`[{ e1 }] u.1 : nat))%:R.
  + by move=> u; rewrite mulr_ge0 ?ler0n ?ltW.
  have hasA: \E?_[cwhilen ν1 n m] (fun u => \E_[ν1 u] Phi).
  + apply/bounded_has_exp; exists N%:R => u; rewrite ger0_norm ?ge0A //.
    by apply/exp_le_bd => // u'; rewrite ger0_norm ?ge0Phi ?leNPhi.
  have hasB := hascb (cwhilen ν1 n m) [pred u : rmem | `[{ e1 }] u.1] p (ltW gt0p).
  have hE1: E n.+1 = \E_[cwhilen ν1 n m] (fun u => \E_[ν1 u] Phi).
  + by rewrite /E /= (exp_dlet_bd _ _ ge0Phi leNPhi).
  have hE2: p * a n
    = \E_[cwhilen ν1 n m] (fun u => p * ((`[{ e1 }] u.1 : nat))%:R).
  + by rewrite /a pr_exp -expZ.
  rewrite hE1 hE2 -(expD ge0A ge0B hasA hasB).
  apply/le_exp_supp => //.
  + by move=> u; rewrite addr_ge0 ?ge0A ?ge0B.
  move=> u /(rgIv n) /andP [Iu leu].
  case: (boolP (`[{ e1 }] u.1)) => he; last first.
  + by rewrite (ν1_id _ he) exp_dunit mulr0n mulr0 addr0.
  have gt0k: (0 < `[{ v }] u.1)%N by apply/(hpos _ Iu he).
  have hk: (`[{ v }] u.1)%:R = ((`[{ v }] u.1).-1)%:R + 1 :> R.
  + by rewrite -mulrSr (ltn_predK gt0k).
  pose D := [pred w : rmem | (`[{ v }] w.1 < `[{ v }] u.1)%N].
  pose g (w : rmem) : R := ((`[{ v }] u.1).-1)%:R * ((D w : nat))%:R
                         + (`[{ v }] u.1)%:R * (((~~ D w) : nat))%:R.
  have ge0g1: forall w : rmem,
      (0 : R) <= ((`[{ v }] u.1).-1)%:R * ((D w : nat))%:R.
  + by move=> w; rewrite mulr_ge0 ?ler0n.
  have ge0g2: forall w : rmem,
      (0 : R) <= (`[{ v }] u.1)%:R * (((~~ D w) : nat))%:R.
  + by move=> w; rewrite mulr_ge0 ?ler0n.
  have hgE: \E_[ν1 u] g <= (`[{ v }] u.1)%:R - \P_[ν1 u] D.
  + have hsum: ((`[{ v }] u.1).-1)%:R * \P_[ν1 u] D
             + (`[{ v }] u.1)%:R * (1 - \P_[ν1 u] D)
             = (`[{ v }] u.1)%:R - \P_[ν1 u] D.
    - by rewrite hk mulrBr mulr1 mulrDl mul1r opprD addrA addrACA subrr add0r.
    rewrite /g (expD ge0g1 ge0g2 (hascb _ _ _ (ler0n _ _))
        (hascb _ _ _ (ler0n _ _))) !expZ -!pr_exp pr_predC -hsum.
    rewrite lerD2l; apply/ler_wpM2l; first by apply/ler0n.
    by rewrite lerD2r le1_pr.
  have hasg: \E?_[ν1 u] g.
  + apply/bounded_has_exp; exists ((`[{ v }] u.1)%:R) => w.
    have ge0gw: (0 : R) <= g w by rewrite /g addr_ge0 ?ge0g1 ?ge0g2.
    rewrite (ger0_norm ge0gw) /g; case: (boolP (D w)) => hD /=.
    + by rewrite mulr1n mulr0n mulr1 mulr0 addr0 ler_nat leq_pred.
    by rewrite mulr0n mulr1n mulr0 mulr1 add0r.
  have hle: \E_[ν1 u] Phi <= \E_[ν1 u] g.
  + apply/le_exp_supp => //.
    + by move=> w; rewrite addr_ge0 ?ge0g1 ?ge0g2.
    move=> w hw; case/andP: (ν1_dec _ Iu he _ hw) => Iw; rewrite /= => lek.
    rewrite /g /Phi /=; case: (boolP ((`[{ v }] w.1 < `[{ v }] u.1)%N)) => hD.
    + rewrite mulr1n mulr0n mulr1 mulr0 addr0.
      by rewrite ler_nat (leq_trans (geq_minl _ _)) // -ltnS (ltn_predK gt0k).
    rewrite mulr0n mulr1n mulr0 mulr1 add0r.
    by rewrite ler_nat (leq_trans (geq_minl _ _)).
  rewrite mulr1n mulr1 (PhiE _ leu).
  apply/(@le_trans _ _ (((`[{ v }] u.1)%:R - \P_[ν1 u] D) + p)).
  + by rewrite lerD2r; apply/(le_trans hle hgE).
  rewrite -[X in _ <= X]addr0 -addrA lerD2l addrC subr_le0.
  by apply/(ν1_pr _ Iu he).
have ge0E: forall n, 0 <= E n by move=> n; apply/exp_ge0.
have tel: forall n, p * (\sum_(i < n) a i) + E n <= N%:R.
+ elim=> [|n ih] /=.
  + rewrite big_ord0 mulr0 add0r /E /= exp_dunit /Phi ler_nat.
    by apply/geq_minr.
  rewrite big_ord_recr /= mulrDr -addrA.
  apply/(le_trans _ ih)/lerD => //.
  by rewrite addrC; apply/step.
have ge0a: forall n, 0 <= a n by move=> n; apply/ge0_pr.
have mono_a: forall n k, (n <= k)%N -> a k <= a n.
+ have le1: forall n, a n.+1 <= a n.
  + move=> n; rewrite /a /= pr_dlet [X in _ <= X]pr_exp.
    apply/le_exp_supp.
    + by move=> u; apply/ge0_pr.
    + by move=> u; apply/ler0n.
    + by apply/(has_exp_natb _ [pred u : rmem | `[{ e1 }] u.1]).
    move=> u /(rgI n) Iu /=; case: (boolP (`[{ e1 }] u.1)) => he.
    + by rewrite mulr1n le1_pr.
    by rewrite (ν1_id _ he) pr_dunit /= (negbTE he) mulr0n.
  move=> n k le_nk; rewrite -(subnK le_nk).
  elim: (k - n)%N => [|j ih]; first by rewrite add0n.
  by rewrite addSn; apply/(le_trans (le1 _)).
(* -- [n] steps cost at least [p * n * a n], so [a n] is O(1/n) -- *)
move=> eps gt0eps; pose n := (Num.bound (N%:R / (p * eps))).+1.
exists n; have gt0n: (0 < n%:R :> R) by rewrite ltr0n.
have gt0pe: 0 < p * eps by rewrite mulr_gt0.
have hb: N%:R / (p * eps) < n%:R.
+ apply/(lt_le_trans (archi_boundP _)); last by rewrite ler_nat leqnSn.
  by rewrite divr_ge0 ?ler0n ?ltW.
rewrite ltr_pdivrMr // in hb.
have hs: p * (n%:R * a n) <= N%:R.
+ apply/(le_trans _ (tel n)).
  apply/(@le_trans _ _ (p * (\sum_(i < n) a i) + 0)); last first.
  + by rewrite lerD2l; apply/ge0E.
  rewrite addr0 ler_pM2l //.
  apply/(@le_trans _ _ (\sum_(i < n) a n)); last first.
  + by apply: ler_sum => i _; apply/mono_a/ltnW/ltn_ord.
  by rewrite sumr_const card_ord mulr_natl.
apply/ltW; rewrite -(@ltr_pM2l _ (p * n%:R)) ?mulr_gt0 //.
rewrite -mulrA; apply/(le_lt_trans hs).
by rewrite -mulrA mulrCA.
Qed.

(* -------------------------------------------------------------------- *)
(* ... and the same rule, for a body proved against a [skip] delayed     *)
(* right-hand side.                                                      *)
Lemma dprhl_whileL_phl_gen I (J : assn) (v : expr nat) (e1 : expr bool)
    c1 r1 r2 (p : R):
  [disjoint (write r1) & (fv e1)]
  -> [disjoint (write r1) & (fv v)]
  -> 0 < p
  -> (forall m : rmem, I m -> J m.1)
  -> (forall m : rmem, I m -> `[{ e1 }] m.1 -> (0 < `[{ v }] m.1)%N)
  -> (forall k : nat,
        phl (J /\ `[{ e1 }] /\ [pred m1 | `[{ v }] m1 == k])%A
          (r1 ;; c1) [pred m1 | (`[{ v }] m1 < k)%N] '>= p)
  -> (forall k : nat,
        dprhl (I /\ `[{ e1#'1 }] /\ [pred u : rmem | `[{ v }] u.1 == k])%A
          r1 skip c1 skip r1 skip
          (I /\ [pred u : rmem | (`[{ v }] u.1 <= k)%N])%A)
  ->
  dprhl I r1 r2 (While e1 Do c1) skip r1 r2 (I /\ `[{ ~~ e1#'1 }])%A.
Proof.
move=> h1 h2 h3 h4 h5 h6 h7.
by apply/(dprhl_whileL_phl h1 h2 h3 h4 h5 h6) => k; apply/dprhl_gendelayL.
Qed.

(* -------------------------------------------------------------------- *)
(* Structural Rules *)
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
move=> H2 /= Hrng.
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
case Hin: (m' \in dinsupp v)=> //.
by move: (Hrng m' Hin) neq=> //= ->.
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
Lemma dprhl_case P A r1 r2 c1 c2 s1 s2 Q :
     dprhl (P /\   A)%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl (P /\ ~ A)%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl P r1 r2 c1 c2 s1 s2 Q.
Proof.
move=> hA hNA m Pm; case/boolP: (A m) => [Am | NAm].
+ by apply/hA; rewrite -(rwP andP).
+ by apply/hNA; rewrite -(rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_frame P r1 r2 c1 c2 s1 s2 Q R:
	[disjoint (rfv (rprp R)) & (rwrite ((r1 ;; c1 ;; s1)#'1)%S `|` rwrite ((r2 ;; c2 ;; s2)#'2)%S)]
	-> (forall m, Q m -> (exists m', m' \in dinsupp (ssem s1 m.1)) /\ (exists m', m' \in dinsupp (ssem s2 m.2)))
	-> dprhl P r1 r2 c1 c2 s1 s2 Q
	-> dprhl (P /\ R)%A r1 r2 c1 c2 s1 s2 (Q /\ R)%A.
Proof.
move=> Hd Hnz Hw m /= /andP [] HP HR.
case: (Hw m HP)=> v vcpl vrng.
exists v; first by [].
move=> m' m'supp /=.
apply /andP.
split; first by apply vrng.
have /Hnz [l r] := vrng m' m'supp.
case: l=> m1' s1supp.
case: r=> m2' s2supp.
have : m1' \in dinsupp (\dlet_(t <- dfst v) ssem s1 t).
+ rewrite dlet_dmargin.
  by apply (dlet_dinsupp m'supp).
have : m2' \in dinsupp (\dlet_(t <- dsnd v) ssem s2 t).
+ rewrite dlet_dmargin.
  by apply (dlet_dinsupp m'supp).
case: vcpl=> -> -> rc2supp rc1supp.
rewrite -esem_prpE.
rewrite (@disjoint_cmd _ _ _ (ircmd '1 s1) _ _ m' (m1', m'.2)).
+ rewrite disj_set_sym. 
	move: Hd.
	by rewrite //= !disjointUr => - [] [].
+ rewrite ssem_iE //=.
	apply (dlet_dinsupp s1supp).
  by rewrite dunit1E eq_refl oner_neq0.
rewrite (@disjoint_cmd _ _ _ (ircmd '2 s2) _ _ (m1', m'.2) (m1', m2')).
+ rewrite disj_set_sym. 
	move: Hd.
	by rewrite //= !disjointUr => - [] _ [] [].
+ rewrite ssem_iE //=.
	apply (dlet_dinsupp s2supp).
  by rewrite dunit1E eq_refl oner_neq0.
rewrite -(@disjoint_cmd _ _ _ (ircmd '1 (r1 ;; c1)) _ _ (m.1, m2') (m1', m2')).
+ rewrite disj_set_sym. 
	move: Hd.
  by rewrite //= !disjointUr => - [] [] [].
+ rewrite ssem_iE //=.
	apply (dlet_dinsupp rc1supp).
  by rewrite dunit1E eq_refl oner_neq0.
rewrite -(@disjoint_cmd _ _ _ (ircmd '2 (r2 ;; c2)) _ _ m (m.1, m2')) //.
+ rewrite disj_set_sym. 
	move: Hd.
  by rewrite //= !disjointUr => - [] _ [] [].
rewrite ssem_iE //=.
apply (dlet_dinsupp rc2supp).
by rewrite dunit1E eq_refl oner_neq0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_swap P c1 c2 Q r1 r2 s1 s2:
  dprhl P r2 r1 c2 c1 s2 s1 Q <-> dprhl (pswap P) r1 r2 c1 c2 s1 s2 (pswap Q).
Proof.
move: P Q c1 c2 r1 r2 s1 s2 => [:hG] P Q c1 c2 r1 r2 s1 s2; split; last first.
+ move: P Q c1 c2 r1 r2 s1 s2; abstract: hG => P Q c1 c2 r1 r2 s1 s2 h -[m1 m2] Pm.
  case: (h (m2, m1))=> //= ν [hC1 hC2] hR; exists (dswap ν) => /=.
  * by apply/ispartialcoupling_swap.
  * by move/range_pswap: hR; apply/range_weaken; case.
+ by move=> h; apply/hG ; apply/dprhl_conseq: h; case.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_exfalso c1 c2 r1 r2 s1 s2 Q : dprhl pred0 r1 r2 c1 c2 s1 s2 Q.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_abort P r1 r2 s1 s2 Q : dprhl P r1 r2 abort abort s1 s2 Q.
Proof.
move=> m _; exists dnull; last by apply/range_dnull.
by rewrite !seq_abort_r !ssemE; split; rewrite dmarginE !dlet_null.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dprhl_trans P12 P23 r1 r2 r3 c1 c2 c3 s1 s3 Q12 Q23:
	dprhl P12 r1 r2 c1 c2 s1 skip Q12
	-> dprhl P23 r2 r3 c2 c3 skip s3 Q23
	-> dprhl [pred m | `[<exists m', P12 (m.1, m') /\ P23 (m', m.2)>]] r1 r3 c1 c3 s1 s3 [pred m | `[<exists m', Q12 (m.1, m') /\ Q23 (m', m.2)>]].
Proof.
move=> H12 H23 [m1 m3] /= /asboolP [m2 [HP12 HP23]].
move: (H12 (m1, m2) HP12)=> [/= v12 [pc12l pc12r] rng12].
move: (H23 (m2, m3) HP23)=> [/= v23 [pc23l pc23r] rng23].
move: pc12r pc23l=> <- dletEq.
have eqr: dfst v23 = dsnd v12.
+ move: dletEq.
	under eq_in_dlet=> [x _|] do [rewrite ssem_skipE|].
	under [RHS]eq_in_dlet=> [x _|] do [rewrite ssem_skipE|].
	by rewrite !dlet_dunit_id.
exists (dmargin (fun v => (v.1.1, v.2)) (dglue Logic.eq_refl eqr)).
+ split.
	+ by rewrite -proj_glue1 pc12l.
	by rewrite -proj_glue2 pc23r.
move=> [m1' m3'] /=.
rewrite dmarginE.
move=> /dinsupp_dlet [] /= [] [] m1'' m2' m3'' /dinsuppPn.
rewrite dglueE dunit1E /=.
have [] := eqVneq (m1'', m3'') (m1', m3'); last by rewrite eq_refl.
rewrite pair_equal_spec=> - [] -> ->.
case: ifPn=> //.
move=> m2_supp /eqP H _.
apply /asboolP.
exists m2'.
split.
+ apply /rng12/dinsuppP/eqP.
	move: H.
	have [->|//]:= eqVneq (v12 (m1', m2')) 0.
	by rewrite !mul0r eq_refl.
apply /rng23/dinsuppP/eqP.
move: H.
have [->|//]:= eqVneq (v23 (m2', m3')) 0.
by rewrite mulr0 mul0r eq_refl.
Qed.
