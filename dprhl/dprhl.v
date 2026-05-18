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

Lemma seq_abort_r (c : cmd): (c ;; abort) =C abort.
Proof.
move=> m.
rewrite !semE.
apply distr_eqP=> v.
under eq_in_dlet=> [? _|] do [rewrite ssem_abortE|].
by rewrite dletC dnullE mulr0.
Qed.

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

Fixpoint fv {T : Type} (e : expr T) : set ident :=
  match e with
  | var_ T x => set1 (vname x)
  | cst_ _ _ => set0
  | prp_ p => [set x : ident | exists S m (v : vars S) y, (vname v = x) /\ p m <> p m.[v <- y]]
  | app_ _ _ l r => fv l `|` fv r
  end.

Fixpoint write (c : cmd) : set ident :=
  match c with
  | abort => set0
  | skip => set0
  | assign _ x _ => set1 (vname x)
  | random _ x _ => set1 (vname x)
  | cond _ c1 c2 => write c1 `|` write c2
  | while _ c => write c
  | seqc c1 c2 => write c1 `|` write c2
  end.

Fixpoint read (c : cmd) : set ident :=
  match c with
  | abort => set0
  | skip => set0
  | assign _ _ e => fv e
  | random _ _ d => fv d
  | cond b c1 c2 => fv b `|` read c1 `|` read c2
  | while b c1 => fv b `|` read c1
  | seqc c1 c2 => read c1 `|` (read c2 `\` write c1) 
  end.

Lemma disjoint_exp {T1 : Type} {T2 : IhbType.type} (e : expr T1) (x : vars T2):
  [disjoint [set (vname x)] & (fv e)]
  -> forall m u, `[{e}] m = `[{e}] m.[x <- u].
Proof.
elim e.
+ move=> T3 y /= dv m u.
  rewrite mget_neq; last by [].
  right.
  move: dv=> /(elimT disj_set2P).
  rewrite disjoints_subset.
  move=> /(_ (vname x)) /=.
  move=> /(_ (Logic.eq_refl _)).
  by rewrite contra.Internals.eqType_neqP.
+ by [].
+ move=> p /(elimT disj_set2P).
  rewrite disjoints_subset /=.
	rewrite sub1set in_setC notin_setE //=.
  move=> + m u.
  rewrite -forallNE=> /(_ (vtype x)).
  rewrite -forallNE=> /(_ m).
	rewrite -forallNE=> /(_ x).
	rewrite -forallNE=> /(_ u).
	rewrite not_andP /=.
	rewrite not_notE.
	rewrite -implyE.
	move=> /(_ Logic.eq_refl) ->.
	by [].
move=> T3 T4 e1 H1 e2 H2 /=.
move=> /(elimT disj_set2P) /disjoints_subset Hsubs m u.
rewrite -H2.
+ apply /(introT disj_set2P).
  rewrite disjoints_subset.
  move=> w /Hsubs.
  rewrite setCU.
  by case.
+ rewrite -H1.
  apply /(introT disj_set2P).
  rewrite disjoints_subset.
  move=> w /Hsubs.
  rewrite setCU.
  by case.
by [].
Qed.

Lemma disjoint_cmd {T : Type} (c : cmd) (e : expr T):
  [disjoint (write c) & (fv e)]
  -> forall (m m': cmem), m' \in dinsupp (ssem c m)
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
  move=> H m m'.
  rewrite ssem_assnE.
  move=> /in_dunit ->.
  exact /disjoint_exp/H.
+ move=> t. 
  move=> y e1.
  move=> H m m'.
  rewrite ssem_rndE.
  move=> /dinsupp_dlet [u] _.
  move=> /in_dunit ->.
  exact /disjoint_exp/H.
+ move=> e1 c0 Hl c1 Hr.
  move=> /(elimT disj_set2P) /disjoints_subset /= + m m'.
  rewrite subUset.
  move=> [Hsubl Hsubr].
  rewrite ssem_ifE.
  case (`[{e1}] m).
  + apply Hl.
    apply /(introT disj_set2P).
    rewrite disjoints_subset.
    by move=> w /Hsubl.
  + apply Hr.
    apply /(introT disj_set2P).
    rewrite disjoints_subset.
    by move=> w /Hsubr.
+ move=> e1 c0 IH.
  move=> /= Hdisj m m'.
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
  case (`[{e1}] m1).
  + move=> _ /dinsuppP.
    by rewrite dnullE.
  move=> + /in_dunit ->.
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
  by apply IH.
move=> c0 Hl c1 Hr.
move=> /(elimT disj_set2P) /disjoints_subset /= + m m'.
rewrite subUset.
move=> [Hsubl Hsubr].
rewrite ssem_seqE.
move=> /dinsupp_dlet [m1] /Hl m1v.
rewrite -in_dinsupp=> H.
have Hdisjl: [disjoint (write c0) & (fv e)].
+ apply /(introT disj_set2P).
  rewrite disjoints_subset.
  by move=> w /Hsubl.
have Hdisjr: [disjoint (write c1) & (fv e)].
+ apply /(introT disj_set2P).
  rewrite disjoints_subset.
  by move=> w /Hsubr.
move: (Hr Hdisjr m1 m' H)=> <-.
exact (m1v Hdisjl).
Qed.

Lemma disjoint_cond (c ct cf : cmd) (e : expr bool):
  [disjoint (write c) & (fv e)]
  -> forall m,
   ssem (c ;; (If e then ct else cf)) m = (if `[{e}] m then ssem (c ;; ct) m else ssem (c ;; cf) m).
Proof.
move=> Hdisj m.
rewrite !ssem_seqE.
case: ifPn=> He.
+ apply eq_in_dlet; last done.
  move=> m' /(disjoint_cmd Hdisj) eqe.
  by rewrite ssem_ifE -eqe He.
apply eq_in_dlet; last done.
move=> m' /(disjoint_cmd Hdisj) eqe.
by rewrite ssem_ifE -eqe (negbTE He).
Qed.

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

Lemma disjoint_set {T : IhbType.type} c (x : vars T) v:
	(vname x) \notin (read c `|` write c)
  -> forall m w, ssem c m w = ssem c m.[x <- v] w.[x <- v].
Proof.
elim c=> /=.
+ move=> _ m w.
  by rewrite !ssem_abortE !dnullE.
+ move=> _ m w.
  rewrite !ssem_skipE !dunit1E.
  admit. (* equality *)
+ move=> t v0 e H m w.
  rewrite !ssem_assnE !dunit1E.
  admit. (* x \notin fv e => `[{e}] m = `[{e}] m.[x <- v] 
					  x <> v0 => m.[x <- v][v0 <- `[{e}] m] = m.[v0 <- `[{e}] m][x <- v] *)
+ move=> t v0 d H m w.
  rewrite !ssem_rndE !dletE.
  apply eq_psum=> y.
  rewrite !dunit1E.
  admit. (* x \notin fv d => `[{d}] m = `[{d}] m.[x <- v] 
					  x <> v0 => m.[x <- v][v0 <- y] = m.[v0 <- y][x <- v] *)
+ move=> e c1 H1 c2 H2 H3 m w.
  rewrite !semE.
  have <-: `[{e}] m = `[{e}] m.[x <- v].
  + apply disjoint_exp.
    admit.
  case: ifPn=> _.
  + apply H1.
    admit.
  apply H2.
  admit.
+ move=> e c1 H1 H2 m w.
  rewrite !semE !dlimE.
  congr (constructive_ereal.fine (nlim _)).
  apply funext=> n.
  elim n.
  + move=> /=.
    by rewrite !ssem_abortE !dnullE.
  move=> p _.
  rewrite !(whilen_iterc _ _ _ _).
  move: m w.
  elim p.
  + move=> m w.
    rewrite iterc0.
    rewrite !(seq_skip_l _ _).
    rewrite !semE.
    have <-: `[{e}] m = `[{e}] m.[x <- v].
  	+ apply disjoint_exp.
    	admit.
		case: ifPn=> _.
  	+ by rewrite !dnullE.
    admit. (* eqaulity *)
  move=> q Iq m w.
  rewrite !ssem_seqE !(itercSl q _ _) -!ssem_seqE.
  rewrite -!(seqA _ _ _ _) ssem_seqE ssem_seqE.
  admit. (* fiddly *)
admit. (* fiddly *)
Admitted.

End Variables.


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
  (forall m : rmem, P m -> Q m)
  -> dprhl P r1 r2 skip skip r1 r2 Q.
Proof.
move=> H1 m H2.
exists (dunit m).
+ by split; rewrite dmargin_dunit dlet_unit seq_skip_r.
by apply/range_dunit/H1/H2.
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

Lemma dprhl_assignL {T : IhbType.type} Q r1 r'1 r2 (x : vars T) (e : expr T) :
  (forall m, ssem r'1 m = ssem r1 m.[x <- `[{ e }] m])
  -> [disjoint (write r'1) & (fv e)]
  -> dprhl [pred m : rmem | Q m.[~1 x <- `[{ e }] m.1]] r'1 r2 (x <<- e) skip r1 r2 Q.
Proof.
move=> Heq Hwrite.
move=> m /= Qmxe; exists (dunit (m.[~1 x <- `[{ e }] m.1])); last first.
+ by apply/range_dunit.
split.
+ rewrite dlet_dmargin dlet_unit.
  rewrite ssem_seqE.
  rewrite -/(mselect '1 _) mselect_mset /=.
  under eq_in_dlet => [? _|] do [rewrite ssem_assnE|].
  rewrite -Heq -{1}(dlet_dunit_id (ssem r'1 _)).
  apply eq_in_dlet; last done.
  move=> /= m2 /[dup] H /(disjoint_cmd Hwrite) <-.
  rewrite Heq in H.
  apply distr_eqP=> w.
  rewrite !dunit1E.
  suff {1}->: m2.[x <- `[{e}] m.1] = m2.
  + by [].
  apply mem_ext=> U.
  have := eqVneq T U.
  admit.
rewrite dlet_dmargin dlet_unit seq_skip_r.
by rewrite -/(mselect '2 _) mselect_mset.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma dprhl_rndL {t : IhbType.type} P (x : vars t) (d : dexpr t) r1 r2 Q :
  [disjoint (write r1) & ((vname x) |` (fv d))]
	->  (vname x) \notin (read r1)
	-> P =1 [pred m : rmem
       |  dweight (`[{ d }] m.1) == 1
       & `[< range [pred v | Q m.[~1 x <- v]] (`[{ d }] m.1) >]]
  -> dprhl P r1 r2 (x <$- d) skip r1 r2 Q.
Proof.
admit.
(* 
move=> PE -[m1 m2] /=; rewrite {}PE => /andP[/= /eqP wgt1] /asboolP hrg.
rewrite !ssemE; set μ := `[{ d }] m1.
pose ν := \dlet_(v <- μ) dunit (m1.[x <- v], m2); exists ν.
admit.
*)
Admitted.

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
have -> : v (w, m) = 0.
have := dinsuppPn v (w, m).
move=> /reflect_eq ->.
move: (q (w, m)).
admit.
admit.
Admitted.

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
(*
Lemma dprhl_frame P r1 r2 c1 c2 s1 s2 Q R:
	[disjoint (fv (rprp R)) & (write r1 `|` write r2 `|` write c1 `|` write c2)] 
	-> dprhl P r1 r2 c1 c2 s1 s2 Q
	-> dprhl (P /\ R)%A r1 r2 c1 c2 s1 s2 (Q /\ R)%A.
*)

(* -------------------------------------------------------------------- *)
Lemma dprhl_congr P r1 r2 c1 c2 s1 s2 t1 t2 Q:
	dprhl P r1 r2 c1 c2 s1 s2 Q
	-> dprhl P r1 r2 (c1 ;; t1) (c2 ;; t2) (s1 ;; t1) (s2 ;; t2) Q.
Proof.
move=> H m {}/H.
move=> [v [Hfst Hsnd] Hsupp].
exists v; last exact Hsupp.
split; rewrite -sem_seqA ssem_seqE. 
+ rewrite -Hfst dlet_dlet.
  by under eq_in_dlet => [? _ |] do [rewrite ssem_seqE|].
rewrite -Hsnd dlet_dlet.
by under eq_in_dlet => [? _ |] do [rewrite ssem_seqE|].
Qed.

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
