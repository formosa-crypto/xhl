(* -------------------------------------------------------------------- *)

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
  | cond b _ _ => fv b
  | while b _ => fv b
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

End Variables.

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
  admit. (* Should be provable *)
+ move=> n m /mono H x.
  rewrite -!dmarginE.
  admit. (* Should be provable *)
by split; apply/eq_dlim => n; case: (hC n); rewrite -dmarginE.
Admitted.

End PreCouplingsTheory.

(* -------------------------------------------------------------------- *)
Implicit Types P Q R I : rassn.
Implicit Types c r s t : cmd.

(* -------------------------------------------------------------------- *)
Definition dprhl P r1 r2 c1 c2 s1 s2 Q :=
  forall m : rmem, P m ->
                   exists2 ν,
  isprecoupling
    (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2)
    (ssem s1) (ssem s2)
    ν
  & range Q ν.

Lemma dprhlw P r1 r2 c1 c2 s1 s2 Q m :
  dprhl P r1 r2 c1 c2 s1 s2 Q -> P m ->
    { ν | isprecoupling (ssem (r1 ;; c1) m.1) (ssem (r2 ;; c2) m.2) (ssem s1) (ssem s2) ν & range Q ν }.
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
Lemma dprhl_skip P r1 r2 Q:
  (forall m : rmem, P m -> Q m)
  -> dprhl P r1 r2 skip skip r1 r2 Q.
Proof.
move=> H1 m H2.
exists (dunit m).
+ by split; rewrite dmargin_dunit dlet_unit seq_skip_r.
by apply/range_dunit/H1/H2.
Qed.

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
  move=> /= m2 /(disjoint_cmd Hwrite) <-.
  admit. (* Need equality of memories *)
rewrite dlet_dmargin dlet_unit seq_skip_r.
by rewrite -/(mselect '2 _) mselect_mset.
Admitted.

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
Proof. set J := (I /\ _)%A => Hdisj1 Hdisj2 hs h.
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
(* Structural Rules *)

Lemma dprhl_pushL Q r1 r2 c1 c2:
  dprhl Q r1 r2 c1 c2 (r1 ;; c1) (r2 ;; c2) Q.
Proof.
move=> m Qm.
exists (dunit m).
+ by split; rewrite dmargin_dunit dlet_unit.
by apply: range_dunit.
Qed.

Lemma dprhl_popL P r1 r2 c1 c1' c2 s1 s2 Q:
  dprhl P r1 r2 (c1 ;; c1') c2 s1 s2 Q
  <->
  dprhl P (r1 ;; c1) r2 c1' c2 s1 s2 Q.
Proof.
by split; move=> H m {}/H; rewrite seqA.
Qed.

Lemma dprhl_case P A r1 r2 c1 c2 s1 s2 Q :
     dprhl (P /\   A)%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl (P /\ ~ A)%A r1 r2 c1 c2 s1 s2 Q
  -> dprhl P r1 r2 c1 c2 s1 s2 Q.
Proof.
move=> hA hNA m Pm; case/boolP: (A m) => [Am | NAm].
+ by apply/hA; rewrite -(rwP andP).
+ by apply/hNA; rewrite -(rwP andP).
Qed.
