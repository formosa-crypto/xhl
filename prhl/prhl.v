(* -------------------------------------------------------------------- *)
From Stdlib             Require Import Setoid Morphisms.
From mathcomp           Require Import all_boot all_order all_algebra.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import boolp.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope sem_scope.
Local Open Scope mem_scope.

(* -------------------------------------------------------------------- *)
Section Couplings.
Context {A B : choiceType} (μ1 : Distr A) (μ2 : Distr B).

Definition iscoupling (ν : Distr (A * B)) :=
  dfst ν = μ1 /\ dsnd ν = μ2.
End Couplings.

(* -------------------------------------------------------------------- *)
Section CouplingsTheory.
Context {A B C D : choiceType}.

Lemma iscoupling_eq (μ1 μ2 μ1' μ2' : Distr _) (ν : Distr (A * B)) :
  μ1 =1 μ1' -> μ2 =1 μ2' -> iscoupling μ1 μ2 ν -> iscoupling μ1' μ2' ν.
Proof. by do 2! move=> /distr_eqP->. Qed.

Lemma iscoupling_prod (μ : Distr (A * B)) :
  iscoupling (dfst μ) (dsnd μ) μ.
Proof. by []. Qed.

Lemma iscoupling_dnull : @iscoupling A B dnull dnull dnull.
Proof. by split; rewrite dmarginE dlet_null. Qed.

Lemma iscoupling_dunit a b :
  @iscoupling A B (dunit a) (dunit b) (dunit (a, b)).
Proof. by split; rewrite dmarginE dlet_unit. Qed.

Lemma iscoupling_swap (μ1 μ2 : Distr A) (ν : Distr (A * A)) :
  iscoupling μ1 μ2 ν -> iscoupling μ2 μ1 (dswap ν).
Proof.
case=> <- <-; split; apply/distr_eqP => m;
  by rewrite (dfst_dswap, dsnd_dswap).
Qed.

Lemma iscoupling_dlet
  (μ1 μ2 : Distr _) (ν : Distr (A * B))
  (θ1 θ2 : _ -> Distr _) (ν' : _ -> Distr (C * D)) :

     iscoupling μ1 μ2 ν
  -> (forall x, x \in dinsupp ν ->
        iscoupling (θ1 x.1) (θ2 x.2) (ν' x))
  -> iscoupling
       (\dlet_(x <- μ1) (θ1 x))
       (\dlet_(x <- μ2) (θ2 x))
       (\dlet_(x <- ν ) (ν' x)).
Proof.
move=> [eq1 eq2] hC; split; rewrite !dmargin_dlet; subst μ1 μ2.
+ by rewrite dlet_dmargin; apply/eq_in_dlet => // x /hC [<- _].
+ by rewrite dlet_dmargin; apply/eq_in_dlet => // x /hC [_ <-].
Qed.

Lemma iscoupling_dlim
  (μ1 μ2 : nat -> Distr _) (ν : nat -> Distr (A * B)) :

     (forall n, iscoupling (μ1 n) (μ2 n) (ν n))
  -> (forall n m, (n <= m)%N -> ν n <=1 ν m)
  -> iscoupling (dlim μ1) (dlim μ2) (dlim ν).
Proof.
move=> hC mono; rewrite /iscoupling !dmarginE !dlet_lim //.
by split; apply/eq_dlim => n; case: (hC n).
Qed.
End CouplingsTheory.

(* -------------------------------------------------------------------- *)
Implicit Types P Q S I : rassn.
Implicit Types c       : cmd.

Definition psi := ident -> (@cmd_ ident cmem ident).

Section prhl.

Definition prhl_  (ps: psi) P c1 c2 Q  :=
  forall m : rmem, P m ->
    exists2 ν,
        iscoupling (ssem_ ps c1 m.1) (ssem_ ps c2 m.2) ν
      & range Q ν.

Section Logic.

Inductive derivable : pred rmem -> cmd -> cmd -> pred rmem -> Prop :=
| H_Skip : forall P, derivable P skip skip P
| H_abort P c1 c2 Q : derivable P abort abort Q
| H_case P A c1 c2 Q :
     derivable (P /\   A)%A c1 c2 Q
  -> derivable (P /\ ~ A)%A c1 c2 Q
  -> derivable P c1 c2 Q
| H_swap P c1 c2 Q :
  derivable (pswap P) c2 c1 (pswap Q) -> derivable P c1 c2 Q
| H_conseq P P' c1 c2 Q Q' :
     (forall m, P' m -> P  m)
  -> (forall m, Q  m -> Q' m)
  -> derivable P  c1 c2 Q
  -> derivable P' c1 c2 Q'
| H_assignL {t : IhbType.type} (x : vars t) (e : expr t) Q :
  derivable [pred m : rmem | Q m.[~1 x <- `[{ e }] m.1]] (x <<- e) skip Q
| H_rndL {t : IhbType.type} P (x : vars t) (d : dexpr t) Q :
     P =1 [pred m : rmem
       |  dweight (`[{ d }] m.1) == 1
       & `[< range [pred v | Q m.[~1 x <- v]] (`[{ d }] m.1) >]]
     -> derivable P (x <$- d) skip Q
| H_if P e1 e2 c1 c'1 c2 c'2 Q :
     derivable (P /\ `[{    e1#'1 &&    e2#'2 }])%A c1  c2  Q
  -> derivable (P /\ `[{ ~~ e1#'1 && ~~ e2#'2 }])%A c'1 c'2 Q
  -> derivable (P /\ `[{ e1#'1 =b e2#'2 }])%A
       (If e1 then c1 else c'1)
       (If e2 then c2 else c'2)
       Q
| H_ifL P e c1 c2 c Q :
     derivable (P /\ `[{    e#'1 }])%A c1 c Q
  -> derivable (P /\ `[{ ~~ e#'1 }])%A c2 c Q
  -> derivable P (If e then c1 else c2) c Q
| H_seq R P c1 c1' c2 c2' Q :
     derivable P c1  c2  R
  -> derivable R c1' c2' Q
  -> derivable P (c1 ;; c1') (c2 ;; c2') Q
| H_while I e1 e2 c1 c2 :
     (forall m : rmem, I m -> `[{ e1#'1 =b e2#'2 }] m)
  -> (derivable (I /\ `[{ e1#'1 && e2#'2 }])%A c1 c2 I)
  ->  derivable
    I
      (While e1 Do c1)
      (While e2 Do c2)
    (I /\ `[{ ~~ e1#'1}] /\ `[{ ~~ e2#'2 }])%A.

Scheme derivable_min := Minimality for derivable Sort Prop.

End Logic.

Section Sound.
Section Rules.
Context {ps: psi}.

Notation prhl   := (prhl_ ps).

(* -------------------------------------------------------------------- *)
Lemma prhlw P c1 c2 Q m :
  prhl P c1 c2 Q -> P m ->
    { ν | iscoupling (ssem_ ps c1 m.1) (ssem_ ps c2 m.2) ν & range Q ν }.
Proof. move=> h Pm.
have: exists ν, iscoupling (ssem_ ps c1 m.1) (ssem_ ps c2 m.2) ν /\ range Q ν.
+ by case: (h _ Pm) => ν h1 h2; exists ν; split.
by case/cid=> ν [h1 h2]; exists ν.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_sem P c1 c2 c'1 c'2 Q :
     (forall m, P m -> ssem_ ps c1 m.1 = ssem_ ps c'1 m.1)
  -> (forall m, P m -> ssem_ ps c2 m.2 = ssem_ ps c'2 m.2)
  -> prhl P c1  c2  Q
  -> prhl P c'1 c'2 Q.
Proof.
move=> eq1 eq2 h m Pm; case: (h _ Pm) => [ν hC hR].
by exists ν => //; rewrite -!(eq1, eq2).
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_conseq P P' c1 c2 Q Q' :
     (forall m, P' m -> P  m)
  -> (forall m, Q  m -> Q' m)
  -> prhl P  c1 c2 Q
  -> prhl P' c1 c2 Q'.
Proof.
move=> hP hQ h m /hP /h [ν hC hR]; exists ν => //.
by apply/range_weaken/hQ: hR.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_swap P c1 c2 Q :
  prhl P c2 c1 Q <-> prhl (pswap P) c1 c2 (pswap Q).
Proof.
move: P Q c1 c2 => [:hG] P Q c1 c2; split; last first.
+ move: P Q c1 c2; abstract: hG => P Q c1 c2 h -[m1 m2] Pm.
  case: (h (m2, m1))=> //= ν [hC1 hC2] hR; exists (dswap ν) => /=.
  * by apply/iscoupling_swap.
  * by move/range_pswap: hR; apply/range_weaken; case.
+ by move=> h; apply/hG; apply/prhl_conseq: h; case.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_lepr P c1 c2 (E1 E2 : assn) m:
     P m
  -> prhl P c1 c2 [pred m | E1 m.1 ==> E2 m.2]
  -> \P_[ssem_ ps c1 m.1] E1 <= \P_[ssem_ ps c2 m.2] E2.
Proof.
case: m => /= m1 m2 Pm h; case/h: Pm => {h} /= ν [<- <-] h.
by rewrite !pr_dmargin le_in_pr //= => m /h /implyP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_eqpr P c1 c2 (E1 E2 : assn) m:
     P m
  -> prhl P c1 c2 [pred m | E1 m.1 == E2 m.2]
  -> \P_[ssem_ ps c1 m.1] E1 = \P_[ssem_ ps c2 m.2] E2.
Proof.
case: m => [m1 m2] Pm h; rewrite (rwP eqP) eq_le (@prhl_lepr P) //=.
+ apply/prhl_conseq: h => // {m1 m2 Pm} -[m1 m2] /=.
  by move/eqP=> ->; apply/implyP.
apply/(prhl_lepr (P := pswap P) (m := (m2, m1))) => //.
move/prhl_swap: h; apply/prhl_conseq=> // {m1 m2 Pm} -[m1 m2] /=.
by move/eqP=> ->; apply/implyP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_exfalso c1 c2 Q : prhl pred0 c1 c2 Q.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_abort P c1 c2 Q : prhl P abort abort Q.
Proof.
move=> m _; exists dnull; last by apply/range_dnull.
by rewrite !ssemE; split; rewrite dmarginE dlet_null.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_case P A c1 c2 Q :
     prhl (P /\   A)%A c1 c2 Q
  -> prhl (P /\ ~ A)%A c1 c2 Q
  -> prhl P c1 c2 Q.
Proof.
move=> hA hNA m Pm; case/boolP: (A m) => [Am | NAm].
+ by apply/hA; rewrite -(rwP andP).
+ by apply/hNA; rewrite -(rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_skip P : prhl P skip skip P.
Proof.
move=> m Pm; exists (dunit m); last by apply/range_dunit.
by rewrite !ssemE -!dmargin_dunit; apply/iscoupling_prod.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_assignL {t : IhbType.type} (x : vars t) (e : expr t) Q :
  prhl [pred m : rmem | Q m.[~1 x <- `[{ e }] m.1]] (x <<- e) skip Q.
Proof.
move=> m /= Qmxe; exists (dunit (m.[~1 x <- `[{ e }] m.1])); last first.
+ by apply/range_dunit.
rewrite !ssemE; apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ by apply/distr_eqP; rewrite dmargin_dunit -/(mselect '1 _) mselect_mset.
+ by apply/distr_eqP; rewrite dmargin_dunit -/(mselect '2 _) mselect_mset.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_rndL {t : IhbType.type} P (x : vars t) (d : dexpr t) Q :
     P =1 [pred m : rmem
       |  dweight (`[{ d }] m.1) == 1
       & `[< range [pred v | Q m.[~1 x <- v]] (`[{ d }] m.1) >]]
  -> prhl P (x <$- d) skip Q.
Proof.
move=> PE -[m1 m2] /=; rewrite {}PE => /andP[/= /eqP wgt1] /asboolP hrg.
rewrite !ssemE; set μ := `[{ d }] m1.
pose ν := \dlet_(v <- μ) dunit (m1.[x <- v], m2); exists ν.
+ apply/(iscoupling_eq _ _ (iscoupling_prod _)).
  * apply/distr_eqP; rewrite dmargin_dlet; apply/eq_in_dlet=> //=.
    by move=> v _; rewrite dmargin_dunit.
  * move=> m; rewrite dmargin_dlet -[RHS]mul1r -wgt1 -dletC.
    apply/distr_eqP: m; apply/eq_in_dlet => // v _.
    by rewrite dmargin_dunit.
+ case=> m'1 m'2 /dinsupp_dlet[v vμ]; rewrite dunit1E.
  rewrite pnatr_eq0 eqb0 negbK; case/eqP=> <- <-.
  by move/(_ v vμ): hrg => /= {vμ}; case: {ν} x v.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_if P e1 e2 c1 c'1 c2 c'2 Q :
     prhl (P /\ `[{    e1#'1 &&    e2#'2 }])%A c1  c2  Q
  -> prhl (P /\ `[{ ~~ e1#'1 && ~~ e2#'2 }])%A c'1 c'2 Q
  -> prhl (P /\ `[{ e1#'1 =b e2#'2 }])%A
       (If e1 then c1 else c'1)
       (If e2 then c2 else c'2)
     Q.
Proof.
move=> h1 h2 m /andP[/= Pm /eqP]; rewrite !ssemE => eqe.
rewrite -eqe; case: ifPn => hc.
+ by apply/h1 => /=; rewrite Pm !ssemE -eqe hc.
+ by apply/h2 => /=; rewrite Pm !ssemE -eqe hc.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_ifL P e c1 c2 c Q :
     prhl (P /\ `[{    e#'1 }])%A c1 c Q
  -> prhl (P /\ `[{ ~~ e#'1 }])%A c2 c Q
  -> prhl P (If e then c1 else c2) c Q.
Proof.
move=> h1 h2 m Pm; rewrite !ssemE; case: ifPn => he.
+ by apply/h1 => /=; rewrite ssemE Pm.
+ by apply/h2 => /=; rewrite ssemE Pm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_seq R P c1 c1' c2 c2' Q :
     prhl P c1  c2  R
  -> prhl R c1' c2' Q
  -> prhl P (c1 ;; c1') (c2 ;; c2') Q.
Proof.
move=> h1 h2 m Pm; case: (h1 _ Pm) => ν hC hR.
pose ν' m :=
  if @idP (m \in dinsupp ν) is ReflectT Rm then
    tag (prhlw h2 (hR _ Rm))
  else dnull.
exists (\dlet_(m <- ν) ν' m); last first.
+ apply/(range_dlet hR) => m' Rm'; rewrite /ν'.
  case: {-}_ / idP; first by move=> p; case: prhlw.
  by move=> _ x /dinsuppP; rewrite dnullE.
rewrite !ssemE; apply/iscoupling_dlet => //.
move=> m' hm'; rewrite /ν'; case: {-}_ / idP => //.
by move=> p; case: prhlw.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_while I e1 e2 c1 c2 :
     (forall m : rmem, I m -> `[{ e1#'1 =b e2#'2 }] m)
  -> (prhl (I /\ `[{ e1#'1 && e2#'2 }])%A c1 c2 I)
  ->  prhl
    I
      (While e1 Do c1)
      (While e2 Do c2)
    (I /\ `[{ ~~ e1#'1}] /\ `[{ ~~ e2#'2 }])%A.
Proof. set J := (I /\ _)%A => hs h.
pose ν1 m := if @idP (J m) is ReflectT Rm then tag (prhlw h Rm) else dunit m.
pose νn := fix νn n m {struct n} :=
  if n is n.+1 then \dlet_(m' <- νn n m) ν1 m' else dunit m.
pose νe n m := \dlet_(m' <- νn n m) if esem e1 m'.1 then dnull else dunit m'.
move=> m Im; pose ν n := νe n m.
have rg_νn: forall n, range I (νn n m).
+ elim=> [|n ih] /=; first by apply/range_dunit.
  apply/(range_dlet ih) => {Im ν ih} m Im; rewrite /ν1.
  case: {-}_ / idP; first by move=> p; case: prhlw.
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
+ rewrite !ssemE;
    rewrite -(iffLR (distr_eqP _ _) (dlim_bump (fun _ => _ m.1)));
    rewrite -(iffLR (distr_eqP _ _) (dlim_bump (fun _ => _ m.2))).
  apply/iscoupling_dlim => [n|n k le_nk]; last first.
  * move=> m'; rewrite -[k](subnK le_nk); elim: (_ - _)%N => //.
    by move=> n' ihn'; rewrite addSn; apply/(le_trans ihn').
  rewrite !whilen_iterc !ssemE; apply/iscoupling_dlet => /=; last first.
  * move=> m' Im'; rewrite !ssemE; move/rg_νn/hs: Im'.
    rewrite !ssemE => /eqP <-; case: ifPn => _.
    - by apply/iscoupling_dnull.
    - by case: m' => a b; apply/iscoupling_dunit.
  elim: n => /= [|n ihn]; rewrite !(iterc0, itercSr) !ssemE.
  * by case: {+}m => a b; apply/iscoupling_dunit.
  apply/iscoupling_dlet => //= m' /rg_νn Im'; move/hs: (Im').
  rewrite !ssemE => /eqP eqe; rewrite -eqe /ν1.
  case: {-}_ / idP => /= [p|]; first case/and3P: {+}p.
  * by rewrite !ssemE => _ -> _; case: prhlw.
  rewrite !ssemE -eqe Im' /= andbb => /negP/negbTE => ->/=.
  by case: {+}m' => a b; apply/iscoupling_dunit.
+ apply/range_dlim => n; apply/(range_dlet (rg_νn n)) => m' Im'.
  case: ifPn => [he1|hNe1]; first by apply/range_dnull.
  apply/range_dunit=> /=; rewrite Im' /= !ssemE.
  by move: (hs _ Im'); rewrite !ssemE => /eqP <-; rewrite hNe1.
Qed.
End Rules.

Hint Resolve prhl_skip             : prhl.
Hint Resolve prhl_abort            : prhl.
Hint Resolve prhl_case             : prhl.
Hint Resolve prhl_swap             : prhl.
Hint Resolve prhl_conseq           : prhl.
Hint Resolve prhl_assignL          : prhl.
Hint Resolve prhl_rndL             : prhl.
Hint Resolve prhl_if               : prhl.
Hint Resolve prhl_ifL              : prhl.
Hint Resolve prhl_seq              : prhl.
Hint Resolve prhl_while            : prhl.

Lemma soundness :
  (forall ps P c1 c2 Q,
      derivable P c1 c2 Q ->
       prhl_ ps P c1 c2 Q).
Proof.
intros ps.
apply: derivable_min.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ intros ??????;  apply prhl_swap; auto.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
Qed.

End Sound.
End prhl.
