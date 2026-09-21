(* -------------------------------------------------------------------- *)
From Stdlib             Require Import Setoid Morphisms.
From mathcomp           Require Import boot order algebra.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import counting_distr.
From xhl.pwhile Require Import notations inhabited mem pwhile psemantic passn range.
From xhl.hl     Require Import hl_stmt.

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
Context {R : realType}.
Local Notation Distr T := {distr T%type / R}.
Context {A B : choiceType} (μ1 : Distr A) (μ2 : Distr B).

Definition iscoupling (ν : Distr (A * B)) :=
  dfst ν = μ1 /\ dsnd ν = μ2.
End Couplings.

(* -------------------------------------------------------------------- *)
Section CouplingsTheory.
Context {R : realType}.
Local Notation Distr T := {distr T%type / R}.
Context {A B C D : choiceType}.

Lemma iscoupling_eq (μ1 μ2 μ1' μ2' : Distr _) (ν : Distr (A * B)) :
  μ1 =1 μ1' -> μ2 =1 μ2' -> iscoupling μ1 μ2 ν -> iscoupling μ1' μ2' ν.
Proof. by do 2! move=> /distr_eqP->. Qed.

Lemma iscoupling_prod (μ : Distr (A * B)) :
  iscoupling (dfst μ) (dsnd μ) μ.
Proof. by []. Qed.

Lemma iscoupling_dnull : @iscoupling R A B dnull dnull dnull.
Proof. by split; rewrite dmarginE dlet_null. Qed.

Lemma iscoupling_dunit a b :
  @iscoupling R A B (dunit a) (dunit b) (dunit (a, b)).
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
Section prhl.
Context {Rl : realType} {A B : codeType} {X Xg Y : eqType}
        {M : memType A B X Xg}.

Local Notation Distr T := {distr T%type / Rl}.
Local Notation rmem  := (rmem A B X Xg M).
Local Notation vars  := (vars_ X).
Local Notation gvars   := (vars_ Xg).
Local Notation expr  := (@expr_ A B X Xg M).
Local Notation dexpr T := (expr (Distr T)).
Local Notation cmd   := (@cmd_ Rl A B X Xg M Y).
Local Notation assn  := (pred M).
Local Notation rassn := (pred rmem).
Local Notation psi := (Y -> (@cmd_ Rl A B X Xg M Y)).

Implicit Types P Q S I : rassn.
Implicit Types c       : cmd.

Definition prhl_  (ps1 ps2: psi) P c1 c2 Q  :=
  forall m : rmem, P m ->
    exists2 ν,
        iscoupling (ssem_ ps1 c1 m.1) (ssem_ ps2 c2 m.2) ν
      & range Q ν.

Section Logic.

Inductive derivable : psi -> psi -> pred rmem -> cmd -> cmd -> pred rmem -> Prop :=
| H_Skip : forall P ps1 ps2, derivable ps1 ps2 P skip skip P
| H_abort P c1 c2 Q ps1 ps2: derivable ps1 ps2 P abort abort Q
| H_case P Pa c1 c2 Q ps1 ps2:
     derivable ps1 ps2 (P /\   Pa)%A c1 c2 Q
  -> derivable ps1 ps2 (P /\ ~ Pa)%A c1 c2 Q
  -> derivable ps1 ps2 P c1 c2 Q
| H_swap P c1 c2 Q ps1 ps2:
  derivable ps2 ps1 (pswap P) c2 c1 (pswap Q) -> derivable ps1 ps2 P c1 c2 Q
| H_conseq P P' c1 c2 Q Q' ps1 ps2 :
     (forall m, P' m -> P  m)
  -> (forall m, Q  m -> Q' m)
  -> derivable ps1 ps2 P  c1 c2 Q
  -> derivable ps1 ps2 P' c1 c2 Q'
| H_assignL {t : A} (x : vars t) (e : expr t) Q ps1 ps2:
  derivable ps1 ps2 [pred m : rmem | Q m.[~1 x <- `[{ e }] m.1]] (x <<- e) skip Q
| H_rndL {t : A} P (x : vars t) (d : dexpr t) Q ps1 ps2 :
     P =1 [pred m : rmem
       |  dweight (`[{ d }] m.1) == 1
       & `[< range [pred v | Q m.[~1 x <- v]] (`[{ d }] m.1) >]]
     -> derivable ps1 ps2 P (x <$- d) skip Q
| H_if P e1 e2 c1 c'1 c2 c'2 Q ps1 ps2:
     derivable ps1 ps2 (P /\ `[{    e1#'1 &&    e2#'2 }])%A c1  c2  Q
  -> derivable ps1 ps2 (P /\ `[{ ~~ e1#'1 && ~~ e2#'2 }])%A c'1 c'2 Q
  -> derivable ps1 ps2 (P /\ `[{ e1#'1 =b e2#'2 }])%A
       (If e1 then c1 else c'1)
       (If e2 then c2 else c'2)
       Q
| H_ifL P e c1 c2 c Q ps1 ps2 :
     derivable ps1 ps2 (P /\ `[{    e#'1 }])%A c1 c Q
  -> derivable ps1 ps2 (P /\ `[{ ~~ e#'1 }])%A c2 c Q
  -> derivable ps1 ps2 P (If e then c1 else c2) c Q
| H_seq R P c1 c1' c2 c2' Q ps1 ps2:
     derivable ps1 ps2 P c1  c2  R
  -> derivable ps1 ps2 R c1' c2' Q
  -> derivable ps1 ps2 P (c1 ;; c1') (c2 ;; c2') Q
| H_while I e1 e2 c1 c2 ps1 ps2:
     (forall m : rmem, I m -> `[{ e1#'1 =b e2#'2 }] m)
  -> (derivable ps1 ps2 (I /\ `[{ e1#'1 && e2#'2 }])%A c1 c2 I)
  ->  derivable ps1 ps2
    I
      (While e1 Do c1)
      (While e2 Do c2)
    (I /\ `[{ ~~ e1#'1}] /\ `[{ ~~ e2#'2 }])%A.

Scheme derivable_min := Minimality for derivable Sort Prop.

End Logic.

Section Sound.
Section Rules.

(* -------------------------------------------------------------------- *)
Lemma prhlw P c1 c2 Q m ps1 ps2:
  prhl_ ps1 ps2 P c1 c2 Q -> P m ->
    { ν | iscoupling (ssem_ ps1 c1 m.1) (ssem_ ps2 c2 m.2) ν & range Q ν }.
Proof. move=> h Pm.
have: exists ν, iscoupling (ssem_ ps1 c1 m.1) (ssem_ ps2 c2 m.2) ν /\ range Q ν.
+ by case: (h _ Pm) => ν h1 h2; exists ν; split.
by case/cid=> ν [h1 h2]; exists ν.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_sem P c1 c2 c'1 c'2 Q ps1 ps2:
     (forall m, P m -> ssem_ ps1 c1 m.1 = ssem_ ps1 c'1 m.1)
  -> (forall m, P m -> ssem_ ps2 c2 m.2 = ssem_ ps2 c'2 m.2)
  -> prhl_ ps1 ps2 P c1  c2  Q
  -> prhl_ ps1 ps2 P c'1 c'2 Q.
Proof.
move=> eq1 eq2 h m Pm; case: (h _ Pm) => [ν hC hR].
by exists ν => //; rewrite -!(eq1, eq2).
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_conseq P P' c1 c2 Q Q' ps1 ps2:
     (forall m, P' m -> P  m)
  -> (forall m, Q  m -> Q' m)
  -> prhl_ ps1 ps2 P  c1 c2 Q
  -> prhl_ ps1 ps2 P' c1 c2 Q'.
Proof.
move=> hP hQ h m /hP /h [ν hC hR]; exists ν => //.
by apply/range_weaken/hQ: hR.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_swap P c1 c2 Q ps1 ps2:
  @prhl_ ps2 ps1 P c2 c1 Q <-> @prhl_ ps1 ps2 (pswap P) c1 c2 (pswap Q).
Proof.
move: P Q c1 c2 ps1 ps2 => [:hG] P Q c1 c2; split; last first.
+ move: P Q c1 c2 ps1 ps2; abstract: hG => P Q c1 c2 ps1 ps2 h -[m1 m2] Pm.
  case: (h (m2, m1))=> //= ν [hC1 hC2] hR; exists (dswap ν) => /=.
  * by apply/iscoupling_swap.
  * by move/range_pswap: hR; apply/range_weaken; case.
+ by move=> h;  apply/hG; apply/prhl_conseq: h; case.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_lepr P c1 c2 (E1 E2 : assn) m ps1 ps2:
     P m
  -> prhl_ ps1 ps2 P c1 c2 [pred m | E1 m.1 ==> E2 m.2]
  -> \P_[ssem_ ps1 c1 m.1] E1 <= \P_[ssem_ ps2 c2 m.2] E2.
Proof.
case: m => /= m1 m2 Pm h; case/h: Pm => {h} /= ν [<- <-] h.
by rewrite !pr_dmargin le_in_pr //= => m /h /implyP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_eqpr P c1 c2 (E1 E2 : assn) m ps1 ps2:
     P m
  -> prhl_ ps1 ps2 P c1 c2 [pred m | E1 m.1 == E2 m.2]
  -> \P_[ssem_ ps1 c1 m.1] E1 = \P_[ssem_ ps2 c2 m.2] E2.
Proof.
case: m => [m1 m2] Pm h; rewrite (rwP eqP) eq_le (@prhl_lepr P) //=.
+ apply/prhl_conseq: h => // {m1 m2 Pm} -[m1 m2] /=.
  by move/eqP=> ->; apply/implyP.
apply/(prhl_lepr (P := pswap P) (m := (m2, m1))) => //.
move/prhl_swap: h; apply/prhl_conseq=> // {m1 m2 Pm} -[m1 m2] /=.
by move/eqP=> ->; apply/implyP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_exfalso c1 c2 Q ps1 ps2: prhl_ ps1 ps2 pred0 c1 c2 Q.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_abort P c1 c2 Q ps1 ps2: prhl_ ps1 ps2 P abort abort Q.
Proof.
move=> m _; exists dnull; last by apply/range_dnull.
by rewrite !ssemE; split; rewrite dmarginE dlet_null.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_case P Pa c1 c2 Q ps1 ps2:
     prhl_ ps1 ps2 (P /\   Pa)%A c1 c2 Q
  -> prhl_ ps1 ps2 (P /\ ~ Pa)%A c1 c2 Q
  -> prhl_ ps1 ps2 P c1 c2 Q.
Proof.
move=> hA hNA m Pm; case/boolP: (Pa m) => [Am | NAm].
+ by apply/hA; rewrite -(rwP andP).
+ by apply/hNA; rewrite -(rwP andP).
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_skip P ps1 ps2: prhl_ ps1 ps2 P skip skip P.
Proof.
move=> m Pm; exists (dunit m); last by apply/range_dunit.
by rewrite !ssemE -!dmargin_dunit; apply/iscoupling_prod.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_assignL {t : A} (x : vars t) (e : expr t) Q ps1 ps2:
  prhl_ ps1 ps2 [pred m : rmem | Q m.[~1 x <- `[{ e }] m.1]] (x <<- e) skip Q.
Proof.
move=> m /= Qmxe; exists (dunit (m.[~1 x <- `[{ e }] m.1])); last first.
+ by apply/range_dunit.
rewrite !ssemE; apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ by apply/distr_eqP; rewrite dmargin_dunit -/(mselect '1 _) mselect_mset.
+ by apply/distr_eqP; rewrite dmargin_dunit -/(mselect '2 _) mselect_mset.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_assign {t1 t2 : A}
    (x1 : vars t1) (e1 : expr t1) (x2 : vars t2) (e2 : expr t2)
    Q (ps1 ps2 : psi) :
  prhl_ ps1 ps2
    [pred m : rmem | Q (m.[~1 x1 <- `[{ e1 }] m.1]).[~2 x2 <- `[{ e2 }] m.2]]
    (x1 <<- e1) (x2 <<- e2) Q.
Proof.
move=> m /= Qm.
exists (dunit (m.[~1 x1 <- `[{ e1 }] m.1]).[~2 x2 <- `[{ e2 }] m.2]); last first.
+ by apply/range_dunit.
rewrite !ssemE; apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ by apply/distr_eqP; rewrite dmargin_dunit -/(mselect '1 _) !mselect_mset.
+ by apply/distr_eqP; rewrite dmargin_dunit -/(mselect '2 _) !mselect_mset.
Qed.

(* -------------------------------------------------------------------- *)
Definition gset1 {t : B} (m : rmem) (x : gvars t) (v : interp t) : rmem :=
  m.{(x #g '1)%V <- v}.

Definition gset2 {t : B} (m : rmem) (x : gvars t) (v : interp t) : rmem :=
  m.{(x #g '2)%V <- v}.

Lemma prhl_gassignL {t : B} (x : gvars t) (e : expr (interp t))
    Q (ps1 ps2 : psi) :
  prhl_ ps1 ps2
    [pred m : rmem | Q (gset1 m x (`[{ e }] m.1))]
    (G x <<- e) skip Q.
Proof.
move=> m /= Qm; exists (dunit (gset1 m x (`[{ e }] m.1))); last first.
+ by apply/range_dunit.
rewrite !ssemE; apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ by apply/distr_eqP; rewrite dmargin_dunit /gset1 msetg_iE.
+ by apply/distr_eqP; rewrite dmargin_dunit /gset1 msetg_iE.
Qed.

Lemma prhl_gassign {t1 t2 : B}
    (x1 : gvars t1) (e1 : expr (interp t1))
    (x2 : gvars t2) (e2 : expr (interp t2)) Q (ps1 ps2 : psi) :
  prhl_ ps1 ps2
    [pred m : rmem |
       Q (gset2 (gset1 m x1 (`[{ e1 }] m.1)) x2 (`[{ e2 }] m.2))]
    (G x1 <<- e1) (G x2 <<- e2) Q.
Proof.
move=> m /= Qm.
exists (dunit (gset2 (gset1 m x1 (`[{ e1 }] m.1)) x2 (`[{ e2 }] m.2)));
  last first.
+ by apply/range_dunit.
rewrite !ssemE; apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ by apply/distr_eqP; rewrite dmargin_dunit /gset2 /gset1 !msetg_iE.
+ by apply/distr_eqP; rewrite dmargin_dunit /gset2 /gset1 !msetg_iE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_rndL {t : A} P (x : vars t) (d : dexpr t) Q ps1 ps2:
     P =1 [pred m : rmem
       |  dweight (`[{ d }] m.1) == 1
       & `[< range [pred v | Q m.[~1 x <- v]] (`[{ d }] m.1) >]]
  -> prhl_ ps1 ps2 P (x <$- d) skip Q.
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
Lemma prhl_rnd {t : A} P (x1 x2 : vars t) (d1 d2 : dexpr t)
    Q (ps1 ps2 : psi) :
     (forall m : rmem, P m -> `[{ d1 }] m.1 = `[{ d2 }] m.2)
  -> (forall (m : rmem) v, P m -> v \in dinsupp (`[{ d1 }] m.1) ->
        Q (m.[~1 x1 <- v]).[~2 x2 <- v])
  -> prhl_ ps1 ps2 P (x1 <$- d1) (x2 <$- d2) Q.
Proof.
move=> eqd hQ m Pm; rewrite !ssemE.
exists (\dlet_(v <- `[{ d1 }] m.1) dunit ((m.[~1 x1 <- v]).[~2 x2 <- v]));
  last first.
+ by move=> m' /dinsupp_dlet[v vd /in_dunit ->]; apply: hQ.
apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ apply/distr_eqP; rewrite dmargin_dlet; apply/eq_in_dlet => //=.
  by move=> v _; rewrite dmargin_dunit -/(mselect '1 _) !mselect_mset.
+ apply/distr_eqP; rewrite dmargin_dlet -(eqd _ Pm); apply/eq_in_dlet => //=.
  by move=> v _; rewrite dmargin_dunit -/(mselect '2 _) !mselect_mset.
Qed.

(* -------------------------------------------------------------------- *)
(* Both sides sample, coupled along a map [f]: the left value [v] is
 * matched with [f m v] on the right.  The two sample spaces may now
 * differ, which [prhl_rnd] does not allow, and [f] may depend on the
 * memory, as EasyCrypt's [rnd] does.  [prhl_rnd] is the [f = id] case.
 *
 * Note the premise is a pushforward equation, *not* bijectivity of [f]:
 * the witness [\dlet_(v <- d1) dunit (v, f m v)] has first marginal
 * [d1] and second marginal [dmargin (f m) d1], so [dmargin (f m) d1 =
 * d2] is exactly what makes it a coupling.  EasyCrypt states its rule
 * with a bijection because it also wants the inverse, to read the
 * postcondition from either side; nothing here needs it. *)
Lemma prhl_rnd_gen {t1 t2 : A} P (x1 : vars t1) (x2 : vars t2)
    (d1 : dexpr t1) (d2 : dexpr t2) (f : rmem -> interp t1 -> interp t2)
    Q (ps1 ps2 : psi) :
     (forall m : rmem, P m -> dmargin (f m) (`[{ d1 }] m.1) = `[{ d2 }] m.2)
  -> (forall (m : rmem) v, P m -> v \in dinsupp (`[{ d1 }] m.1) ->
        Q (m.[~1 x1 <- v]).[~2 x2 <- f m v])
  -> prhl_ ps1 ps2 P (x1 <$- d1) (x2 <$- d2) Q.
Proof.
move=> eqd hQ m Pm; rewrite !ssemE.
exists (\dlet_(v <- `[{ d1 }] m.1)
          dunit ((m.[~1 x1 <- v]).[~2 x2 <- f m v])); last first.
+ by move=> m' /dinsupp_dlet[v vd /in_dunit ->]; apply: hQ.
apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ apply/distr_eqP; rewrite dmargin_dlet; apply/eq_in_dlet => //=.
  by move=> v _; rewrite dmargin_dunit -/(mselect '1 _) !mselect_mset.
+ apply/distr_eqP; rewrite dmargin_dlet -(eqd _ Pm) dlet_dmargin.
  apply/eq_in_dlet => //=.
  by move=> v _; rewrite dmargin_dunit -/(mselect '2 _) !mselect_mset.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_block P bs1 (c1 : cmd) rs1 bs2 (c2 : cmd) rs2
    Q (ps1 ps2 : psi) :
     (forall m0 : rmem, P m0 ->
        prhl_ ps1 ps2
          [pred m : rmem |
             (m.1 == minit m0.1 bs1) && (m.2 == minit m0.2 bs2)]
          c1 c2
          [pred m : rmem | Q (mret m0.1 m.1 rs1, mret m0.2 m.2 rs2)])
  -> prhl_ ps1 ps2 P (block bs1 c1 rs1) (block bs2 c2 rs2) Q.
Proof.
move=> h m0 Pm0.
have hpre :
  (minit m0.1 bs1 == minit m0.1 bs1) && (minit m0.2 bs2 == minit m0.2 bs2).
+ by rewrite !eqxx.
case: (h m0 Pm0 (minit m0.1 bs1, minit m0.2 bs2) hpre) => ν [hC1 hC2] hR.
rewrite !ssemE.
exists (\dlet_(m <- ν) dunit (mret m0.1 m.1 rs1, mret m0.2 m.2 rs2));
  last first.
+ by apply/(range_dlet hR) => m' Qm'; apply/range_dunit.
apply/(iscoupling_eq _ _ (iscoupling_prod _)).
+ apply/distr_eqP; rewrite dmargin_dlet -hC1 dlet_dmargin.
  by apply/eq_in_dlet => //= m' _; rewrite dmargin_dunit.
+ apply/distr_eqP; rewrite dmargin_dlet -hC2 dlet_dmargin.
  by apply/eq_in_dlet => //= m' _; rewrite dmargin_dunit.
Qed.

(* -------------------------------------------------------------------- *)
Definition lossless_ps (ps : psi) (P : pred M) (c : cmd) :=
  forall m : M, P m -> dweight (ssem_ ps c m) = 1.

(* -------------------------------------------------------------------- *)
Lemma prhl_prod (P1 Q1 P2 Q2 : pred M) (c1 c2 : cmd) (ps1 ps2 : psi) :
     lossless_ps ps1 P1 c1
  -> lossless_ps ps2 P2 c2
  -> hl_ ps1 P1 c1 Q1
  -> hl_ ps2 P2 c2 Q2
  -> prhl_ ps1 ps2
       [pred m : rmem | P1 m.1 & P2 m.2] c1 c2
       [pred m : rmem | Q1 m.1 & Q2 m.2].
Proof.
move=> ll1 ll2 h1 h2 [m1 m2] /= /andP[P1m1 P2m2].
have w1 : dweight (ssem_ ps1 c1 m1) = 1 by apply: ll1.
have w2 : dweight (ssem_ ps2 c2 m2) = 1 by apply: ll2.
exists (\dlet_(a <- ssem_ ps1 c1 m1)
          \dlet_(b <- ssem_ ps2 c2 m2) dunit (a, b)); last first.
+ apply/(range_dlet (h1 _ P1m1)) => a Q1a.
  apply/(range_dlet (h2 _ P2m2)) => b Q2b.
  by apply/range_dunit; rewrite /= Q1a Q2b.
split.
+ rewrite dmargin_dlet -[RHS](dlet_dunit_id (ssem_ ps1 c1 m1)).
  apply/eq_in_dlet => // a _; rewrite dmargin_dlet.
  apply/distr_eqP => t; rewrite -[RHS]mul1r -w2 -dletC.
  apply/distr_eqP: t; apply/eq_in_dlet => // b _.
  by rewrite dmargin_dunit.
+ rewrite dmargin_dlet.
  apply/distr_eqP => t; rewrite -[RHS]mul1r -w1 -dletC.
  apply/distr_eqP: t; apply/eq_in_dlet => // a _.
  rewrite dmargin_dlet -[RHS](dlet_dunit_id (ssem_ ps2 c2 m2)).
  by apply/eq_in_dlet => // b _; rewrite dmargin_dunit.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_if P e1 e2 c1 c'1 c2 c'2 Q ps1 ps2:
     prhl_ ps1 ps2 (P /\ `[{    e1#'1 &&    e2#'2 }])%A c1  c2  Q
  -> prhl_ ps1 ps2 (P /\ `[{ ~~ e1#'1 && ~~ e2#'2 }])%A c'1 c'2 Q
  -> prhl_ ps1 ps2 (P /\ `[{ e1#'1 =b e2#'2 }])%A
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
Lemma prhl_ifL P e c1 c2 c Q ps1 ps2:
     prhl_ ps1 ps2 (P /\ `[{    e#'1 }])%A c1 c Q
  -> prhl_ ps1 ps2 (P /\ `[{ ~~ e#'1 }])%A c2 c Q
  -> prhl_ ps1 ps2 P (If e then c1 else c2) c Q.
Proof.
move=> h1 h2 m Pm; rewrite !ssemE; case: ifPn => he.
+ by apply/h1 => /=; rewrite ssemE Pm.
+ by apply/h2 => /=; rewrite ssemE Pm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma prhl_seq R P c1 c1' c2 c2' Q ps1 ps2:
     prhl_ ps1 ps2 P c1  c2  R
  -> prhl_ ps1 ps2 R c1' c2' Q
  -> prhl_ ps1 ps2 P (c1 ;; c1') (c2 ;; c2') Q.
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
Lemma prhl_while I e1 e2 c1 c2 ps1 ps2:
     (forall m : rmem, I m -> `[{ e1#'1 =b e2#'2 }] m)
  -> (prhl_ ps1 ps2 (I /\ `[{ e1#'1 && e2#'2 }])%A c1 c2 I)
  ->  prhl_ ps1 ps2
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
  elim: n => [|n ihn]; rewrite !(iterc0, itercSr) !ssemE.
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
  (forall ps1 ps2 P c1 c2 Q,
      derivable ps1 ps2 P c1 c2 Q ->
       prhl_ ps1 ps2 P c1 c2 Q).
Proof.
apply: derivable_min.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ eauto 2 with prhl.
+ intros ????????;apply prhl_swap; auto.
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
