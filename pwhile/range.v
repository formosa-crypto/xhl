(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis  Require Import reals realseq realsum distr.
(* ----------------- *) Require Import notations inhabited pwhile psemantic passn.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope sem_scope.
Local Open Scope mem_scope.

(* -------------------------------------------------------------------- *)
Definition range {A : choiceType} (P : pred A) (mu : Distr A) := 
  forall m, m \in dinsupp mu -> P m.  

Section Range.
Context {A B : choiceType}.

Lemma range_dnull (P : pred A) : range P dnull.
Proof. by move=> x /dinsuppP; rewrite dnullE. Qed.

Lemma range_dunit (P: pred A) m : P m -> range P (dunit m).
Proof. by move=> Pm m' /in_dunit ->. Qed.

Lemma range_dlet (PA : pred A) (PB : pred B) mu f :
    range PA mu -> (forall m, PA m -> range PB (f m))
  -> range PB (\dlet_(m <- mu) f m).
Proof. by move=> hA hB y /dinsupp_dlet[x] /hA /hB /(_ y). Qed.

Lemma dinsupp_dlim (mu : nat -> Distr A) x:
  x \in dinsupp (\dlim_(n) mu n) ->
    exists k, x \in dinsupp (mu k).
Proof.
move/dinsuppP; rewrite dlimE; apply: contra_notP.
move/asboolPn/forallp_asboolPn => eq; rewrite (@eq_nlim _ (fun _ => 0)).
  by move=> n; apply/dinsuppPn/negP/eq.
  by rewrite nlimC.
Qed.

Lemma range_dlim P (mu : nat -> Distr A):
  (forall n, range P (mu n)) -> range P (dlim mu).
Proof. by move=> h m /dinsupp_dlim[k] /h. Qed.
 
Lemma range_weaken (P1 P2 : pred A) mu:
  (forall x, P1 x -> P2 x) ->
  range P1 mu -> range P2 mu.
Proof. by move=> imp_P h m /h /imp_P. Qed.

Lemma range_pswap (P : pred (A * B)) (mu : Distr (A * B)) :
  range P mu -> range (pswap P) (dswap mu).
Proof.
move=> h [m1 m2] m_in_mu; have := h (m2, m1); apply.
by apply/dinsuppP; rewrite -dswapK; apply/dinsuppP/dinsupp_swap.
Qed.

Lemma pr_range (mu : Distr A) (E : pred A) :
  \P_[mu] (~ E)%A = 0 <-> range E mu.
Proof. 
  split.
  + by move=> /pr_eq0 h x; apply/contraLR => /h /dinsuppPn. 
  rewrite /range -(pr_pred0 mu)=> Hin;apply eq_in_pr=> x /Hin.
  by rewrite /mem /= /in_mem /= => ->.   (* TODO: simplify this *)
Qed.
End Range.

(* -------------------------------------------------------------------- *)
Section Phl.
Context {X : eqType} {mem : memType X}.

Notation assn := (pred mem).
Notation cmd  := (@cmd_ X mem).

Definition phl (P : assn) (c : cmd) (Q : assn) :=
  forall m, P m -> range Q (ssem_ c m).

Arguments phl P%_A c%_S Q%_A.

Definition forall_in {T : IhbType.type} (mu : mem -> Distr T) (P : T -> assn) : assn := 
  `[< fun m => forall t,  t \in dinsupp (mu m) -> P t m >]%A.

Notation "`[ 'forall' x 'in' mu => Q ]" :=
  (@forall_in _ mu%A (fun x => Q)): assn.

Notation "`[ 'forall' x 'in' mu | m => Q ]" :=
  (@forall_in _ mu%A (fun x m => Q)): assn.

(* -------------------------------------------------------------------- *)
(* Core rules                                                           *)
(* -------------------------------------------------------------------- *)
Lemma phl_eq (P Q : assn) (c c' : cmd): 
     (forall m, P m -> ssem_ c m = ssem_ c' m) 
  -> phl P c Q
  -> phl P c' Q.
Proof. by move=> Hc Hw m Pm;rewrite -Hc //;apply Hw. Qed.

Instance phl_m : Proper (eq ==> @eqcmd _ mem ==> eq ==> iff) phl.
Proof. by move=> ??-> ??? ??->;split;apply phl_eq. Qed.

Lemma phl_conseq (P2 Q2 P1 Q1 : assn) (c : cmd):
 (forall m, P1 m -> P2 m) ->
 (forall m, Q2 m -> Q1 m) ->
 phl P2 c Q2 -> phl P1 c Q1.
Proof. by move=> HP HQ H2 m /HP /H2 Hr m' /Hr /HQ. Qed.

Lemma phl_F (c : cmd) P: phl pred0 c P.
Proof. by []. Qed.

Lemma phl_T (c : cmd) P: phl P c predT.
Proof. by []. Qed.

Lemma phl_skip (P : assn) : phl P skip P.
Proof. by move=> ??;rewrite ssemE;apply range_dunit. Qed.

Lemma phl_abort (P Q : assn) : phl P abort Q.
Proof. by move=> ??;rewrite ssemE;apply range_dnull. Qed.

Lemma phl_assign {T : IhbType.type} x (e:expr_ X mem T) (Q : assn):
   phl [pred m | Q m.[x <- `[{e}]%A m]] (x <<- e) Q.
Proof. by move=> m /=;rewrite !semE;apply range_dunit. Qed.

Lemma phl_random {T : IhbType.type} x (d:expr_ X mem (Distr T)) (Q : assn):
   phl `[forall v in `[{d}] | m => Q m.[x <- v]] (x <$- d) Q.
Proof. 
move=> m /asboolP /= h; rewrite !semE.
apply (@range_dlet _ _ [pred v | Q m.[x<- v]]) => v /=.
  by apply h. by apply range_dunit.
Qed.

Lemma phl_seq (R Pr Po : assn) (c1 c2:cmd):
  phl Pr c1 R -> phl R c2 Po -> phl Pr (c1;;c2) Po.
Proof.
by move=> H1 H2 m /H1 Hm; rewrite ssemE; apply/(range_dlet Hm H2).
Qed.

Lemma phl_if (Pr Po : assn) (e:expr_ X mem bool) (c1 c2:cmd):
  phl (Pr /\ `[{e}])   c1 Po ->
  phl (Pr /\ `[{~~e}]) c2 Po -> 
  phl Pr (If e then c1 else c2)%S Po.
Proof.
by move=> H1 H2 m Hm; rewrite ssemE; case: ifPn => He;
  [apply H1 | apply H2] => /=; rewrite Hm.
Qed.
  
Lemma phl_while (I : assn) (e:expr_ X mem bool) (c:cmd):
  phl (I /\ `[{e}]) c I ->
  phl I (While e Do c) (I /\ `[{~~e}]).
Proof.
move=> Hc m Hm; rewrite ssemE; apply/range_dlim=> n.
elim: n m Hm => [|n Hn] m Hm /=.
+ by rewrite ssemE; apply range_dnull.
apply (@phl_if I)=> //; last by apply phl_skip.
by apply (phl_seq Hc)=> ??; apply Hn.
Qed.

(* -------------------------------------------------------------------- *)
Lemma phl_ll (P Q : assn) (c:cmd) m: 
  phl P c Q -> P m -> \P_[ssem_ c m] predT = 1 -> \P_[ssem_ c m] Q = 1.
Proof.
 by move=> Hphl /Hphl HP <-; rewrite !pr_exp;apply/eq_exp => x /HP ->.
Qed.
End Phl.

(* -------------------------------------------------------------------- *)
Definition eqon (X : pred { t : IhbType.type & vars t } ) (m : cmem) :=
  nosimpl (fun m' : cmem => forall x, x \in X -> m.[tagged x] = m'.[tagged x]).

Definition separated X (P : pred dmem) :=
  forall (mu1 mu2 : dmem),
      (forall m : cmem, \P_[mu1] [pred m' | `[<eqon (predC X) m m'>] ] =
                        \P_[mu2] [pred m' | `[<eqon (predC X) m m'>] ])
    -> mu1 \in P -> mu2 \in P.

(* -------------------------------------------------------------------- *)
Fixpoint mod (c : cmd) : pred { t : IhbType.type & vars t } :=
  match c with
  | abort    => pred0
  | skip     => pred0
  | x <<- _  => [pred y | `[<y = Tagged _ x>]]
  | x <$- _  => [pred y | `[<y = Tagged _ x>]]
  | c1 ;; c2 => [predU mod c1 & mod c2]

  | If _ then c1 else c2 => [predU mod c1 & mod c2]
  | While _ Do c         => mod c
  end.

(* -------------------------------------------------------------------- *)
Definition eaccess {t} (e : expr t) : pred { t : IhbType.type & vars t } :=
  match e with
  | var_ _ x => [pred y | `[<y = Tagged _ x>]]
  | _ => pred0
  end.

(* -------------------------------------------------------------------- *)
Global Instance eqon_R X : Equivalence (eqon X).
Proof. 
constructor=> //; first by move=> c1 c2 eq x /eq ->.
by move=> c1 c2 c3 eq1 eq2 x xX; rewrite eq1 ?eq2.
Qed.

(* -------------------------------------------------------------------- *)
Lemma mod_spec c m:
   phl [pred m' | m == m'] c 
       [pred m' | `[<eqon (predC (mod c)) m m'>] ].
Proof. elim: c m.
+ by move=> m; apply phl_abort.
+ move=> m; pose P := [pred m' | m == m'].
  apply (phl_conseq (P2 := P) (Q2 := P))=> //; last exact/phl_skip.
  by move=> m' /eqP ->; apply/asboolT.
+ move=> t x e m; set Q := (Q in phl _ _ Q).
  pose R := [pred m' | Q m'.[x <- `[{e}] m']].
  apply (phl_conseq (P2 := R) (Q2 := Q))=> //; last exact/phl_assign.
  move=> m' /eqP <-; apply/asboolP=> -[u y] /asboolP /=.
  move/eq_vars=> neq; rewrite mget_neq //.
  by case: eqP neq; intuition.
+ move=> t x d m; set Q := (Q in phl _ _ Q).
  pose R := forall_in `[{d}] (fun v m => Q m.[x <- v]).
  apply (phl_conseq (P2 := R) (Q2 := Q)) => //; last exact/phl_random.
  move=> m' /= /eqP <-; apply/asboolP => z.
  move=> zQ; apply/asboolP => -[u y] /asboolP /eq_vars /= neq.
  by rewrite mget_neq //; case: eqP neq; intuition.
+ move=> e c1 ih1 c2 ih2 m; apply phl_if.
  * pose P := [pred m' | m == m'].
    pose Q := [pred m' | `[<eqon (predC (mod c1)) m m'>]].
    apply (phl_conseq (P2 := P) (Q2 := Q)); last exact/ih1.
    - by move=> m' /= /andP [/eqP <-].
    move=> m' /asboolP eq_m_m'; apply/asboolP=> z.
    by case/norP => [cz1 cz2]; rewrite eq_m_m'.
  * pose P := [pred m' | m == m'].
    pose Q := [pred m' | `[<eqon (predC (mod c2)) m m'>]].
    apply (phl_conseq (P2 := P) (Q2 := Q)); last exact/ih2.
    - by move=> m' /= /andP [/eqP <-].
    move=> m' /asboolP eq_m_m'; apply/asboolP=> z.
    by case/norP => [cz1 cz2]; rewrite eq_m_m'.
+ move=> e c ihc m.
  pose P := ([pred m' | `[< eqon (~ mod c)%A m m' >]])%A.
  pose Q := ([pred m' | `[< eqon (~ mod c)%A m m' >]] /\ `[{~~ e}])%A.
  apply (phl_conseq (P2 := P) (Q2 := Q)).
  + by move=> m' /eqP <-; apply /asboolP.
  + by move=> m' /andP [].
  apply/phl_while=> m1 /andP[] /asboolP Hm1 _.
  apply: (@range_weaken _ [pred m' | `[< eqon (~ mod c)%A m1 m' >]]).
  + move=> x /asboolP eq_m1_x; apply/asboolP=> z Hz.
    by rewrite Hm1 // eq_m1_x.
  by apply (ihc m1)=> //=.
+ move=> c1 ih1 c2 ih2 m; eapply phl_seq; first by apply (ih1 m).
  move=> m1 /asboolP Hm1.
  apply: (@range_weaken _ [pred m' | `[< eqon (~ mod c2)%A m1 m' >]]).
  + move=> x /asboolP Hx; apply/asboolP=> z /=.
    by case/norP => [/= zc1 zc2]; rewrite Hm1 // Hx.
  by apply (ih2 m1) => /=.
Qed.

(* -------------------------------------------------------------------- *)
Lemma modll c mu m : lossless predT c ->
  \P_[mu]         [pred m' | `[<eqon (predC (mod c)) m m'>] ] =
  \P_[dssem c mu] [pred m' | `[<eqon (predC (mod c)) m m'>] ].
Proof.
move=> ll; rewrite pr_dlet pr_exp; apply/eq_exp => m' _.
apply/esym; rewrite !inE; case/boolP: (X in (_ X)%:R) => /= /asboolP h.
+ pose P := [pred m' | `[< eqon (~ mod c)%A m m' >]]; suff: phl P c P.
  - by move=> Hr; rewrite (phl_ll Hr) ?ll //; apply/asboolP.
  move=> m''; rewrite !inE => /asboolP eqm''.
  apply: (range_weaken (P1 := [pred m' | `[< eqon (~ mod c)%A m'' m' >]])).
  + by move=> m3 /asboolP eqm3; apply/asboolP; rewrite eqm''.
  by apply/mod_spec; rewrite inE.
+ rewrite (eq_in_pr (B := pred0)) ?pr_pred0 // => m''.
  move/mod_spec=> /(_ _ (eqxx _)) => /asboolP eq_m'_m''.
  by apply/asboolPn => eq_m_m''; apply/h; rewrite eq_m'_m''.
Qed.
