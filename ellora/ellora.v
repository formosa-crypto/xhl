(* -------------------------------------------------------------------- *)
(* ------- *)           Require Import Setoid Morphisms.
From mathcomp           Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.
From xhl.hl Require Import hl.

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
Local Notation iwhilen k b c := (iterc k (IfT b then c)).

(* -------------------------------------------------------------------- *)
Implicit Types P Q S : dassn.
Implicit Types c     : cmd.
Implicit Types mu    : dmem.

(* -------------------------------------------------------------------- *)
Definition detm (P : assn) :=
  [pred mu : dmem | `[< forall x, x \in dinsupp mu -> x \in P >]].

Definition oplus P Q (mu : dmem) :=
  exists2 smu : dmem * dmem,
    forall x, mu x = smu.1 x + smu.2 x & P smu.1 /\ Q smu.2.

Definition oplusb P Q :=
  [pred mu | `[< oplus P Q mu >]].

Notation "'□' P" := (detm P) (at level 20).
Notation "P ⊕ Q" := (oplusb P Q) (at level 40).

Lemma detmP (P : assn) mu :
  reflect (forall x, x \in dinsupp mu -> x \in P) (mu \in □ P).
Proof. by apply/asboolP. Qed.

Lemma oplusP P Q mu :
  reflect (oplus P Q mu) (mu \in P ⊕ Q).
Proof. by apply/asboolP. Qed.

(* -------------------------------------------------------------------- *)
Definition tclosed (P : nat -> dassn) (Pinf : dassn) :=
  forall (mu : nat -> dmem),
      (forall n, mu n \in P n)
   -> (forall x, exists l, ncvg (fun n => mu n x) l%:E)
   -> \dlim_(n) mu n \in Pinf.

(* -------------------------------------------------------------------- *)
Lemma tclosed_and (P Q : nat -> dassn) Pinf Qinf :
   tclosed P Pinf ->
   tclosed Q Qinf ->
   tclosed (fun n => P n /\ Q n)%A (Pinf /\ Qinf)%A.
Proof.
move=> cP cQ mu hmu hmu'; apply/andP; split.
+ by apply cP=> n //; case/andP: (hmu n).
+ by apply cQ=> n //; case/andP: (hmu n).  
Qed.

(* -------------------------------------------------------------------- *)
Lemma tclosed_square (P : assn) : tclosed (fun n => □ P)%A (□ P).
Proof.
move=> mu hmu mucvg; apply/detmP => m; case/dinsupp_dlim.
by move=> n mux; have/asboolP := hmu n => /(_ _ mux).
Qed.

(* -------------------------------------------------------------------- *)
Definition uclosed (P : nat -> dassn) (Pinf : dassn) :=
  forall (mu : nat -> dmem),
      (forall n, mu n \in P n)
   -> (forall n m, (n <= m)%N -> mu n <=1 mu m)
   -> \dlim_(n) mu n \in Pinf.

(* -------------------------------------------------------------------- *)
Lemma tclosed_uclosed (P : nat -> dassn) Pinf :
  tclosed P Pinf -> uclosed P Pinf.
Proof.
move=> uc mu h1 h2; apply/uc => // x; apply/ncvg_mono_bnd => [??/h2|] //.
apply/asboolP/nboundedP; exists 2%:R => // n; apply/(@le_lt_trans _ _ 1).
+ by rewrite ger0_norm ?(ge0_mu, le1_mu1). + by rewrite (@ltr_nat _ 1).
Qed.

(* -------------------------------------------------------------------- *)
Lemma uclosed_and (P Q : nat -> dassn) Pinf Qinf :
   uclosed P Pinf ->
   uclosed Q Qinf ->
   uclosed (fun n => P n /\ Q n)%A (Pinf /\ Qinf)%A.
Proof.
move=> cP cQ mu hmu hmu'; apply/andP; split.
+ by apply cP=> // n; case/andP: (hmu n).
+ by apply cQ=> // n; case/andP: (hmu n).  
Qed.

(* -------------------------------------------------------------------- *)
Lemma uclosed_square (P : assn) : uclosed (fun n => □ P)%A (□ P).
Proof. by apply/tclosed_uclosed/tclosed_square. Qed.

(* -------------------------------------------------------------------- *)
Definition tclosed0 P :=
   forall (mu : nat -> dmem),
      (forall n, mu n \in P)
    -> (forall x, exists l, ncvg (fun n => mu n x) l%:E)
   -> \dlim_(n) mu n \in P.

Definition dclosed P := tclosed0 P /\
  (forall mu, mu \in P -> forall mu', mu' <=1 mu -> mu' \in P).

(* -------------------------------------------------------------------- *)
Local Lemma Xclosed_while P b c : tclosed0 P ->
     (forall mu n, mu \in P -> dssem (whilen b c n.+1) mu \in P)
  -> (forall mu, mu \in P -> dssem (While b Do c) mu \in P).
Proof. move=> tcP h mu muP.
rewrite /dssem bsemE -dlim_let; first by apply/homo_whilen.
set F := (F in \dlim_(n) F n).
have ->: \dlim_(n) F n = \dlim_(n) F n.+1.
  by apply/distr_eqP=> m; rewrite dlim_bump.
rewrite {}/F; apply/tcP=> [|m]; first by move=> n; apply/h.
apply/ncvg_mono_bnd => [n p le_np|]; last first.
  apply/asboolP/nboundedP; exists 2%:R => // n.
  apply/(@le_lt_trans _ _ 1); last by rewrite (@ltr_nat _ 1).
  by rewrite ger0_norm ?(ge0_mu, le1_mu1).
by apply/le_in_dlet=> {}m _ m'; apply/homo_whilen.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma Xclosed_iterc P b c n:
     (forall mu, mu \in P -> dssem (IfT b then c) mu \in P)
  -> (forall mu, mu \in P -> dssem (iterc n (IfT b then c)) mu \in P).
Proof.
move=> h mu muP; rewrite ssem_iterop_iter.
elim: n mu muP => [|n ihn] mu muP /=.
  by rewrite /dssem bsemE dlet_dunit_id.
by rewrite /dssem bsemE -dlet_dlet; apply/ihn/h.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dclosed_while P b c : dclosed P ->
     (forall mu, mu \in P -> dssem (IfT b then c) mu \in P)
  -> (forall mu, mu \in P -> dssem (While b Do c) mu \in P).
Proof.
move=> [tcP dwP] h mu muP; apply/Xclosed_while => // {muP} mu n muP.
rewrite whilen_iterc; set cn := iterc _ _.
move/(_ (dssem cn mu)): dwP; apply; first by apply/Xclosed_iterc.
move=> m; apply/le_in_dlet=> {}m _ m'; rewrite ssemE.
rewrite -[X in _ <= _ X _]dlet_dunit_id; apply/le_in_dlet.
move=> {m'} m _ m'; rewrite ssemE; case: ifP=> _.
  by rewrite ssemE; apply/lef_dnull. by rewrite ssemE.
Qed.

(* -------------------------------------------------------------------- *)
Definition dassn_map P (F : dmem -> dmem) mu := (F mu \in P).

Arguments dassn_map : simpl never.

Notation "P .[ F ]" := (dassn_map P F) : assn.

(* -------------------------------------------------------------------- *)
Definition ellora P Q c :=
  forall mu, mu \in P -> dssem c mu \in Q.

Arguments ellora P%_A Q%_A c.

(* -------------------------------------------------------------------- *)
Lemma ellora_skip P : ellora P P skip.
Proof. by move=> mu; rewrite /dssem bsemE dlet_dunit_id. Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_abort P : ellora P (□ pred0) abort.
Proof.
move=> mu _; rewrite /dssem bsemE; apply/detmP=> m; apply/contraLR=> _.
by apply/dinsuppPn; rewrite dletC dnullE mulr0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_seq S P Q c1 c2 :
  ellora P S c1 -> ellora S Q c2 -> ellora P Q (c1 ;; c2).
Proof. by move=> e1 e2 mu /e1 /e2; rewrite /dssem bsemE dlet_dlet. Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_conseq P' Q' P Q c :
    (forall mu, mu \in P  -> mu \in P')
  -> (forall mu, mu \in Q' -> mu \in Q )
  -> ellora P' Q' c
  -> ellora P  Q  c.
Proof. by move=> hP hQ h mu /hP /h /hQ. Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_sem c1 P Q c2 :
    (forall mu, mu \in P -> dssem c1 mu = dssem c2 mu)
  -> ellora P Q c1 -> ellora P Q c2.
Proof. by move=> eq h mu Pmu; have := h _ Pmu; rewrite eq. Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_and P Q1 Q2 c :
  ellora P Q1 c -> ellora P Q2 c -> ellora P (Q1 /\ Q2) c.
Proof.
move=> h1 h2 mu muP; apply/andP; split.
  by apply/h1. by apply/h2.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_or P1 P2 c Q :
  ellora P1 Q c -> ellora P2 Q c -> ellora (P1 \/ P2)%A Q c.
Proof. by move=> h1 h2 mu /orP[/h1|/h2]. Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_sem_condT P Q (e : expr bool) c1 c2 :
  (forall mu, mu \in P -> forall m, m \in dinsupp mu -> `[{ e }] m)
  -> ellora P Q c1 -> ellora P Q (If e then c1 else c2).
Proof.
move=> h; apply/ellora_sem=> mu /h em; apply/eq_in_dlet=> //.
by move=> m /em; rewrite !ssemE => ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_sem_condF P Q (e : expr bool) c1 c2 :
  (forall mu, mu \in P -> forall m, m \in dinsupp mu -> `[{ ~~ e }] m)
  -> ellora P Q c2 -> ellora P Q (If e then c1 else c2).
Proof.
move=> h; apply/ellora_sem=> mu /h em; apply/eq_in_dlet=> //.
by move=> m /em; rewrite !ssemE => /negbTE ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_split P P' Q Q' c :
  ellora P Q c -> ellora P' Q' c -> ellora (P ⊕ P') (Q ⊕ Q') c.
Proof.
move=> h1 h2 mu /oplusP[] [mu1 mu2] /= muE []  /h1 hQ1 /h2 hQ2.
apply/oplusP; exists (dssem c mu1, dssem c mu2)=> /=; last by split.
by move=> m; apply/dlet_additive.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_cond P P' Q Q' e c1 c2 :
  let SP := (P /\ □ [pred m | `[{    e }] m])%A in
  let SQ := (Q /\ □ [pred m | `[{ ~~ e }] m])%A in

     ellora SP P' c1
  -> ellora SQ Q' c2
  -> ellora (SP ⊕ SQ) (P' ⊕ Q') (If e then c1 else c2).
Proof.
move=> SP SQ hP hQ; apply/ellora_split.
+ by apply/ellora_sem_condT=> // mu /andP[_] /detmP.
+ by apply/ellora_sem_condF=> // mu /andP[_] /detmP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_semmap P c : ellora P.[fun mu => dssem c mu] P c.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_cond b c :
  ellora (□ predT) (□ `[{~~ b}]) (While b Do c).
Proof.
move=> mu _; apply/detmP=> m; rewrite /dssem bsemE => /dinsupp_dlet[m' _].
rewrite dlimE; apply/contra=> bm; pose u0 := fun _ : nat => 0 : R.
rewrite (@eq_nlim _ u0) ?nlimC // {}/u0 => n; elim: n m' => [|n ihn].
  by move=> m'; rewrite ssemE dnullE.
move=> m'; rewrite ssemE; case: ifP=> bm'; rewrite !ssemE.
  by unlock dlet; rewrite /= /mlet psum_eq0 // => m''; rewrite ihn mulr0.
by rewrite dunit1E (rwP eqP) pnatr_eq0 eqb0; apply/contraFN: bm' => /eqP->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_dclosed P b c :
  dclosed P -> ellora P P (IfT b then c)
    -> ellora P (P /\ □ `[{~~ b}]) (While b Do c).
Proof.
move=> dcP hIf; apply/ellora_and; first by apply/dclosed_while.
apply/(ellora_conseq _ _ (ellora_while_cond _ _)) => //.
by move=> mu _; apply/detmP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_uclosed (P Q : nat -> dassn) Qinf b c :
     (forall n, ellora (P n) (P n.+1) (IfT b then c))
  -> (forall n, ellora (P n) (Q n) (IfT b then abort))
  -> uclosed Q Qinf
  -> ellora (P 0)%N (Qinf /\ □ `[{~~ b}]) (While b Do c).
Proof. 
move=> hP hQ Quclosed mu P0_mu.
rewrite /dssem bsemE -dlim_let; first by apply/homo_whilen.
pose F n := \dlet_(x <- mu) ssem (whilen b c n) x.
have ->: \dlim_(n) F n = \dlim_(n) F n.+1.
+ by apply/distr_eqP=> m; rewrite dlim_bump.
apply: (uclosed_and Quclosed (@uclosed_square (`[{~~ b}])%A)).
+ move=> n; pose R := ssem (iwhilen n b c ;; IfT b then abort).
  rewrite [X in X \in _](_ : _ = \dlet_(x <- mu) R x) {}/R {}/F.
  * by apply eq_in_dlet => // m _; rewrite whilen_iterc.
  move: P0_mu; rewrite -(subnn n); move: mu (leqnn n).
  elim: {1 4 5}n => [|m ihm] mu Hn.
  * rewrite [dlet _ _](_ : _ = \dlet_(x <- mu) ssem (IfT b then abort) x).
    - by apply eq_in_dlet=> // m _;rewrite iterc0 !bsemE dlet_unit.
    rewrite subn0 => Pmu_nl; apply/(ellora_and (hQ n)) => //.
    move=> m _; apply/asboolP => m' /dinsupp_dlet [y] Hy.
    rewrite !bsemE; case: ifPn; first by rewrite dnullE eqxx.
    by rewrite dunit1E pnatr_eq0 eqb0 negbK => ? /eqP<-.
  move=> PS_mu; pose d := \dlet_(x <- mu) ssem (IfT b then c) x.
  pose R x := ssem (iterc m (IfT b then c) ;; IfT b then abort) x.
  rewrite [dlet _ _](_ : _ = \dlet_(x <- d) R x) {}/R {}/d.
  + rewrite dlet_dlet; apply eq_in_dlet=> // m1 _.
    by rewrite ssem_seqE itercSl -ssem_seqE sem_seqA ssem_seqE.
  apply ihm; first by apply ltnW. by rewrite -subnSK //; apply hP. 
move=> n m le_mn x; rewrite {}/F; apply/le_dlet=> // y _ z.
by apply/homo_whilen.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_tclosed (P Q : nat -> dassn) Qinf b c :
     (forall n, ellora (P n) (P n.+1) (IfT b then c))
  -> (forall n, ellora (P n) (Q n) (IfT b then abort))
  -> tclosed Q Qinf
  -> ellora (P 0)%N (Qinf /\ □ `[{~~ b}]) (While b Do c).
Proof. 
move=> h1 h2 uc; apply/ellora_while_uclosed => //.
by apply/tclosed_uclosed.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_certain_ct P b c :
    (forall mu, mu \in P -> exists k,
       \P_[dssem (iwhilen k b c) mu] [eta `[{ b }]] = 0)
  -> ellora P P (IfT b then c)
  -> ellora P (P /\ □ `[{ ~~ b}]) (While b Do c).
Proof.
move=> ct hIf; apply/ellora_and; last first.
  apply/(ellora_conseq _ _ (ellora_while_cond _ _)) => //.
  by move=> mu _; apply/detmP.
move=> mu muP; case/(_ _ muP): ct => k ct.
suff ->: dssem (While b Do c) mu = dssem (iwhilen k b c) mu.
  by apply/Xclosed_iterc.
apply/eq_in_dlet=> // m m_in_mu; rewrite (unrolln_while k).
apply/distr_eqP=> m'; rewrite -[X in _ = _ X _]dlet_dunit_id.
rewrite ssemE; apply/distr_eqP: m'; apply/eq_in_dlet=> //.
move=> m' hm'; rewrite ssem_while0 //; apply/negP=> bm'.
have: m' \in dinsupp (dssem (iwhilen k b c) mu).
  apply/dinsuppP; rewrite /dssem => /eq0_dlet /(_ _ m_in_mu).
  by move/dinsuppP=> -/(_ hm').
by move/pr_eq0: ct => /(_ _ bm') /dinsuppP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_certain (P : nat -> dassn) k e c :
     (forall n, ellora (P n) (P n.+1) (IfT e then c))
  -> (forall mu, P 0%N mu -> dssem (While e Do c) =
                             dssem (iterc k (IfT e then c)))
  -> ellora (P 0%N) (P k /\ □ `[{~~ e}]) (While e Do c).
Proof.
move=> el ds mu P0_mu; rewrite (ds _ P0_mu); apply/andP; split.
+ elim: {ds} k => [|k ih]; first by rewrite iterc0 dssem_skipE.
  by move/el: ih; rewrite -dssem_seqE -itercSr.
apply/detmP=> m; rewrite -(ds mu) //; case/dinsupp_dlet.
move=> m' _; rewrite ssemE -(funext (dlim_bump _)).
case/dinsupp_dlim=> p; rewrite whilen_iterc bsemE.
case/dinsupp_dlet=> m'' _; rewrite !bsemE; case: ifPn.
+ by move=> _; rewrite dnullE eqxx.
+ by move=> ne; rewrite dunit1E pnatr_eq0 eqb0 negbK => /eqP<-.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_frame P c :
  separated (mod c) P -> lossless predT c -> ellora P P c.
Proof. by move=> spc llc mu; apply/spc=> m; apply/modll. Qed.

(* -------------------------------------------------------------------- *)
Hint Resolve ellora_skip             : ellora.
Hint Resolve ellora_abort            : ellora.
Hint Resolve ellora_seq              : ellora.
Hint Resolve ellora_conseq           : ellora.
Hint Resolve ellora_sem              : ellora.
Hint Resolve ellora_and              : ellora.
Hint Resolve ellora_or               : ellora.
Hint Resolve ellora_sem_condT        : ellora.
Hint Resolve ellora_sem_condF        : ellora.
Hint Resolve ellora_split            : ellora.
Hint Resolve ellora_cond             : ellora.
Hint Resolve ellora_semmap           : ellora.
Hint Resolve ellora_while_cond       : ellora.
Hint Resolve ellora_while_dclosed    : ellora.
Hint Resolve ellora_while_tclosed    : ellora.
Hint Resolve ellora_while_uclosed    : ellora.
Hint Resolve ellora_while_certain    : ellora.
Hint Resolve ellora_while_certain_ct : ellora.
Hint Resolve ellora_frame            : ellora.
