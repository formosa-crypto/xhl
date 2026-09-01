(* -------------------------------------------------------------------- *)
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp filter.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import counting_distr ereal.
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
Local Notation dmem  := (Distr cmem).
Local Notation dassn := (pred  dmem).
Local Notation dassn2 := (dmem -> dassn).

Implicit Types P Q S : dassn.
Implicit Types c : cmd.
Implicit Types mu : dmem.

(* -------------------------------------------------------------------- *)
(* Ellora triple                                               *)
(* -------------------------------------------------------------------- *)

Definition ellora_ ps P Q c :=
  forall mu, mu \in P -> dssem ps c mu \in Q.

Arguments ellora_ ps P%_A Q%_A c.

(* -------------------------------------------------------------------- *)
(* Generic ellora triple                                                 *)
(* -------------------------------------------------------------------- *)

Definition kellora_ (ps: psi) (P : dassn) (Q : dassn2) (c : cmd) :=
    forall mu, mu \in P -> dssem ps c mu \in (Q mu).

Arguments kellora_ ps P%_A Q%_A c.

Local Notation eqmu mu :=
  (fun x => `[< x = mu >]).

Lemma kellora_ellora ps P c (Q: dassn2) :
  kellora_ ps P Q c <-> (forall s0, ellora_ ps (eqmu s0) (fun s => P s0 ==> Q s0 s) c).
Proof.
  split.
  + move=> h s0 s /asboolP <-.
    apply /implyP => HP.
    by apply h.
  + move=> h s hP.
    have /implyP H : dssem ps c s \in (fun t => P s ==> Q s t)
      by apply: (h s s); apply/asboolP.
    exact: (H hP).
Qed.

Lemma ellora_kellora ps P c Q :
  kellora_ ps P (fun _ => Q) c <-> ellora_ ps P Q c.
Proof.
  by split; move => h s hP; apply h.
Qed.

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
   -> (forall x, cvgn (fun n => (mu n x)%:E)) (* pointwise convergent *)
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
   -> (forall n m, (n <= m)%N -> mu n <=1 mu m) (* pointwise nondecreasing *)
   -> \dlim_(n) mu n \in Pinf.

(* -------------------------------------------------------------------- *)
Lemma tclosed_uclosed (P : nat -> dassn) Pinf :
  tclosed P Pinf -> uclosed P Pinf.
Proof.
by move=> uc mu h1 h2; apply/uc => // x; apply: cvg_dlim; exact: dhomo_dnd h2.
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
   -> (forall x, cvgn (fun n => (mu n x)%:E))
   -> \dlim_(n) mu n \in P.

Definition dclosed P := tclosed0 P /\
  (forall mu, mu \in P -> forall mu', mu' <=1 mu -> mu' \in P).

(* -------------------------------------------------------------------- *)
Local Lemma Xclosed_while P b c ps : tclosed0 P ->
    (forall mu n, mu \in P -> dssem ps (whilen b c n.+1) mu \in P)
  -> (forall mu, mu \in P -> dssem ps (While b Do c) mu \in P).
Proof. move=> tcP h mu muP.
rewrite /dssem bsemE -dlim_let; first by apply/homo_whilen.
set F := (F in \dlim_(n) F n).
have ->: \dlim_(n) F n = \dlim_(n) F n.+1.
  by apply/distr_eqP=> m; rewrite dlim_bump.
rewrite {}/F; apply/tcP=> [|x]; first by move=> n; apply/h.
apply: cvg_dlim; apply/dhomo_dnd => n p le_np m'.
by apply/le_in_dlet=> {}m _ m''; apply/homo_whilen.
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma Xclosed_iterc P b c n ps:
     (forall mu, mu \in P -> dssem ps (IfT b then c) mu \in P)
  -> (forall mu, mu \in P -> dssem ps (iterc n (IfT b then c)) mu \in P).
Proof.
move=> h mu muP; rewrite ssem_iterop_iter.
elim: n mu muP => [|n ihn] mu muP /=.
  by rewrite /dssem bsemE dlet_dunit_id.
by rewrite /dssem bsemE -dlet_dlet; apply/ihn/h.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dclosed_while P b c ps: dclosed P ->
     (forall mu, mu \in P -> dssem ps (IfT b then c) mu \in P)
  -> (forall mu, mu \in P -> dssem ps (While b Do c) mu \in P).
Proof.
move=> [tcP dwP] h mu muP; apply/Xclosed_while => // {muP} mu n muP.
rewrite whilen_iterc; set cn := iterc _ _.
move/(_ (dssem ps cn mu)): dwP; apply; first by apply/Xclosed_iterc.
move=> m; apply/le_in_dlet=> {}m _ m'; rewrite ssemE.
rewrite -[X in _ <= _ X _]dlet_dunit_id; apply/le_in_dlet.
move=> {m'} m _ m'; rewrite ssemE; case: ifP=> _.
  by rewrite ssemE; apply/lef_dnull. by rewrite ssemE.
Qed.

(* -------------------------------------------------------------------- *)
Definition dassn_map P (F : dmem -> dmem) mu := (F mu \in P).

Arguments dassn_map : simpl never.

Notation "P .[ F ]" := (dassn_map P F) : assn.

Notation psi := (ident -> cmd_ ident cmem ident).

(* -------------------------------------------------------------------- *)
Local Notation iwhilen k b c := (iterc k (IfT b then c)).

(* -------------------------------------------------------------------- *)
Section Logic.

Definition post_shift (post : nat -> dassn2) n : dassn2 :=
 if n is n'.+1 then post n' else (fun _ => eqmu dnull).

Inductive sellora : psi -> (ident -> dassn) -> (ident -> dassn2) -> dassn -> dassn -> cmd -> Prop :=
| EAbort P pre post ps : sellora ps pre post P (□ pred0) abort

| ESkip P pre post  ps : sellora ps pre post P P skip

| EAssign {t : IhbType.type} P (x : vars t) (e : expr t) pre post ps:
    sellora ps pre post (P.[fun mu => dssem ps (x <<- e) mu])%A P (x <<- e)

| EGAssign {t : IhbType.type} P (x : vars t) (e : expr t) pre post ps:
    sellora ps pre post (P.[fun mu => dssem ps (G x <<- e) mu])%A P (G x <<- e)

| ESample {t : IhbType.type} P (x : vars t) (d : dexpr t) pre post ps:
    sellora ps pre post (P.[fun mu => dssem ps (x <$- d) mu])%A P (x <$- d)

| ECond P P' Q Q' e c1 c2 ps pre post :
    let SP := (P /\ □ [pred m | `[{    e }] m])%A in
    let SQ := (Q /\ □ [pred m | `[{ ~~ e }] m])%A in
    sellora ps pre post SP P' c1
    -> sellora ps pre post SQ Q' c2
    -> sellora ps pre post (SP ⊕ SQ) (P' ⊕ Q') (If e then c1 else c2)

| EWhileTClosed (P Q : nat -> dassn) Qinf b c pre post ps :
       (forall n, sellora ps pre post (P n) (P n.+1) (IfT b then c))
    -> (forall n, sellora ps pre post (P n) (Q n) (IfT b then abort))
    -> tclosed Q Qinf
    -> sellora ps pre post (P 0%N) (Qinf /\ □ `[{~~ b}])%A (While b Do c)

| ESeq S P Q c1 c2 pre post ps :
  sellora ps pre post P S c1 ->
  sellora ps pre post S Q c2 ->
  sellora ps pre post P Q (c1 ;; c2)

| EConseq P' Q' P Q c pre post ps :
       (forall mu, mu \in P  -> mu \in P')
    -> (forall mu, mu \in Q' -> mu \in Q )
    -> sellora ps pre post P' Q' c
    -> sellora ps pre post P  Q  c

| H_khl : forall P Q c pre post ps,
     sellora2 ps pre post P (fun _ => Q) c -> sellora ps pre post P Q c
with sellora2: psi -> (ident -> dassn) -> (ident -> dassn2) -> dassn -> dassn2 -> cmd -> Prop :=
   | H_hl: forall P (Q:dassn2) c pre post ps,
       (forall s0, sellora ps pre post (eqmu s0) (fun s => P s0 ==> Q s0 s) c) ->
       sellora2 ps pre post P Q c
   | EBlock : forall (F : cmem -> dmem) bs c rs pre post ps,
       (forall m, sellora ps pre post (eqmu (dunit (minit m bs))) (eqmu (F m)) c) ->
       sellora2 ps pre post xpredT
         (fun mu => eqmu (\dlet_(m <- mu) \dlet_(m' <- F m) dunit (mret m m' rs)))
         (block bs c rs)
   | H_call : forall pre post f ps, sellora2 ps pre post (pre f) (post f) (call f)
   | H_rec : forall P (Q: dassn2) c pre postinf pre' postinf' post ps',
       (forall p s, tclosed (fun n => post_shift (post p) n s)  (postinf p s)) ->
       (forall p' ps n , sellora2 ps pre
                      (fun f => post_shift (post f) n) (pre p')
                      (post p' n) (ps' p')) ->
       (forall ps, sellora2 ps pre postinf P Q c) ->
       sellora2 ps' pre' postinf' P Q c
   | H_adapt : forall (P1 P2 : dassn) (Q1 Q2 : dassn2) c pre post ps,
       (forall m, P1 m -> P2 m) ->
       (forall m0, P1 m0 -> forall m, Q2 m0 m -> Q1 m0 m) ->
       sellora2 ps pre post P2 Q2 c -> sellora2 ps pre post P1 Q1 c.

Scheme derivable_min := Minimality for sellora Sort Prop
  with derivable2_min := Minimality for sellora2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

End Logic.

Section Sound.

Section Rules.
Context (ps: psi).

Notation ellora   := (ellora_ ps).
Notation kellora   := (kellora_ ps).

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
    (forall mu, mu \in P -> dssem ps c1 mu = dssem ps c2 mu)
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
apply/oplusP; exists (dssem ps c mu1, dssem ps c mu2)=> /=; last by split.
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
Lemma ellora_semmap P c : ellora P.[fun mu => dssem ps c mu] P c.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_block (F : cmem -> dmem) bs c rs :
  (forall m, ellora (eqmu (dunit (minit m bs))) (eqmu (F m)) c) ->
  kellora xpredT
    (fun mu => eqmu (\dlet_(m <- mu) \dlet_(m' <- F m) dunit (mret m m' rs)))
    (block bs c rs).
Proof.
move=> H mu _; apply/asboolP; rewrite /dssem.
apply/eq_in_dlet => // m _; rewrite ssem_blockE.
have /asboolP : dssem ps c (dunit (minit m bs)) \in eqmu (F m).
  by apply: H; apply/asboolP.
by rewrite /dssem dlet_unit => ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_cond b c :
  ellora (□ predT) (□ `[{~~ b}]) (While b Do c).
Proof.
move=> mu _; apply/detmP=> m; rewrite /dssem => /dinsupp_dlet[m' _].
rewrite ssem_whileE; case/dinsupp_dlim=> -[|p].
+ by rewrite /= ssem_abortE in_dinsupp dnullE eqxx.
rewrite whilen_iterc ssem_seqE => /dinsupp_dlet[m'' _].
rewrite ssem_ifE; case: ifPn.
+ by move=> _; rewrite ssem_abortE dnullE eqxx.
by move=> ne; rewrite ssem_skipE dunit1E pnatr_eq0 eqb0 negbK => /eqP<-.
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
pose F n := \dlet_(x <- mu) ssem ps (whilen b c n) x.
have ->: \dlim_(n) F n = \dlim_(n) F n.+1.
+ by apply/distr_eqP=> m; rewrite dlim_bump.
apply: (uclosed_and Quclosed (@uclosed_square (`[{~~ b}])%A)).
+ move=> n; pose R := ssem ps (iwhilen n b c ;; IfT b then abort).
  rewrite [X in X \in _](_ : _ = \dlet_(x <- mu) R x) {}/R {}/F.
  * by apply eq_in_dlet => // m _; rewrite whilen_iterc.
  move: P0_mu; rewrite -(subnn n); move: mu (leqnn n).
  elim: {1 4 5}n => [|m ihm] mu Hn.
  * rewrite [dlet _ _](_ : _ = \dlet_(x <- mu) ssem ps (IfT b then abort) x).
    - by apply eq_in_dlet=> // m _;rewrite iterc0 !bsemE dlet_unit.
    rewrite subn0 => Pmu_nl; apply/(ellora_and (hQ n)) => //.
    move=> m _; apply/asboolP => m' /dinsupp_dlet [y] Hy.
    rewrite !bsemE; case: ifPn; first by rewrite dnullE eqxx.
    by rewrite dunit1E pnatr_eq0 eqb0 negbK => ? /eqP<-.
  move=> PS_mu; pose d := \dlet_(x <- mu) ssem ps (IfT b then c) x.
  pose R x := ssem ps (iterc m (IfT b then c) ;; IfT b then abort) x.
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
       \P_[dssem ps (iwhilen k b c) mu] [eta `[{ b }]] = 0)
  -> ellora P P (IfT b then c)
  -> ellora P (P /\ □ `[{ ~~ b}]) (While b Do c).
Proof.
move=> ct hIf; apply/ellora_and; last first.
  apply/(ellora_conseq _ _ (ellora_while_cond _ _)) => //.
  by move=> mu _; apply/detmP.
move=> mu muP; case/(_ _ muP): ct => k ct.
suff ->: dssem ps (While b Do c) mu = dssem ps (iwhilen k b c) mu.
  by apply/Xclosed_iterc.
apply/eq_in_dlet=> // m m_in_mu; rewrite (unrolln_while k).
apply/distr_eqP=> m'; rewrite -[X in _ = _ X _]dlet_dunit_id.
rewrite ssemE; apply/distr_eqP: m'; apply/eq_in_dlet=> //.
move=> m' hm'; rewrite ssem_while0 //; apply/negP=> bm'.
have: m' \in dinsupp (dssem ps (iwhilen k b c) mu).
  apply/dinsuppP; rewrite /dssem => /eq0_dlet /(_ _ m_in_mu).
  by move/dinsuppP=> -/(_ hm').
by move/pr_eq0: ct => /(_ _ bm') /dinsuppP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_while_certain (P : nat -> dassn) k e c :
     (forall n, ellora (P n) (P n.+1) (IfT e then c))
  -> (forall mu, P 0%N mu -> dssem ps (While e Do c) =
                             dssem ps (iterc k (IfT e then c)))
  -> ellora (P 0%N) (P k /\ □ `[{~~ e}]) (While e Do c).
Proof.
move=> el ds mu P0_mu; rewrite (ds _ P0_mu); apply/andP; split.
+ elim: {ds} k => [|k ih]; first by rewrite iterc0 dssem_skipE.
  by move/el: ih; rewrite -dssem_seqE -itercSr.
apply/detmP=> m; rewrite -(ds mu) //; case/dinsupp_dlet.
move=> m' _; rewrite ssem_whileE; case/dinsupp_dlim=> -[|p].
+ by rewrite /= ssem_abortE in_dinsupp dnullE eqxx.
rewrite whilen_iterc ssem_seqE => /dinsupp_dlet[m'' _].
rewrite ssem_ifE; case: ifPn.
+ by move=> _; rewrite ssem_abortE dnullE eqxx.
by move=> ne; rewrite ssem_skipE dunit1E pnatr_eq0 eqb0 negbK => /eqP<-.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ellora_frame P c :
  nocall c ->
  separated (mod c) P -> lossless predT c -> ellora P P c.
Proof. by move=> hc spc llc mu; apply/spc=> m; apply/modll. Qed.

(* -------------------------------------------------------------------- *)

(** Hoare triple for a com with procedure context **)

Definition ellora_triple_ctx (pre : ident -> dassn)
                             (post : ident -> dassn2)
                             (ps: psi) (P: dassn) (Q: dassn2) (c: cmd) :=
 (forall p, kellora_ ps (pre p) (post p) (call p)) -> kellora_ ps P Q c.

(** Hoare triple for a procedure with procedure context **)

Definition ellora_triple_proc_ctx (pre : ident -> dassn)
                                  (post : ident -> nat -> dassn2)
                                  (ps_init :psi):=
  forall p ps n, ellora_triple_ctx
              pre
              (fun f => post_shift (post f) n)
              ps
              (pre p)
              (post p n)
              (ps_init p).

Lemma recursive_proc  (ps': psi)
                      (pre : ident -> dassn)
                      (post : ident -> nat -> dassn2)
                      (postinf : ident -> dassn2)  :
  (forall p s, tclosed (fun n => post_shift (post p) n s)  (postinf p s)) ->
    ellora_triple_proc_ctx pre post ps' ->
  (forall p, kellora_ ps' (pre p) (postinf p) (call p)).
Proof.
move=> Htclosed Hstep.
(* term-wise identification of the k_inliner and ubnf approximations *)
have KU : forall n c m, ssem_ (k_inliner_ps1 n ps') c m = ssem_aux (ubnf ps' n) c m.
  by move=> n c m; rewrite ssem_aux_ssem_.
(* each finite approximation satisfies the shifted contract, by induction *)
have key : forall n p s, s \in pre p ->
    dssem (k_inliner_ps1 n ps') (call p) s \in post_shift (post p) n s.
  elim => [|n IHn] p s hP.
  - have -> : dssem (k_inliner_ps1 0 ps') (call p) s = dnull.
      rewrite /dssem; transitivity (\dlet_(m0 <- s) (dnull : Distr cmem)).
        by apply/eq_in_dlet => // m0 _; rewrite KU /=.
      by apply/distr_eqP => x; rewrite dletC dnullE mulr0.
    by rewrite /post_shift; apply/asboolP.
  - have -> : dssem (k_inliner_ps1 n.+1 ps') (call p) s
            = dssem (k_inliner_ps1 n ps') (ps' p) s.
      by rewrite /dssem; apply/eq_in_dlet => // m0 _; rewrite (inline2_split n 1).
    apply: (Hstep p (k_inliner_ps1 n ps') n); last exact: hP.
    by move=> p0 s0 hP0; exact: (IHn _ _ hP0).
move=> p s hP.
(* monotonicity of the approximation in the depth *)
have mono : forall m0 n1 n2, (n1 <= n2)%N ->
    ssem_ (k_inliner_ps1 n1 ps') (call p) m0
      <=1 ssem_ (k_inliner_ps1 n2 ps') (call p) m0.
  move=> m0 n1 n2 le; rewrite !KU.
  by apply: mono_ssem_aux; exact: (homo_ubnf le).
have monoD : forall n1 n2, (n1 <= n2)%N ->
    dssem (k_inliner_ps1 n1 ps') (call p) s
      <=1 dssem (k_inliner_ps1 n2 ps') (call p) s.
  by move=> n1 n2 le; rewrite /dssem; apply/le_in_dlet => m0 _; exact: (mono m0 n1 n2 le).
(* the real call is the limit of its finite approximations *)
have E : dssem ps' (call p) s = \dlim_(n) dssem (k_inliner_ps1 n ps') (call p) s.
  rewrite /dssem [RHS]dlim_let; first by move=> x n1 n2 le; exact: (mono x n1 n2 le).
  by apply/eq_in_dlet => // m0 _; rewrite dlim_inliner_ssem.
rewrite E; apply: (Htclosed p s).
- by move=> n; apply: key.
- move=> x; apply: cvg_dlim; apply/dhomo_dnd => n1 n2 le.
  exact: (monoD n1 n2 le).
Qed.

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple :
  forall P (Q:dassn2) c
    (pre : ident -> dassn)
    (post : ident -> nat -> dassn2)
    (postinf : ident -> dassn2)  ,
    (forall p s, tclosed (fun n => post_shift (post p) n s)  (postinf p s)) ->
    ellora_triple_proc_ctx pre post ps  ->
    ellora_triple_ctx pre postinf ps P Q c ->
    kellora P Q c.
Proof.
move=> P Q c pre post postinf Htcl Hproc Hc.
by apply: Hc; apply: recursive_proc; [exact: Htcl | exact: Hproc].
Qed.

End Rules.

(* -------------------------------------------------------------------- *)
Hint Resolve ellora_abort            : ellora.
Hint Resolve ellora_skip             : ellora.
(* [ellora_semmap] is the pullback rule for an arbitrary [c]: it is what
 * discharges assign / gassign / sample alike, so it sits with them. *)
Hint Resolve ellora_semmap           : ellora.
Hint Resolve ellora_cond             : ellora.
Hint Resolve ellora_while_tclosed    : ellora.
Hint Resolve ellora_seq              : ellora.
(* structural, not syntax-directed *)
Hint Resolve ellora_sem              : ellora.
Hint Resolve ellora_conseq           : ellora.

Definition valid_cl pre post (ps:psi) :=
  forall f, kellora_ ps (pre f) (post f) (call f).

Lemma soundness:
  (forall ps pre post (P Q:dassn) c,
      sellora ps pre post P Q c -> valid_cl pre post ps -> ellora_ ps P Q c) /\
    (forall ps pre post (P: dassn) (Q: dassn2) c,
      sellora2 ps pre post P Q c -> valid_cl pre post ps -> kellora_ ps P Q c).
Proof.
apply derivable_mut.
+ (* EAbort *) eauto 2 using ellora_cond with ellora.
+ (* ESkip *) eauto 2 using ellora_cond with ellora.
+ (* EAssign *) eauto 2 using ellora_cond with ellora.
+ (* EGAssign *) by move => *; apply: ellora_semmap.
+ (* ESample *) eauto 2 using ellora_cond with ellora.
+ (* ECond *)
  move => P P' Q Q' e c1 c2 ps ????? Hc1 ? Hc2 Hv.
  by apply: ellora_cond;[ exact: (Hc1 Hv) | exact: (Hc2 Hv)].
+ (* EWhileTClosed *)
  move =>  P Q Qinf b c ?? ps ? HI ? Ha Hclose Hv.
  apply: ellora_while_tclosed.
  + move => n.  by apply: HI.
  + move => n.  by apply: Ha.
  + exact: Hclose.
+ (* ESeq *)
  move => S P Q c1 c2 pre post ps ? Hc1 ? Hc2 Hv.
  apply: ellora_seq;[exact: Hc1 | exact: Hc2].
+ (* EConseq *)
  move => P' Q' P Q c pre post ps HP HQ ? HI Hv m HPre.
  apply: HQ.
  apply: (HI Hv).
  by apply: HP.
+ (* H_khl *) eauto 2 using ellora_cond with ellora.
+ (* H_hl *)
  move => P Q c cl ps ?? HI Hv.
  apply /kellora_ellora.
  by move => s0; apply HI.
+ (* EBlock *)
  move => F bs c rs pre post ps ? IH Hv.
  by apply: ellora_block => m; exact: IH.
+ (* H_call *) move => ?? f ps Hv. exact: (Hv f).
+ (* H_rec *)
  move => P Q c pre postinf pre' postinf' post ps' Hclose ? Hf ? IHc Hv.
  apply: recursion_hoare_triple.
  - exact: Hclose.
  - by move=> p ps n Hpre; exact: (Hf p ps n Hpre).
  - by move=> Hcall; exact: (IHc ps' Hcall).
+ (* H_adapt *)
  move => P1 p2 Q1 Q2 c ?? ps HP HQ ? HI Hv m HPre.
  have := (HI Hv m (HP m HPre)).
  exact: HQ.
Qed.

Corollary ellora_sound0 P c Q ps :
  sellora ps (fun _ => xpredT) (fun _ _ => xpredT) P Q c -> ellora_ ps P Q c.
Proof.
  move => Hd; exact: (proj1 soundness _ (fun _ => xpredT) (fun _ _ => xpredT)).
Qed.

Corollary kellora_sound0 P c (Q:dassn2) ps :
  sellora2 ps (fun _ => xpredT) (fun _ _ => xpredT) P Q c -> kellora_ ps P Q c.
Proof.
  move => Hd;  exact: (proj2 soundness _ (fun _ => xpredT) (fun _ _ => xpredT)).
Qed.

End Sound.

Section Complete.

Definition iscomplete' ps pre post (c:cmd) (Q: dmem -> dassn):=
  (forall mu, sellora ps pre post (eqmu mu) (Q mu) c).

Lemma rel_cpl_skip pre post (ps ps' : psi) mu :
  sellora ps pre post (eqmu mu) (eqmu (dssem ps' skip mu)) skip.
Proof.
apply/(@EConseq (eqmu mu) (eqmu mu)) => //.
+ by move=> nu /asboolP ->; apply/asboolP; rewrite dssem_skipE.
by apply/ESkip.
Qed.

Lemma rel_cpl_abort pre post (ps ps' : psi) mu :
  sellora ps pre post (eqmu mu) (eqmu (dssem ps' abort mu)) abort.
Proof.
apply/(@EConseq (eqmu mu) (□ pred0)) => //.
+ move=> nu /asboolP h; apply/asboolP; rewrite dssem_abortE.
  apply/distr_eqP=> m; rewrite dnullE.
  by case: (nu m =P 0)=> // /dinsuppP /h.
by apply/EAbort.
Qed.

Lemma rel_cpl_if pre post (ps ps' : psi) e c1 c2 :
    (forall mu, sellora ps pre post (eqmu mu) (eqmu (dssem ps' c1 mu)) c1)
 -> (forall mu, sellora ps pre post (eqmu mu) (eqmu (dssem ps' c2 mu)) c2)
 -> forall mu, sellora ps pre post (eqmu mu)
        (eqmu (dssem ps' (If e then c1 else c2) mu)) (If e then c1 else c2).
Proof.
move=> ih1 ih2 mu.
pose mu1 := (drestr `[{    e }] mu).
pose mu2 := (drestr `[{ ~~ e }] mu).
pose R1 x := `[< x = dssem ps' c1 mu1 >].
pose R2 x := `[< x = dssem ps' c2 mu2 >].
apply/(@EConseq (eqmu mu) (R1 ⊕ R2)) => //; first move=> nu /asboolP.
* case=> -[nu1 nu2 /= eqD] [/asboolP eq1 /asboolP eq2].
  apply/asboolP; apply/distr_eqP=> m; rewrite eqD.
  rewrite !(eq1, eq2) /dssem bsemE.
  rewrite [RHS](dlet_additive (mu1 := mu1) (mu2 := mu2)).
  - by apply/drestrD.
  congr (_ + _); apply/distr_eqP: m; apply/eq_in_dlet => //.
  - by move=> m'; rewrite dinsupp_restr => /andP[_ ->].
  - move=> m'; rewrite dinsupp_restr => /andP[_ /=].
    by move/negbTE=> ->.
pose P1 x := `[< x = mu1 >]; pose P2 x := `[< x = mu2 >].
apply/(@EConseq (P1 ⊕ P2) (R1 ⊕ R2)) => //.
* move=> nu /asboolP ->; apply/asboolP; exists (mu1, mu2) => /=.
  - by apply/drestrD. - by split; apply/asboolP.
apply/(EConseq _ _ (@ECond P1 R1 P2 R2 _ _ _ _ _ _ _ _)) => //.
* move=> nu /asboolP[] [nu1 nu2 /= eqD] [eq1 eq2].
  apply/asboolP; exists (nu1, nu2) => //=.
  split; apply/andP; split=> //; apply/asboolP => /= m.
  - by move/asboolP: eq1=> ->; rewrite dinsupp_restr=> /andP[].
  - by move/asboolP: eq2=> ->; rewrite dinsupp_restr=> /andP[].
* apply: (EConseq _ _ (ih1 mu1)) => nu /= => [/andP[]|].
  - by move/asboolP=> -> h; apply/asboolP/distr_eqP=> m.
  by move/asboolP=> ->; apply/asboolP.
* apply: (EConseq _ _ (ih2 mu2)) => nu /= => [/andP[]|].
  - by move/asboolP=> -> h; apply/asboolP/distr_eqP=> m.
  by move/asboolP=> ->; apply/asboolP.
Qed.

Definition pre_mgt : ident -> dassn :=   fun (f:ident) => xpredT.

Definition cl_mgt ps : ident -> dassn2 :=
  fun (f:ident) => (fun mu => eqmu (dssem ps (ps f) mu)).

Lemma rel_complete_d (c : cmd) P Q ps' :
  ellora_ ps' P Q c ->
  (forall ps, iscomplete' ps (pre_mgt) (cl_mgt ps') c (fun d d' => P d ==> Q d')).
Proof.
  elim: c P Q =>
        [ | | T x e | T gx ge | T x d | bs cb ihb rs
        | e c1 ih1 c2 ih2 | e c0 ih0 | c1 ih1 c2 ih2 | f ]
          P Q  Hhl ps.
  + move=> mu.
    apply: (@EConseq (eqmu mu) (□ pred0)) => //; last by apply/EAbort.
    move=> nu /asboolP h; apply/implyP => Pmu.
    have hQ := Hhl mu Pmu; rewrite dssem_abortE in hQ.
    suff -> : nu = mnull by exact: hQ.
    apply/distr_eqP=> m; rewrite dnullE.
    by case: (nu m =P 0)=> // /dinsuppP /h.
  + move=> mu.
    apply: (@EConseq (eqmu mu) (eqmu mu)) => //; last by apply/ESkip.
    move=> nu /asboolP ->; apply/implyP => Pmu.
    have hQ := Hhl mu Pmu; rewrite dssem_skipE in hQ; exact: hQ.
  + move=> mu.
    apply: (EConseq _ _ (EAssign (fun d' => P mu ==> Q d') x e _ _ ps)) => //.
    move=> nu /asboolP ->; rewrite /dassn_map /=; apply/implyP => Pmu.
    have E : dssem ps (x <<- e) mu = dssem ps' (x <<- e) mu.
      by rewrite /dssem; apply/eq_in_dlet => // m _; rewrite !ssem_assnE.
    rewrite E; exact: (Hhl mu Pmu).
  + (* gassign: the semantics of a global assignment does not mention [ps],
     * so the pullback rule applies exactly as it does for [assign]. *)
    move=> mu.
    apply: (EConseq _ _ (EGAssign (fun d' => P mu ==> Q d') gx ge _ _ ps)) => //.
    move=> nu /asboolP ->; rewrite /dassn_map /=; apply/implyP => Pmu.
    have E : dssem ps (G gx <<- ge) mu = dssem ps' (G gx <<- ge) mu.
      by rewrite /dssem; apply/eq_in_dlet => // m _; rewrite !ssem_gassnE.
    rewrite E; exact: (Hhl mu Pmu).
  + move=> mu.
    apply: (EConseq _ _ (ESample (fun d' => P mu ==> Q d') x d _ _ ps)) => //.
    move=> nu /asboolP ->; rewrite /dassn_map /=; apply/implyP => Pmu.
    have E : dssem ps (x <$- d) mu = dssem ps' (x <$- d) mu.
      by rewrite /dssem; apply/eq_in_dlet => // m _; rewrite !ssem_rndE.
    rewrite E; exact: (Hhl mu Pmu).
  + (* block: the body's behaviour is taken pointwise in the input memory --
     * that is what the induction hypothesis provides -- and [EBlock]
     * integrates it over [mu]. *)
    move=> mu.
    pose F m := ssem_ ps' cb (minit m bs).
    have Hbody : forall m, sellora ps pre_mgt (cl_mgt ps')
                     (eqmu (dunit (minit m bs))) (eqmu (F m)) cb.
    { move=> m.
      have Hsem : ellora_ ps' (eqmu (dunit (minit m bs))) (eqmu (F m)) cb.
        by move=> nu /asboolP ->; apply/asboolP; rewrite /dssem dlet_unit.
      apply: (EConseq _ _ (ihb _ _ Hsem ps (dunit (minit m bs)))) => //.
      by move=> nu /= /implyP H; apply: H; apply/asboolP. }
    apply: H_khl.
    apply: (H_adapt (P2 := xpredT)
              (Q2 := fun mu0 =>
                 eqmu (\dlet_(m <- mu0) \dlet_(m' <- F m) dunit (mret m m' rs)))).
    - by [].
    - move=> m0 /asboolP -> d /asboolP ->.
      apply/implyP => Pmu; have hQ := Hhl mu Pmu.
      suff -> : (\dlet_(m <- mu) \dlet_(m' <- F m) dunit (mret m m' rs))
              = dssem ps' (block bs cb rs) mu by exact: hQ.
      by rewrite /dssem; apply/eq_in_dlet => // m _; rewrite ssem_blockE.
    - by apply: EBlock; exact: Hbody.
  + move=> mu.
    pose mu1 := drestr `[{    e }] mu.
    pose mu2 := drestr `[{ ~~ e }] mu.
    pose R1 x := `[< x = dssem ps' c1 mu1 >].
    pose R2 x := `[< x = dssem ps' c2 mu2 >].
    apply/(@EConseq (eqmu mu) (R1 ⊕ R2)) => //.
    { move=> nu /oplusP[] [nu1 nu2 /= eqD] [/asboolP eq1 /asboolP eq2].
      apply/implyP => Pmu.
      have E : nu = dssem ps' (If e then c1 else c2) mu.
      { apply/distr_eqP=> m; rewrite eqD !(eq1, eq2) /dssem bsemE.
        rewrite [RHS](dlet_additive (mu1 := mu1) (mu2 := mu2)).
        - by apply/drestrD.
        congr (_ + _); apply/distr_eqP: m; apply/eq_in_dlet => //.
        - by move=> m'; rewrite dinsupp_restr => /andP[_ ->].
        - move=> m'; rewrite dinsupp_restr => /andP[_ /=].
          by move/negbTE=> ->. }
      by rewrite E; exact: (Hhl mu Pmu). }
    pose P1 x := `[< x = mu1 >]; pose P2 x := `[< x = mu2 >].
    apply/(@EConseq (P1 ⊕ P2) (R1 ⊕ R2)) => //.
    * move=> nu /asboolP ->; apply/asboolP; exists (mu1, mu2) => /=.
      - by apply/drestrD. - by split; apply/asboolP.
    apply/(EConseq _ _ (@ECond P1 R1 P2 R2 _ _ _ _ _ _ _ _)) => //.
    * move=> nu /asboolP[] [nu1 nu2 /= eqD] [eq1 eq2].
      apply/asboolP; exists (nu1, nu2) => //=.
      split; apply/andP; split=> //; apply/asboolP => /= m.
      - by move/asboolP: eq1=> ->; rewrite dinsupp_restr=> /andP[].
      - by move/asboolP: eq2=> ->; rewrite dinsupp_restr=> /andP[].
    * apply: (EConseq _ _ (ih1 (eqmu mu1) (eqmu (dssem ps' c1 mu1)) _ ps mu1)).
      - by move=> nu /andP[H1 _].
      - by move=> nu /= /implyP H; apply: H; apply/asboolP.
      - by move=> nu /asboolP ->; apply/asboolP.
    * apply: (EConseq _ _ (ih2 (eqmu mu2) (eqmu (dssem ps' c2 mu2)) _ ps mu2)).
      - by move=> nu /andP[H1 _].
      - by move=> nu /= /implyP H; apply: H; apply/asboolP.
      - by move=> nu /asboolP ->; apply/asboolP.
  + move=> mu.
    have rc0 : forall d, sellora ps (pre_mgt) (cl_mgt ps') (eqmu d) (eqmu (dssem ps' c0 d)) c0.
    { move=> d; apply: (EConseq _ _ (ih0 (eqmu d) (eqmu (dssem ps' c0 d)) _ ps d)).
      - by move=> nu /asboolP ->; apply/asboolP.
      - by move=> nu /= /implyP H; apply: H; apply/asboolP.
      - by move=> nu /asboolP ->; apply/asboolP. }
    pose I n := iter n (seqc^~ (IfT e then c0)) skip.
    pose A n := eqmu (dssem ps' (I n) mu).
    pose B n := eqmu (dssem ps' (I n ;; IfT e then abort) mu).
    pose Qinf := eqmu (dssem ps' (While e Do c0) mu).
    apply/(EConseq _ _ (@EWhileTClosed A B Qinf _ _ _ _ _ _ _ _)).
    { by move=> nu /asboolP ->; apply/asboolP => /=;
        rewrite /dssem !bsemE dlet_dunit_id. }
    { move=> nu /andP[/asboolP -> _]; apply/implyP => Pmu.
      exact: (Hhl mu Pmu). }
    { move=> n; rewrite /A {2}/I; set D := dssem ps' (iter _ _ _) _.
      have ->: D = dssem ps' (IfT e then c0) (dssem ps' (I n) mu)
        by rewrite /D iterS dssem_seqE.
      apply/rel_cpl_if; first exact: rc0.
      by move=> d; apply: rel_cpl_skip. }
    { move=> n; rewrite /A /B; set D := dssem ps' (_ ;; _) _.
      have ->: D = dssem ps' (IfT e then abort) (dssem ps' (I n) mu)
        by rewrite /D dssem_seqE.
      apply/rel_cpl_if; first by move=> d; apply: rel_cpl_abort.
      by move=> d; apply: rel_cpl_skip. }
    { move=> nu Bnu cvg; apply/asboolP.
      pose C n := dssem ps' (I n ;; IfT e then abort) mu.
      transitivity (\dlim_(n) C n); first apply/eq_dlim.
      * by move=> n; move/asboolP: (Bnu n) => ->.
      rewrite {}/C /dssem bsemE -dlim_let; first by apply/homo_whilen.
      apply/distr_eqP=> m; rewrite -[in RHS]dlim_bump.
      apply/distr_eqP: m; apply/eq_dlim=> n; apply/eq_in_dlet=> //.
      move=> m _; rewrite whilen_iterc; rewrite !ssemE.
      by apply/eq_in_dlet=> //; rewrite ssem_iterop_iterrev. }
  + move=> mu.
    pose d1 := dssem ps' c1 mu.
    apply/(@ESeq (eqmu d1)).
    - apply: (EConseq _ _ (ih1 (eqmu mu) (eqmu d1) _ ps mu)).
      * by move=> nu /asboolP ->; apply/asboolP.
      * by move=> nu /= /implyP H; apply: H; apply/asboolP.
      * by move=> nu /asboolP ->; apply/asboolP.
    - apply: (EConseq _ _ (ih2 (eqmu d1) (eqmu (dssem ps' c2 d1)) _ ps d1)).
      * by move=> nu /asboolP ->; apply/asboolP.
      * move=> nu /= /implyP H.
        have Hd : nu = dssem ps' c2 d1 by apply/asboolP; apply: H; apply/asboolP.
        by apply/implyP => Pmu; rewrite Hd /d1 -dssem_seqE; exact: (Hhl mu Pmu).
      * by move=> nu /asboolP ->; apply/asboolP.
  + (* call *)
    move=> mu.
    apply: H_khl.
    apply: (H_adapt (P2 := pre_mgt f) (Q2 := cl_mgt ps' f)).
    - by [].
    - move=> m0 /asboolP -> m /asboolP ->.
      apply/implyP => Pmu; have hQ := Hhl mu Pmu.
      suff -> : dssem ps' (ps' f) mu = dssem ps' (call f) mu by exact: hQ.
      by rewrite /dssem; apply/eq_in_dlet => // m1 _; rewrite ssem_call_eq.
    - exact: H_call.
Qed.

Lemma rel_complete (c : cmd) (P : dassn) (Q : dassn2) ps:
  kellora_ ps P Q c -> forall ps', sellora2 ps' (pre_mgt) (cl_mgt ps) P Q c.
Proof.
move=> /kellora_ellora h ps'.
apply: H_hl => s0.
apply: (EConseq _ _ (rel_complete_d (h s0) ps' s0)).
- by move=> mu Hmu.
- by move=> nu /= /implyP H; apply: H; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)
(* The proof system depends on the procedure contract only              *)
(* extensionally: two pointwise-equal call contexts derive exactly the  *)
(* same judgements.                                                     *)
Lemma sellora_eq_post :
  (forall ps pre post (P Q : dassn) c, sellora ps pre post P Q c ->
     forall post', (forall f mu, post f mu = post' f mu) ->
       sellora ps pre post' P Q c) /\
  (forall ps pre post (P : dassn) (Q : dassn2) c, sellora2 ps pre post P Q c ->
     forall post', (forall f mu, post f mu = post' f mu) ->
       sellora2 ps pre post' P Q c).
Proof.
apply: derivable_mut.
- (* EAbort *) by move=> *; apply: EAbort.
- (* ESkip *) by move=> *; apply: ESkip.
- (* EAssign *) by move=> t P x e pre post ps post' heq; apply: EAssign.
- (* EGAssign *) by move=> t P x e pre post ps post' heq; apply: EGAssign.
- (* ESample *) by move=> t P x d pre post ps post' heq; apply: ESample.
- (* ECond *)
  by move=> P P' Q Q' e c1 c2 ps pre post SP SQ _ IH1 _ IH2 post' heq;
     apply: (ECond (IH1 _ heq) (IH2 _ heq)).
- (* EWhileTClosed *)
  move=> P Q Qinf b c pre post ps _ IH1 _ IH2 htc post' heq.
  by apply: (EWhileTClosed (fun n => IH1 n _ heq) (fun n => IH2 n _ heq) htc).
- (* ESeq *)
  by move=> S P Q c1 c2 pre post ps _ IH1 _ IH2 post' heq;
     apply: (ESeq (IH1 _ heq) (IH2 _ heq)).
- (* EConseq *)
  by move=> P' Q' P Q c pre post ps hP hQ _ IH post' heq;
     apply: (EConseq hP hQ (IH _ heq)).
- (* H_khl *)
  by move=> P Q c pre post ps _ IH post' heq; apply: (H_khl (IH _ heq)).
- (* H_hl *)
  by move=> P Q c pre post ps _ IH post' heq;
     apply: H_hl => s0; exact: (IH s0 _ heq).
- (* EBlock: [post] occurs only through the body's premise *)
  move=> F bs c rs pre post ps _ IH post' heq.
  by apply: EBlock => m; exact: (IH m _ heq).
- (* H_call: rebuild the axiom in the new context, then adapt the        *)
  (* postcondition pointwise -- this is what H_adapt is for.            *)
  move=> pre post f ps post' heq.
  apply: (@H_adapt (pre f) (pre f) (post f) (post' f) (call f) pre post' ps).
  - by [].
  - by move=> m0 _ m; rewrite heq.
  - exact: H_call.
- (* H_rec: pre' and postinf' occur only in the conclusion, so the same  *)
  (* premises derive the judgement in any context.                      *)
  move=> P Q c pre postinf pre' postinf' post ps' htc Hbody _ Hc _ post' heq.
  by apply: (@H_rec _ _ _ pre postinf pre' post' post ps' htc Hbody Hc).
- (* H_adapt *)
  by move=> P1 P2 Q1 Q2 c pre post ps hP hQ _ IH post' heq;
     apply: (H_adapt hP hQ (IH _ heq)).
Qed.

Definition cl_mgt_n ps : ident -> nat -> dassn2 :=
  fun (f:ident) (n:nat) =>
    (fun mu => eqmu ((\dlet_(m <- mu) ssem_aux (ubnf ps n) (ps f) m))).

Theorem kellora_complete: forall P c (Q: dassn2) ps pre post,
  kellora_ ps P Q c -> sellora2 ps pre post P Q c.
Proof.
move=> P c Q ps pre post Hvalid.
(* term-wise identification of the k_inliner and ubnf approximations *)
have KU : forall n c0 m, ssem_ (k_inliner_ps1 n ps) c0 m = ssem_aux (ubnf ps n) c0 m.
by move=> n c0 m; rewrite ssem_aux_ssem_.
have EA : forall f n mu, (\dlet_(m <- mu) ssem_aux (ubnf ps n) (ps f) m)
                       = dssem (k_inliner_ps1 n ps) (ps f) mu.
  by move=> f n mu; rewrite /dssem; apply/eq_in_dlet => // m _; rewrite KU.
have Hcall_eq : forall n f mu, dssem (k_inliner_ps1 n ps) ((k_inliner_ps1 n ps) f) mu
                             = dssem (k_inliner_ps1 n ps) (call f) mu.
  by move=> n f mu; rewrite /dssem; apply/eq_in_dlet => // m _; rewrite ssem_call_eq.
have mono : forall (c0 : cmd) x n1 n2, (n1 <= n2)%N ->
    ssem_ (k_inliner_ps1 n1 ps) c0 x <=1 ssem_ (k_inliner_ps1 n2 ps) c0 x.
  by move=> c0 x n1 n2 le; rewrite !KU; apply: mono_ssem_aux; exact: (homo_ubnf le).
have Elim : forall c0 s, dssem ps c0 s = \dlim_(n) dssem (k_inliner_ps1 n ps) c0 s.
  move=> c0 s; rewrite /dssem [RHS]dlim_let;
    first by move=> x n1 n2 le; exact: (mono c0 x n1 n2 le).
  by apply/eq_in_dlet => // m0 _; rewrite dlim_inliner_ssem.
have pS : forall (F : nat -> dassn2) k, post_shift F k.+1 = F k by [].
have p0 : forall (F : nat -> dassn2), post_shift F 0%N = (fun _ => eqmu dnull) by [].
(* the shifted finite contract is exactly the exact contract of the n-th inlining *)
have Ha : forall n f mu, post_shift (cl_mgt_n ps f) n mu = cl_mgt (k_inliner_ps1 n ps) f mu.
  move=> n f mu; rewrite /cl_mgt Hcall_eq; case: n => [|k].
  - rewrite p0.
    suff -> : dssem (k_inliner_ps1 0 ps) (call f) mu = dnull by [].
    rewrite /dssem; transitivity (\dlet_(m0 <- mu) (dnull : Distr cmem)).
      by apply/eq_in_dlet => // m0 _; rewrite KU /=.
    by apply/distr_eqP => x; rewrite dletC dnullE mulr0.
  - rewrite pS.
    suff -> : dssem (k_inliner_ps1 k.+1 ps) (call f) mu
            = \dlet_(m <- mu) ssem_aux (ubnf ps k) (ps f) m by rewrite /cl_mgt_n.
    by rewrite /dssem; apply/eq_in_dlet => // m0 _; rewrite (inline2_split k 1) KU.
apply: (@H_rec _ _ _ pre_mgt (cl_mgt ps) _ _ (cl_mgt_n ps)).
- (* closure: the finite approximations converge to the exact semantics *)
  move=> p s nu Hnu _; rewrite /cl_mgt /=; apply/asboolP.
  have Hnu1 : forall n, nu n.+1 = dssem (k_inliner_ps1 n ps) (ps p) s.
    move=> n; move: (Hnu n.+1); rewrite pS /cl_mgt_n /= => /asboolP ->.
    exact: (EA p n s).
  have -> : \dlim_(n) nu n = \dlim_(n) nu n.+1.
    by apply/distr_eqP => x; rewrite dlim_bump.
  by rewrite (Elim (ps p) s); apply/eq_dlim => n; exact: (Hnu1 n).
- (* body derivation at each depth, via completeness for the n-th inlining *)
  move=> p' ps0 n.
  apply: (proj2 sellora_eq_post _ _ (cl_mgt (k_inliner_ps1 n ps))).
  + apply: (@rel_complete (ps p') (pre_mgt p') (cl_mgt_n ps p' n) (k_inliner_ps1 n ps)).
    by move=> mu _; rewrite /cl_mgt_n /= EA; apply/asboolP.
  + by move=> f mu; rewrite Ha.
- (* the command c meets its contract assuming the exact call contract *)
  by apply: rel_complete.
Qed.

Theorem ellora_complete: forall P c Q ps pre post,
  ellora_ ps P Q c -> sellora ps pre post P Q c.
Proof.
move=> P c Q ps pre post Hvalid.
apply: H_khl.
apply kellora_complete.
by apply ellora_kellora.
Qed.

End Complete.
