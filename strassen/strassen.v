(* -------------------------------------------------------------------- *)
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.finmap    Require Import finmap.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.analysis  Require Import reals realseq realsum distr xfinmap.
(* ------- *)           Require Import xbigops misc maxflow elift.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Local Notation edge T := (vertex T * vertex T)%type.

Local Notation "← x" := (inl x) (at level 2).
Local Notation "→ x" := (inr x) (at level 2).

Local Notation "⇐ x" := (inl (Some x)) (at level 2).
Local Notation "⇒ x" := (inr (Some x)) (at level 2).

(* ==================================================================== *)
Local Notation distr T := {distr T / R}.

(* -------------------------------------------------------------------- *)
Lemma nbounded_sub_mono (u : nat -> R) : nbounded u ->
  {α : nat -> nat & {b : bool |
    {homo α : x y / (x < y)%N} &
    {homo ((-1) ^+ b \*o (u \o α)) : x y / (x <= y)%N >-> (x <= y)} } }.
Proof.
move=> bnd_u; pose E n := `[<forall m, (n < m)%N -> (u m < u n)%R>].
case: (discrete.existsTP (fun s : seq nat => {subset E <= s})) => /=; last first.
+ case/natpred_finiteN => α homo_α Eα; exists α, true => //.
  move=> m n le_mn; rewrite expr1 /= !mulN1r ler_oppr opprK.
  move: le_mn; rewrite leq_eqVlt => /orP[/eqP->//|lt_mn].
  by have /asboolP := Eα m => /(_ (α n) (homo_α _ _ lt_mn)) /ltW.
case=> s sub_sE; pose N := \max_(i <- s) i.+1.
have h k : (N <= k)%N -> exists k', (k < k')%N && (u k <= u k').
+ move=> le_Nk; case/boolP: (E k).
  * move/sub_sE => k_in_s; move: le_Nk; rewrite /N.
    rewrite (perm_big _ (perm_to_rem (k_in_s))) /=.
    by rewrite big_cons geq_max ltnn.
  case/existsp_asboolPn=> k' /asboolPn /imply_asboolPn.
  case=> lt_kk' /negP; rewrite -leNgt => le_ukuk'.
  by exists k'; rewrite lt_kk' le_ukuk'.
pose α := fix α n := if n is n.+1
  then xchoose (h _ (leq_addr (α n - N) N))
  else N%N.
have geN_α n : (N <= α n)%N.
+ elim: n => //= n ih; have := xchooseP (h _ (leq_addr (α n - N) N)).
  case/andP; rewrite {1}subnKC // => /(leq_trans _) h' _.
  by apply/h'; apply/(leq_trans ih).
have homo_α : {homo α : x y / (x < y)%N}.
+ apply/homoS_lt => -[|n] /=.
  * have := xchooseP (h _ (leq_addr (N - N) N)).
    by case/andP; rewrite subnn {1}addn0.
  set m := xchoose _; have := xchooseP (h _ (leq_addr (m - N) N)).
  case/andP; rewrite {1}subnKC //.
  have := xchooseP (h _ (leq_addr (α n - N) N)).
  rewrite {1}subnKC ?geN_α // => /andP[h' _].
  by apply/(leq_trans _ h')/ltnW/geN_α.
exists (fun n => α n.+1), false => //.
+ by move=> m n; rewrite -ltnS => /homo_α.
apply/homoS_ler=> n; rewrite expr0 /= !mul1r.
set m := xchoose _; have := xchooseP (h _ (leq_addr (m - N) N)).
set k := xchoose _ => /andP[]; rewrite subnKC //.
have := xchooseP (h _ (leq_addr (α n - N) N)); rewrite -/m.
by rewrite subnKC ?geN_α // => /andP[/ltnW /(leq_trans (geN_α _))].
Qed.

(* -------------------------------------------------------------------- *)
Lemma BW (u : nat -> R) : nbounded u ->
  {α : nat -> nat | {homo α : x y / (x < y)%N} & iscvg (u \o α)}.
Proof.
move=> bnd; have bndcp f : nbounded (u \o f).
+ by case: bnd => v hv; exists v => n; apply/hv.
case/nbounded_sub_mono: (bnd) => [α] [[]] homo_α homo_uα; last first.
+ exists α => //; have /ncvg_mono_bnd: nbounded (u \o α) by apply/bndcp.
  case=> [x y /homo_uα|]; first by rewrite !expr0 /= !mul1r.
  by move=> l cvl; exists l.
exists α => //; have /ncvg_mono_bnd: nbounded ((\- u) \o α).
+ case: bnd; elim/nbh_finW => e gt0_e /= h.
  exists (NFin _ gt0_e) => n /=; move: (h (α n)); rewrite !inE.
  by rewrite !subr0 normrN.
case=> [x y /homo_uα|]; first by rewrite !expr1 /= !mulN1r.
move=> l cvl; exists (- l) => /=; apply/(ncvg_eq (v := \- (\- u \o α))).
+ by move=> x /=; rewrite opprK.
+ by apply/(@ncvgN _ _ l%:E).
Qed.

(* -------------------------------------------------------------------- *)
Axiom DCT : forall {T: choiceType} (un : nat -> T -> R) (u g : T -> R),
     (forall x, ncvg (un^~ x) (u x)%:E)
  -> (forall n x, `|un n x| <= g x)
  -> summable g
  -> summable u /\ ncvg (fun n => psum (un n)) (psum u)%:E.

(* -------------------------------------------------------------------- *)
Lemma DCT_swap {T: choiceType} (un : nat -> T -> R) (u g : T -> R) :
     (forall x, ncvg (un^~ x) (u x)%:E)
  -> (forall n x, `|un n x| <= g x)
  -> summable g
  -> real_of_er (nlim (fun n => psum (un n)))
     = psum (fun a => (real_of_er (nlim (un^~ a)))).
Proof.
move=> h1 h2 h3; case: (DCT h1 h2 h3) => _ /nlimE ->.
by apply/eq_psum => x /=; rewrite (nlimE (h1 x)).
Qed.

(* -------------------------------------------------------------------- *)
Lemma DCT_ncvg {T: choiceType} (un : nat -> T -> R) (u g : T -> R) :
     (forall x, ncvg (un^~ x) (u x)%:E)
  -> (forall n x, `|un n x| <= g x)
  -> summable g
  -> ncvg (fun n => psum (un n)) (psum u)%:E.
Proof. by move=> h1 h2 h3; case: (@DCT T un u g). Qed.

(* ==================================================================== *)
Section CountableSeqCompacityForDistr.
Context {A : countType} (μ : nat -> distr A).

(* -------------------------------------------------------------------- *)
Lemma strcvg :
  {Ω : nat -> nat | {homo Ω : x y / (x < y)%N} &
    forall a : A, iscvg (fun n => μ (Ω n) a)}.
Proof.
have α a θ: {α : nat -> nat |
  {homo α : x y / (x < y)%N} & iscvg (μ^~ a \o θ \o α)}.
+ case: (@BW (μ^~ a \o θ)) => [|α mono_α cvg_μα]; last by exists α.
  apply/asboolP/nboundedP; exists 2%:R => // n.
  by rewrite (@le_lt_trans _ _ 1) ?ltr1n // ger0_norm //= le1_mu1.
have homo_α a θ : {homo tag (α a θ) : x y / (x < y)%N} by case: (α a θ).
pose ω θ n := odflt idfun (omap (fun a => tag (α a θ)) (choice.unpickle n)).
have homo_ω k θ: {homo θ : m n / (m < n)%N} -> {homo ω θ k : m n / (m < n)%N}.
+ move=> homo_θ m n lt_mn; rewrite /ω; case: choice.unpickle => //=.
  * by move=> a; apply/homo_α.
pose Ω := fix Ω k :=
  if k is k'.+1 then
    let σ := ω (Ω k').2 k' in (σ, (Ω k').2 \o σ)
  else (idfun, idfun).
have Ω1SE i: (Ω i.+1).1 =1 ω (Ω i).2 i by [].
have Ω2E i: (Ω i).2 =1 \big[comp/idfun]_(0 <= j < i) (Ω j.+1).1.
+ elim: i => /= [|i ih] n; first by rewrite big_geq.
  by rewrite big_nat_recr //= -ih.
have ΩD2E n m: (Ω (n + m)%N).2 =1
  (Ω n).2 \o \big[comp/idfun]_(0 <= j < m) (Ω (n.+1+j)%N).1 => [k /=|].
+ rewrite !Ω2E -addnE (big_cat_nat _ (n := n)) ?leq_addr //=.
  congr (_ _); rewrite -{1}[n]add0n big_addn addKn.
  by apply/eq_bigcomp => {}k _; rewrite addnC.
have homoΩ2 n: {homo (Ω n).2 : x y / (x < y)%N}.
+ by elim: n => //= n ih; apply/homo_comp => //=; apply/homo_ω.
have homoΩ1 n: {homo (Ω n).1 : x y / (x < y)%N}.
+ by case: n => //= n; apply/homo_ω/homoΩ2.
exists (fun n => (Ω n).2 n) => [|a].
+ move=> m n lt_mn; rewrite -{1}[n](subnK (ltnW lt_mn)) addnC.
  rewrite ΩD2E (@leq_trans ((Ω m).2 n)) //; first by apply/homoΩ2.
  rewrite (misc.homo_leq_mono (homoΩ2 _)) homo_geidfun //.
  by apply/homo_bigcomp => k _; apply/homoΩ1.
have [p pE]: exists p, p = (choice.pickle a).+1 by exists (choice.pickle a).+1.
rewrite (iscvg_shift p); pose T n := (Ω (n + p)%N).2 (n + p)%N.
have h: exists2 σ, {homo σ : x y / (x < y)%N} & T =1 (Ω p).2 \o σ.
+ exists (fun n => (\big[comp/idfun]_(0 <= j < n) (Ω (p.+1+j)%N).1) (n+p)%N).
  * move=> x y ltxy; rewrite -(homo_ltn_mono (homoΩ2 p)).
    have /=<- := ΩD2E p x (x+p)%N; have /=<- := ΩD2E p y (y+p)%N.
    rewrite (leq_trans (homoΩ2 _ (x+p)%N (y+p)%N _)) ?ltn_add2r //.
    rewrite -{2}[y](@subnK x) ?[(x <= y)%N]ltnW // addnA addnAC.
    rewrite [in X in (_ <= X)%N]ΩD2E (misc.homo_leq_mono (homoΩ2 _)).
    by apply/homo_geidfun/homo_bigcomp => k _; apply/homoΩ1.
  * by move=> n /=; rewrite /T addnC ΩD2E.
case: h => σ homoσ TE; pose X := ((μ^~ a) \o (Ω p).2) \o σ.
apply/(@iscvg_eq _ _ X); first by move=> k /=; rewrite -/(T _) TE.
apply/iscvg_sub => //; rewrite {p T TE X}pE /=; set ξ := Ω _.
by rewrite /ω choice.pickleK /=; case: (α a ξ.2).
Qed.
End CountableSeqCompacityForDistr.

(* -------------------------------------------------------------------- *)
Lemma strcvg2
  {A B : countType} (μ1 : nat -> distr A) (μ2 : nat -> distr B)
:
  { Ω : nat -> nat | {homo Ω : x y / (x < y)%N} &
     [/\ forall a : A, iscvg (fun n => μ1 (Ω n) a)
       & forall b : B, iscvg (fun n => μ2 (Ω n) b) ] }.
Proof.
case: (strcvg μ1) => ω1 mono1 cvg1.
case: (strcvg (μ2 \o ω1)) => ω2 mono2 cvg2.
(exists (ω1 \o ω2); last split) => // [m n|a].
+ by move/mono2/mono1.
+ by apply/(iscvg_sub (u := (μ1 \o ω1)^~ a) (σ := ω2)).
Qed.

(* ==================================================================== *)
Section RevStrassen.
Context {A B : finType}.
Context (ε δ : R) (μ1 : distr A) (μ2 : distr B) (S : pred (A * B)).

Hypothesis (ge0_ε : 0 <= ε) (ge0_δ : 0 <= δ).
Hypothesis alift : elift ε δ μ1 μ2 S.

Theorem StrassenI X :
  \P_[μ1] X <= Ω ε * \P_[μ2] (fun y => [exists x in X, S (x, y)]) + δ.
Proof.
case: alift => /= -[μL μR] [EL ER RμL RμR /edist_le -/(_ ge0_ε) /= leδ].
pose T := [pred ab : option A * option B
  | if ab is (Some a, _) then X a else false].
move/(_ T): leδ; rewrite !pr_dmargin => /le_trans.
rewrite -(eqr_pr _ EL) -(eqr_pr _ ER) !pr_dmargin; apply.
rewrite ler_add2r ler_pmul2l ?gt0_Ω //; apply/le_in_pr => /=.
case=> [[a|] b] // /RμR /=; rewrite !inE /= => Sab aX.
by apply/existsP; exists a; rewrite Sab andbT.
Qed.
End RevStrassen.

(* ==================================================================== *)
Section FinStrassen.
Context {A B : finType}.
Context (ε δ : R) (μ1 : distr A) (μ2 : distr B) (S : pred (A * B)).

Hypothesis (ge0_ε : 0 <= ε) (ge0_δ : 0 <= δ).

Hypothesis mono : forall X,
  \P_[μ1] X <= Ω ε * \P_[μ2] (fun y => [exists x in X, S (x, y)]) + δ.

Local Notation ω := (dweight μ2 + Ω (- ε) * δ).
Local Notation N := (option A + option B)%type.

Lemma ge0_ω : 0 <= ω.
Proof. by apply/addr_ge0/mulr_ge0 => //; rewrite ?(ge0_pr, ge0_Ω). Qed.

Local Hint Immediate ge0_ω : core.

Local Notation ge0 := (ler01, ge0_Ω, ge0_ω, ge0_ε, ge0_δ, ge0_mu, ler0n).

(* -------------------------------------------------------------------- *)
Section VertexCase.
Context (P : vertex N -> Prop).

Hypothesis Psrc : P ⊤.
Hypothesis Pdst : P ⊥.
Hypothesis PLN  : P (↓ (← None)).
Hypothesis PL   : forall a, P (↓ (⇐ a)).
Hypothesis PRN  : P (↓ (→ None)).
Hypothesis PR   : forall b, P (↓ (⇒ b)).

Lemma vtx_ind v : P v.
Proof. by case: v => -[[|]|[[a|]|[b|]]]. Qed.
End VertexCase.

(* -------------------------------------------------------------------- *)
Definition c (e : edge N) : R :=
  match e.1, e.2 return R with
  | ⊤, ↓ (← (None  )) => ω - Ω (- ε) * (dweight μ1)
  | ⊤, ↓ (⇐ a       ) => Ω (- ε) * μ1 a

  | ↓ (→ (None  )), ⊥ => Ω (- ε) * δ
  | ↓ (⇒ b       ), ⊥ => μ2 b

  | ↓ (← None), ↓ (→ _   ) => ω
  | ↓ (← _   ), ↓ (→ None) => ω

  | ↓ (⇐ a), ↓ (⇒ b) => (S (a, b))%:R * ω

  | _, _ => 0
  end.

(* -------------------------------------------------------------------- *)
Lemma isnetwork_c : isnetwork (finfun c).
Proof.
apply/networkP=> /= -[a b]; elim/vtx_ind: b; elim/vtx_ind: a => *;
  rewrite ?ffunE /c //=; try by rewrite ?mulr_ge0 1?ge0.
rewrite -addrA -mulrBr -(@pmulr_rge0 _ (Ω ε)) ?gt0_Ω //.
rewrite [X in _ <= X]mulrDr mulrA -ΩD subrr Ω0 mul1r addrA.
rewrite subr_ge0 (le_trans (mono _)) // ler_add2r ler_pmul2l ?gt0_Ω //.
by apply/le_in_pr.
Qed.

Local Notation NF  := (Network isnetwork_c).
Local Notation cut := (pred N).

(* -------------------------------------------------------------------- *)
Lemma enum_VN_perm :
  perm_eq
    (enum {: vertex N})
    (⊤ :: ⊥ :: ↓ (← None) :: ↓ (→ None)
       :: [seq ↓ (⇐ a) | a : A]
       ++ [seq ↓ (⇒ b) | b : B]).
Proof.
have h: perm_eql (enum {: vertex N}) [seq Vertex x | x : bool + N].
+ apply/permPl; apply/uniq_perm; rewrite ?enum_uniq //.
  - by rewrite map_inj_uniq ?enum_uniq // => ?? [].
  by case=> v; rewrite mem_enum; apply/esym/map_f; rewrite enumT.
rewrite /image_mem [X in _ ++ X]map_comp [X in X ++ _]map_comp.
rewrite -map_cat -!map_cons {}h; apply/perm_map.
set s1 := (X in X ++ _); set s2 := (X in _ ++ X).
rewrite (permPl enum_sum_perm) /=.
rewrite (perm_cat2rE _ (perm_map _ enum_bool_perm)) /=.
rewrite !perm_cons [X in _ ++ X]map_comp [X in X ++ _]map_comp.
rewrite -map_cat -!map_cons; apply/perm_map => {s1 s2}.
rewrite (permPl enum_sum_perm) /=.
rewrite (perm_cat2rE _ (perm_map _ enum_option_perm)) /= perm_cons.
rewrite perm_sym -cat1s -perm_catCA /= perm_cat //.
+ by rewrite -[X in perm_eq _ X]map_comp; apply/perm_map.
rewrite perm_sym map_comp -map_cons perm_map //.
by apply/enum_option_perm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sum_cLE : \sum_(a : A) c (⊤, ↓ (⇐ a)) = Ω (-ε) * dweight μ1.
Proof.
rewrite pr_predT psum_fin mulr_sumr; apply/eq_bigr.
by move=> a _; rewrite ger0_norm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sum_cRE : \sum_(b : B) c (↓ (⇒ b), ⊥) = dweight μ2.
Proof.
rewrite pr_predT psum_fin; apply/eq_bigr.
by move=> b _; rewrite ger0_norm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sum_cLSE : \sum_(a : option A) c (⊤, ↓ (← a)) = ω.
Proof.
rewrite big_option /= sum_cLE /c /=; set ω := ω.
by rewrite addrAC -addrA subrr addr0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sum_cRSE : \sum_(b : option B) c (↓ (→ b), ⊥) = ω.
Proof.
by rewrite big_option /= sum_cRE /c /= addrC.
Qed.

(* -------------------------------------------------------------------- *)
Lemma le_NFfc (f : flow NF) e : f e <= c e.
Proof. by have /(_ e) /= := flow_lecp f; rewrite ffunE. Qed.

(* -------------------------------------------------------------------- *)
Lemma ge0_flowNF (f : flow NF) (a : option A) (b : option B):
  0 <= f (↓ (← a), ↓ (→ b)).
Proof.
by apply/flow_ge0; rewrite ffunE; case: a b => [a|] [b|].
Qed.

(* -------------------------------------------------------------------- *)
Lemma sum_flowNFL (f : flow NF) (a : option A) :
  \sum_v f (↓ (← a), v) = \sum_b f (↓ (← a), ↓ (→ b)) - f (⊤, ↓ (← a)).
Proof.
pose XB : {set vertex N} := [set ↓ (→ b) | b : option B].
rewrite (bigID (mem XB)) big_imset /= => [b1 b2 _ _ [//]|].
rewrite (eq_bigl xpredT) //; congr +%R; rewrite (bigD1 ⊤) /=.
+ by apply/imsetP; case.
rewrite flow_antisym big1 ?addr0 // => v /andP[h1 h2].
apply/flow_eq0; rewrite ffunE.
+ elim/vtx_ind: v h1 h2 => //=; try by case: a.
  * by move/imsetP=> []; exists None.
  * by move=> b /imsetP[]; exists (Some b).
+ by elim/vtx_ind: {h1} v h2.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sum_flowNFR (f : flow NF) (b : option B) :
  \sum_v f (↓ (→ b), v) = \sum_a f (↓ (→ b), ↓ (← a)) - f (⊥, ↓ (→ b)).
Proof.
pose XA : {set vertex N} := [set ↓ (← a) | a : option A].
rewrite (bigID (mem XA)) big_imset /= => [a1 a2 _ _ [//]|].
rewrite (eq_bigl xpredT) //; congr +%R; rewrite (bigD1 ⊥) /=.
+ by apply/imsetP; case.
rewrite flow_antisym big1 ?addr0 // => v /andP[h1 h2].
apply/flow_eq0; rewrite ffunE.
+ by elim/vtx_ind: v h1 h2; case: b.
+ elim/vtx_ind: v h1 h2 => //.
  * by move/imsetP=> []; exists None.
  * by move=> a /imsetP[]; exists (Some a).
Qed.

(* -------------------------------------------------------------------- *)
Lemma kcf_flowNFL (f : flow NF) (a : option A) :
  f (⊤, ↓ (← a)) = \sum_b f (↓ (← a), ↓ (→ b)).
Proof.
apply/esym/eqP; rewrite -subr_eq0 -sum_flowNFL.
by apply/eqP/flow_kirchnoff.
Qed.

(* -------------------------------------------------------------------- *)
Lemma kcf_flowNFR (f : flow NF) (b : option B) :
  f (↓ (→ b), ⊥) = \sum_a f (↓ (← a), ↓ (→ b)).
Proof.
apply/eqP; rewrite -subr_eq0 -(rwP eqP) -[RHS](flow_kirchnoff f (→ b)).
rewrite sum_flowNFR [RHS]addrC -flow_antisym; congr +%R.
by rewrite -sumrN; apply/eq_bigr=> /= a _; rewrite -flow_antisym.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cweightE (C : cut) : cweight C NF =
    (if C ← None then \sum_(b | ~~ C (⇒ b)) ω else ω - Ω (-ε) * dweight μ1)
  + (if C → None then Ω (-ε) * δ else \sum_(a | C (⇐ a)) ω)
  + ((C ← None && ~~ C → None)%:R * ω)
  + Ω (-ε) * \P_[μ1] [pred a | ~~ C ⇐ a]
  + \P_[μ2] [pred b | C ⇒ b]
  + \sum_(ab | C ⇐ (ab.1) && ~~ C ⇒ (ab.2)) (S ab)%:R * ω.
Proof.
set c1 := IFP; set c2 := IFP.
set Pμ1 := \P_[μ1] _; set Pμ2 := \P_[μ2] [pred b | C ⇒ b].
pose XA : {set vertex N} := [set ↓ (⇐ x) | x in A].
pose XB : {set vertex N} := [set ↓ (⇒ x) | x in B].
rewrite /cweight {1} /index_enum -enumT /=.
rewrite (perm_big _ enum_VN_perm) /= 2!big_cons /=.
rewrite (bigID (mem XA)) /= -addrA addrCA big_mkcond /=.
rewrite (bigD1 (↓ (← None))) //= !ffunE /= big1 ?addr0.
+ move=> v; rewrite ffunE; case: ifP=> // /andP[].
  by elim/vtx_ind: v => // a _ /imsetP[]; exists a.
rewrite cut_grdE (_ : _ \notin XA = true) ?andbT.
+ by apply/imsetP; case.
rewrite {1}/c /= if_neg addrCA; set c1a := IFP.
rewrite big_andbC big_mkcondr big_imset /= => [a1 a2 _ _ [//]|].
rewrite (eq_bigl xpredT) // [X in X + _ = _](_ : _  = Ω (-ε) * Pμ1).
+ rewrite /Pμ1 pr_finE mulr_sumr; apply/eq_bigr=> a _.
  rewrite !cut_grdE ffunE /c /= if_neg; case: ifP=> //= _.
  - by rewrite !(mul0r, mulr0). - by rewrite !(mul1r, mulr1).
rewrite [_ + (_ * Pμ1)]addrC -!addrA; congr +%R.
rewrite addrC big_mkcond /= big_cons -big_mkcond /= cut_grdE.
rewrite (bigID (mem XB)) /= -[IFF]addr0 -fun2_if; set c1b := IFP.
rewrite [LHS]addrC -(_ : c1a + c1b = c1) -?addrA.
+ rewrite {}/c1a {}/c1b fun2_if !(addr0, add0r); congr IFP.
  rewrite big_mkcondl big_imset /= => [b1 b2 _ _ [//]|].
  rewrite (eq_bigl xpredT) // [RHS]big_mkcond /=.
  by apply/eq_bigr=> b _; rewrite cut_grdE ffunE.
do 2! congr +%R; move=> {c1 c1a c1b}.
rewrite big_mkcond (bigD1 (↓ (→ None))) //= big1 ?addr0.
+ move=> v; rewrite ffunE; case: ifP=> // /andP[].
  by elim/vtx_ind: v => // b _ /imsetP[]; exists b.
rewrite cut_grdE [X in _ && X](_ : _ = true) ?andbT.
+ by apply/imsetP; case.
rewrite ffunE {1}/c /= [RHS]addrCA; congr +%R.
+ by do 2? case: ifP; rewrite !Monoid.simpm.
rewrite big_cons cut_grdE -[IFF]add0r -fun2_if if_same.
rewrite (bigD1 ⊥) //= ffunE {1}/c /= big1 ?addr0.
+ by move=> v; rewrite ffunE => /andP[_]; elim/vtx_ind: v.
set c2a := IFP; rewrite big_cat /= !addrA [RHS]addrAC.
congr +%R; last rewrite big_mkcond /= big_map /Pμ2; last first.
+ rewrite pr_finE [in RHS]/index_enum -enumT; apply/eq_bigr=> b _.
  rewrite cut_grdE /=; case: ifP=> _; rewrite Monoid.simpm //.
  rewrite (bigD1 ⊥) //= ffunE {1}/c /= big1 ?addr0 //.
  by move=> v /andP[_]; rewrite ffunE; elim/vtx_ind: v.
rewrite exchange_big big_mkcond (bigD1 (↓ (→ None))) //=.
rewrite cut_grdE if_neg; set c2b := IFP; rewrite -(_ : c2a + c2b = c2).
+ rewrite {}/c2a {}/c2b /c2 fun2_if ?(addr0, add0r); congr IFP.
  rewrite big_mkcond big_map [RHS]big_mkcond /=.
  rewrite [in RHS]/index_enum -enumT; apply/eq_bigr=> a _.
  by rewrite cut_grdE ffunE; case: ifP.
rewrite -!addrA; do 2! congr +%R; move=> {c2a c2b c2}.
rewrite -big_mkcondl (bigID (mem XB)) /= addrC big1 ?add0r.
+ move=> v; rewrite -andbA => /and3P [_ h1 h2]; rewrite big_map.
  rewrite big1 // => a _; rewrite ffunE; move: h1 h2.
  by elim/vtx_ind: v => // b _ /imsetP[]; exists b.
rewrite big_andbC big_mkcondr big_imset /= => [b1 b2 _ _ [//]|].
rewrite (eq_bigl xpredT) // -big_mkcond big_andbC /=.
rewrite exchange_big big_map enumT pair_big /=; apply/eq_big.
+ by move=> ab; rewrite !cut_grdE.
by case=> [a b] /=; rewrite !cut_grdE ffunE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cweightE_cutL : cweight pred0 NF = \sum_a c (⊤, ↓ (← a)).
Proof.
rewrite cweightE /= !(pr_pred0, pr_predT, big_pred0_eq).
rewrite !Monoid.simpm -addrA addNr addr0 big_option /=.
rewrite {1}/c /= !pr_predT -[LHS]addr0 -!addrA.
do 2! congr+%R; apply/esym/eqP; rewrite addrC subr_eq0.
rewrite psum_fin mulr_sumr; apply/eqP/eq_bigr.
by move=> a _; rewrite /c /= ger0_norm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cweight_cutL : cweight pred0 NF = ω.
Proof. by rewrite cweightE_cutL -sum_cLSE. Qed.

(* -------------------------------------------------------------------- *)
Lemma cweightE_cutR : cweight predT NF = \sum_b c (↓ (→ b), ⊥).
Proof.
rewrite cweightE /= !(pr_pred0, pr_predT, big_pred0_eq).
rewrite !Monoid.simpm big_option /=; congr +%R.
by rewrite psum_fin; apply/eq_bigr=> b _; rewrite ger0_norm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cweight_cutR : cweight predT NF = ω.
Proof. by rewrite cweightE_cutR -sum_cRSE. Qed.

(* -------------------------------------------------------------------- *)
Lemma geω_cut (C : cut) : ω <= cweight C NF.
Proof.
rewrite cweightE; set ω := ω.
set sL := C ← None; set sR := C → None;
  set i1 := IFP; set i2 := IFP;
  set s4 := (X in _ <= _ + X); set s3 := (X in _ + X + s4);
  set s2 := (X in _ + X + s3); set s1 := (X in _ + X + s2).
have h: forall (I : finType) P, 0 <= \sum_(i : I | P i) ω.
+ by move=> I P; apply/sumr_ge0=> i _; apply/ge0_ω.
have [h1 h2 h3 h4]: [/\ 0 <= s1, 0 <= s2, 0 <= s3 & 0 <= s4];
  first (split; try by rewrite 1?mulr_ge0 ?(ge0, ge0_pr)).
+ by apply/sumr_ge0=> /= ab _; rewrite mulr_ge0 ?ge0.
have [hi1 hi2]: [/\ 0 <= i1 & 0 <= i2]; first split.
+ rewrite /i1; case: ifP=> // _; move/forallP: isnetwork_c=> /=.
  by move/(_ (⊤, ↓ (← None))); rewrite ffunE /c /=.
+ by rewrite /i2; case: ifP=> // _; rewrite mulr_ge0 ?ge0.
rewrite /i2; case/boolP: {+}sR => hR; last first.
+ case/boolP: [exists a, C ⇐ a] => [/existsP /= [a Ca]|].
  * by rewrite (bigD1 a) //= !addrA 5?ler_paddr // -addrA ler_paddl.
  rewrite negb_exists => /forallP /= NCA; rewrite /s1 hR andbT.
  case/boolP: {+}sL; rewrite !Monoid.simpm /= => hL.
  * by rewrite 3?ler_paddr // -!addrA 2?ler_paddl.
  rewrite /i1 -if_neg hL /s2 2?ler_paddr // [X in _ <= X]addrAC.
  rewrite ler_paddr // addrAC -addrA -mulrBr ler_paddr //.
  rewrite mulr_ge0 ?ge0_Ω // subr_ge0; apply/le_in_pr.
  by move=> a _ _; apply/NCA.
rewrite /i1; case/boolP: {+}sL => hL.
+ case/boolP: [forall b, C ⇒ b] => [/forallP /=|]; last first.
  * rewrite negb_forall => /existsP [b CNb]; rewrite (bigD1 b) //=.
    by rewrite -6!addrA ler_paddr // !addr_ge0 // mulr_ge0 1?ge0.
  move=> CB; rewrite -![in X in _ <= X]addrA ler_paddl //.
  rewrite /ω [X in X <= _]addrC ler_add2l 2?ler_paddl //.
  by rewrite ler_paddr //; apply/le_in_pr=> b _ _; apply/CB.
case/boolP: [exists ab : A * B, C ⇐ (ab.1) && ~~ C ⇒ (ab.2) && (S ab)].
+ set s := ω - _; rewrite /s4 => /existsP[ab /andP [hCab hab]].
  rewrite (bigD1 ab) ?hCab //= hab mul1r [ω + _]addrC addrA.
  rewrite ler_paddl // addr_ge0 //; last first.
  * by apply/sumr_ge0=> ? _; rewrite mulr_ge0 ?ge0.
  do 4! rewrite addr_ge0 //.
  * by have := hi1; rewrite /i1 -if_neg hL.
  * by rewrite mulr_ge0 ?ge0.
rewrite negb_exists => /forallP /= hS; rewrite ler_paddr //.
rewrite /s1 hR !Monoid.simpm -4!addrA ler_addl addrC.
rewrite subr_ge0 !addrA addrAC; set s := _ + s3.
apply/(@le_trans _ _ (Ω (-ε) * \P_[μ1] [pred a | C ⇐ a] + s2)).
+ rewrite /s2 -mulrDr ler_pmul2l ?gt0_Ω // -pr_or_indep.
  * by move=> a; rewrite !inE negbK.
  by apply/le_in_pr=> a _ _; rewrite 2!inE orbN.
rewrite ler_add2r /s addrC -(@ler_pmul2l _ (Ω ε)) ?gt0_Ω //.
rewrite mulrDr !mulrA -ΩD subrr Ω0 !Monoid.simpm /s3.
pose Pa := [pred a | C ⇐ a].
pose Pb := [pred b | [exists a in Pa, S (a, b)]].
apply/(@le_trans _ _ (Ω ε * \P_[μ2] Pb + δ)); first by apply/mono.
rewrite ler_add2r ler_pmul2l ?gt0_Ω //; apply/le_in_pr.
move=> b _ /existsP[a /andP[Pa_a Sab]]; move/(_ (a, b)): hS => /=.
by rewrite inE in Pa_a; rewrite Pa_a Sab !Monoid.simpm negbK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma mincut_ω : { C : cut | cweight C NF = ω }.
Proof. by exists predT; rewrite cweight_cutR. Qed.

(* -------------------------------------------------------------------- *)
Definition StrassenC := nosimpl (proj1_sig mincut_ω).

(* -------------------------------------------------------------------- *)
Lemma weight_StrassenC : cweight StrassenC NF = ω.
Proof. by rewrite /StrassenC; case: mincut_ω. Qed.

(* -------------------------------------------------------------------- *)
Lemma min_StrassenC (C : cut) : cweight StrassenC NF <= cweight C NF.
Proof. by rewrite weight_StrassenC; apply/geω_cut. Qed.

(* -------------------------------------------------------------------- *)
Section StrassenUnderMaxFlow.
Variable (f : flow NF) (fmax : fmass f = ω).

(* -------------------------------------------------------------------- *)
Lemma fLE (a : option A) : f (⊤, ↓ (← a)) = c (⊤, ↓ (← a)).
Proof.
have := cweightE_cutL; rewrite sum_cLSE -fmax cweightE_cutL fmassE.
pose XA : {set vertex N} := [set ↓ (← a) | a : option A].
move/esym; rewrite (bigID (mem XA)) big_imset /= => [a1 a2 _ _ [//]|].
rewrite (eq_bigl xpredT) // addrC big1 ?add0r.
+ move=> v vXA; apply/flow_eq0; rewrite ffunE.
  * by elim/vtx_ind: v vXA => // [|a'] /imsetP[]; eexists.
  * by elim/vtx_ind: {vXA} v.
move/eqP; rewrite eq_le =>/andP[_ h]; apply/eqP.
apply/contraLR: h; rewrite eq_le le_NFfc -!ltNge => lt.
rewrite !(bigD1 (P := predT) a) //= ltr_le_add //.
by apply/ler_sum=> a' _; apply/le_NFfc.
Qed.

(* -------------------------------------------------------------------- *)
Lemma fRE (b : option B) : f (↓ (→ b), ⊥) = c (↓ (→ b), ⊥).
Proof.
have := cweightE_cutR; rewrite sum_cRSE -fmax cweightE_cutR fmass_snkE.
pose XB : {set vertex N} := [set ↓ (→ b) | b : option B].
move/esym; rewrite (bigID (mem XB)) big_imset /= => [b1 b2 _ _ [//]|].
rewrite (eq_bigl xpredT) // addrC big1 ?add0r.
+ move=> v vXB; apply/flow_eq0; rewrite ffunE.
  * by elim/vtx_ind: v vXB => // [|b'] /imsetP[]; eexists.
  * by elim/vtx_ind: {vXB} v.
move/eqP; rewrite eq_le =>/andP[_ h]; apply/eqP.
apply/contraLR: h; rewrite eq_le le_NFfc -!ltNge => lt.
rewrite !(bigD1 (P := predT) b) //= ltr_le_add //.
by apply/ler_sum=> b' _; apply/le_NFfc.
Qed.

(* -------------------------------------------------------------------- *)
Definition SμL_r (ab : A * option B) : R :=
  Ω ε * f (↓ (⇐ (ab.1)), ↓ (→ (ab.2))).

Definition SμR_r (ab : option A * B) : R :=
  f (↓ (← (ab.1)), ↓ (⇒ (ab.2))).

(* -------------------------------------------------------------------- *)
Lemma dweight_SμL : \sum_ab SμL_r ab = dweight μ1.
Proof.
rewrite /SμL_r; pose F a b := Ω ε * f (↓ (⇐ a), ↓ (→ b)).
rewrite -(pair_big xpredT xpredT F) /= {}/F pr_predT psum_fin.
apply/eq_bigr=> a _; rewrite ger0_norm // -mulr_sumr.
by rewrite -kcf_flowNFL fLE /c /= mulrA -ΩD subrr Ω0 mul1r.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dweight_SμR : \sum_ab SμR_r ab = dweight μ2.
Proof.
rewrite /SμR_r; pose F a b := f (↓ (← a), ↓ (⇒ b)).
rewrite -(pair_big xpredT xpredT F) /= {}/F pr_predT psum_fin.
rewrite exchange_big; apply/eq_bigr=> b _ /=; rewrite ger0_norm //.
by rewrite -kcf_flowNFR fRE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma isdistr_SμL : isdistr SμL_r.
Proof.
apply/isdistr_finP=> /=; split => [ab|].
+ by rewrite mulr_ge0 ?(ge0, ge0_flowNF).
+ by rewrite dweight_SμL le1_pr.
Qed.

(* -------------------------------------------------------------------- *)
Lemma isdistr_SμR : isdistr SμR_r.
Proof.
apply/isdistr_finP=> /=; split => [ab|].
+ by rewrite ge0_flowNF.
+ by rewrite dweight_SμR le1_pr.
Qed.

(* -------------------------------------------------------------------- *)
Definition SμL := nosimpl (mkdistr isdistr_SμL).
Definition SμR := nosimpl (mkdistr isdistr_SμR).

(* -------------------------------------------------------------------- *)
Lemma FinWeakStrassen : elift ε δ μ1 μ2 S.
Proof.
exists (SμL, SμR) => /=; split.
+ move=> a; rewrite dfstE psum_fin /= /SμL_r /=.
  have ->: μ1 a = Ω ε * c (⊤, ↓ (⇐ a)).
  - by rewrite /c /= mulrA -ΩD subrr Ω0 mul1r.
  rewrite -fLE kcf_flowNFL mulr_sumr; apply/eq_bigr.
  by move=> b _; rewrite normrM !ger0_norm // (ge0, ge0_flowNF).
+ move=> b; rewrite dsndE psum_fin /= /SμR_r /=.
  have ->: μ2 b = c (↓ (⇒ b), ⊥) by [].
  rewrite -fRE kcf_flowNFR; apply/eq_bigr.
  by move=> a _; rewrite ger0_norm // ge0_flowNF.
+ move=> a b /dinsuppP /=; rewrite /SμL_r /= => /eqP.
  rewrite mulf_eq0 gt_eqF ?gt0_Ω //=; set e := (X in f X).
  move=> nz_fe; have := le_NFfc f e; rewrite /c /=.
  case: S => //; rewrite mul0r le_eqVlt (negbTE (nz_fe)) /=.
  by rewrite ltNge ge0_flowNF.
+ move=> a b /dinsuppP /=; rewrite /SμR_r /= => /eqP.
  set e := (X in f X) => nz_fe; have := le_NFfc f e; rewrite /c /=.
  case: S => //; rewrite mul0r le_eqVlt (negbTE (nz_fe)) /=.
  by rewrite ltNge ge0_flowNF.
apply/edist_le=> //= X; rewrite !pr_dmargin.
pose P1 := [pred x | ((Some x.1, None) \in X) && (x.2 == None :> option B)].
pose P2 := [pred x | ((Some x.1, x.2 ) \in X) && (x.2 != None)].
set P := (X in X <= _); have {P}->: P = \P_[SμL] P1 + \P_[SμL] P2.
+ rewrite /P (prID _ (fun ab => ab.2 == None)) /=; congr +%R.
  apply/eq_in_pr=> /= -[a b] _; rewrite !inE /in_mem /=.
  by case: (b =P None) => [->|_]; rewrite !(andbT, andbF).
pose Q1 := [pred x | ((None, Some x.2) \in X) && (x.1 == None :> option A)].
pose Q2 := [pred x | ((x.1 , Some x.2) \in X) && (x.1 != None)].
set Q := (X in _ * X); have {Q}->: Q = \P_[SμR] Q1 + \P_[SμR] Q2.
+ rewrite /Q (prID _ (fun ab => ab.1 == None)) /=; congr +%R.
  apply/eq_in_pr=> /= -[a b] _; rewrite !inE /in_mem /=.
  by case: (a =P None) => [->|_]; rewrite !(andbT, andbF).
pose g a b := f (↓ (← a), ↓ (→ b)).
have {P1}->: \P_[SμL] P1 =
  Ω ε * \sum_(a : A | (Some a, None) \in X) g (Some a) None.
+ pose F a b := (P1 (a, b))%:R * SμL (a, b).
  rewrite pr_finE -(pair_big xpredT xpredT F) exchange_big /=.
  rewrite (bigD1 None) //= [X in _ + X]big1 ?addr0.
  - case=> // b _; rewrite {}/F /P1 big1 //.
    by move=> a _; rewrite inE /= andbF mul0r.
  rewrite mulr_sumr [RHS]big_mkcond {}/F /P1; apply/eq_bigr=> a _.
  by rewrite !inE /= eqxx andbT; case: ifP; rewrite !Monoid.simpm.
have {P2}->: \P_[SμL] P2 =
  Ω ε * \sum_(ab | (Some ab.1, Some ab.2) \in X) g (Some ab.1) (Some ab.2).
+ pose F a b := (P2 (a, b))%:R * SμL (a, b).
  rewrite pr_finE -(pair_big xpredT xpredT F) /=.
  rewrite exchange_big big_option big1 /= ?add0r.
  - by move=> a _; rewrite {}/F /P2; rewrite inE andbF mul0r.
  rewrite exchange_big pair_big mulr_sumr [RHS]big_mkcond /=.
  apply/eq_bigr=> -[a b] _ /=; rewrite /F /P2 !inE /=.
  by case: ifP=> //= _; rewrite !Monoid.simpm.
have {Q1}->: \P_[SμR] Q1 =
  \sum_(b : B | (None, Some b) \in X) g None (Some b).
+ pose F a b := (Q1 (a, b))%:R * SμR (a, b).
  rewrite pr_finE -(pair_big xpredT xpredT F) /=.
  rewrite (bigD1 None) //= [X in _ + X]big1 ?addr0.
  - case=> // a _; rewrite {}/F /Q1 big1 //.
    by move=> b _; rewrite inE /= andbF mul0r.
  rewrite [RHS]big_mkcond {}/F /Q1; apply/eq_bigr=> b _.
  by rewrite !inE /= eqxx andbT; case: ifP; rewrite !Monoid.simpm.
have {Q2}->: \P_[SμR] Q2 =
  \sum_(ab | (Some ab.1, Some ab.2) \in X) g (Some ab.1) (Some ab.2).
+ pose F a b := (Q2 (a, b))%:R * SμR (a, b).
  rewrite pr_finE -(pair_big xpredT xpredT F) big_option /= big1.
  - by move=> b _; rewrite {}/F /Q2 /= andbF mul0r.
  rewrite add0r pair_big [RHS]big_mkcond /=.
  apply/eq_bigr=> -[a b] _ /=; rewrite /F /Q2 !inE /=.
  by case: ifP=> //= _; rewrite !Monoid.simpm.
rewrite -ler_subl_addl -mulrDr -mulrBr opprD addrACA subrr addr0.
rewrite mulrBr ler_subl_addr ler_paddr //.
+ rewrite mulr_ge0 ?ge0_Ω //; apply/sumr_ge0.
  by move=> b _; apply/ge0_flowNF.
apply/(@le_trans _ _ (Ω ε * \sum_a g a None)).
+ rewrite ler_pmul2l ?gt0_Ω // big_mkcond /=.
  rewrite big_option ler_paddl //; first by apply/ge0_flowNF.
  by apply/ler_sum=> a _; case: ifP=> // _; apply/ge0_flowNF.
by rewrite /g -kcf_flowNFR fRE /c /= mulrA -ΩD subrr Ω0 mul1r.
Qed.
End StrassenUnderMaxFlow.

(* -------------------------------------------------------------------- *)
Theorem FinStrassen : elift ε δ μ1 μ2 S.
Proof.
case: (maxflow_mincut NF)=> f [hf fmax]; apply/(@FinWeakStrassen f).
case: fmax => /= C fmE; rewrite fmE (rwP eqP) eq_le geω_cut andbT.
by rewrite -fmE -cweight_cutR hf.
Qed.
End FinStrassen.

(* -------------------------------------------------------------------- *)
Section RLift.
Context {T : choiceType} {U : Type}.
Context (c : {fset T}) (f : c -> U) (x0 : U).

Definition rlift := fun x =>
  if @idP (x \in c) is ReflectT h then f [`h]%fset else x0.

Lemma rlift_val x : rlift (fsval x) = f x.
Proof.
rewrite /rlift; case: {-}_ / idP => // h; congr f.
by apply/eqP; rewrite eqE /= eqxx.
Qed.
End RLift.

Section DistrFinRestr.
Context {A : choiceType} (c : {fset A}) (μ : distr A).

Definition mfinrestr (x : c) := μ (val x).

Lemma mfinrestr_is_distr : isdistr mfinrestr.
Proof.
apply/isdistr_finP; split=> [x|]; first by apply/ge0_mu.
have /gerfin_psum -/(_ c) := summable_mu μ.
move/le_trans => /(_ _ (le1_mu μ)) /(le_trans _); apply.
by apply/ler_sum=> /= x _; rewrite ger0_norm.
Qed.

Definition dfinrestr := locked (mkdistr (mfinrestr_is_distr)).

Lemma dfinrestrE x : dfinrestr x = μ (val x).
Proof. by unlock dfinrestr. Qed.

Lemma pr_dfinrestr (X : pred c) :
  \P_[dfinrestr] X = \P_[μ] (rlift X false).
Proof.
rewrite [in RHS]/pr (psum_finseq (r := (enum_fset c))).
+ by apply/fset_uniq.
+ move=> x; rewrite {1}/in_mem /= mulf_eq0 negb_or => /andP[].
  by rewrite /rlift; case: {-}_ / idP => //; rewrite eqxx.
rewrite -big_fset_seq /= /pr psum_fin; apply/eq_bigr => /= x _.
by rewrite dfinrestrE rlift_val.
Qed.
End DistrFinRestr.

(* -------------------------------------------------------------------- *)
Section FinSuppStrassen.
Context {A B : choiceType}.
Context (ε δ : R) (μ1 : distr A) (μ2 : distr B).
Context (c1 : {fset A}) (c2 : {fset B}) (S : pred (A * B)).

Hypothesis (ge0_ε : 0 <= ε) (ge0_δ : 0 <= δ).
Hypothesis (hc1 : {subset dinsupp μ1 <= mem c1}).
Hypothesis (hc2 : {subset dinsupp μ2 <= mem c2}).

Hypothesis mono : forall X, \P_[μ1] X <=
  Ω ε * \P_[μ2] (fun y => `[< exists2 x, x \in X & S (x, y) >]) + δ.

(* FIXME: factor out facts about dfinrestr *)
Theorem FinSuppStrassen : elift ε δ μ1 μ2 S.
Proof.
pose ν1 : distr c1 := dfinrestr c1 μ1.
pose ν2 : distr c2 := dfinrestr c2 μ2.
pose p (x : c1 * c2) := S (val x.1, val x.2).
have h (X : pred c1) : \P_[ν1] X <=
  Ω ε * \P_[ν2] (fun y : c2 => [exists x in X, p (x, y)]) + δ.
+ rewrite pr_dfinrestr (le_trans (mono _)) // ler_add2r.
  rewrite ler_wpmul2l ?ge0_Ω // pr_dfinrestr.
  apply/le_in_pr=> b bsupp; rewrite /in_mem /=.
  case/asboolP=> a; rewrite {1}/rlift; case: {-}_ / idP => //.
  move=> ha Xa Sab; rewrite /rlift; case: {-}_ / idP; last first.
  * by move: bsupp; rewrite {1}/in_mem /= => /hc2.
  by move=> hb; apply/existsP; exists [`ha]%fset; rewrite Xa.
case: (FinStrassen (S := p) ge0_ε ge0_δ h) => {h} /=.
move=> -[η1 η2] /= [ν1E ν2E hs1 hs2 hed].
pose T1 := (A  * option  B)%type; pose T2 := (option  A *  B)%type.
pose U1 := (c1 * option c2)%type; pose U2 := (option c1 * c2)%type.
pose U  := (option c1 * option c2)%type.
pose f1 (xy : U1) := (val xy.1, omap val xy.2).
pose f2 (xy : U2) := (omap val xy.1, val xy.2).
pose ζ1 : distr T1 := dmargin f1 η1.
pose ζ2 : distr T2 := dmargin f2 η2.
exists (ζ1, ζ2) => /=; split.
+ move=> a; rewrite dlet_dlet; set fa := fun xy : U1 => dlet _ _.
  rewrite (eq_in_dlet (g := fun xy => dunit (val xy.1)) (nu := η1)) //=.
  * by move=> xy _ {}a; rewrite dlet_unit.
  case/boolP: (a \in c1) => ac1; last first.
  * rewrite dlet_eq0 => /= [[a' b'] _ /=|].
    - by apply/contra: ac1 => /eqP<-.
    apply/esym; apply/(dinsuppPn μ1); rewrite /in_mem.
    by apply/contra: ac1 => /hc1.
  have := ν1E [`ac1]%fset; rewrite dfinrestrE /= => <-.
  rewrite dmarginE !dletE /=; apply/eq_psum=> /=.
  by case=> [a' b'] /=; rewrite !dunit1E /=.
+ move=> b; rewrite dlet_dlet; set fb := fun xy : U2 => dlet _ _.
  rewrite (eq_in_dlet (g := fun xy => dunit (val xy.2)) (nu := η2)) //=.
  * by move=> xy _ {}b; rewrite dlet_unit.
  case/boolP: (b \in c2) => ac2; last first.
  * rewrite dlet_eq0 => /= [[a' b'] _ /=|].
    - by apply/contra: ac2 => /eqP<-.
    apply/esym; apply/(dinsuppPn μ2); rewrite /in_mem.
    by apply/contra: ac2 => /hc2.
  have := ν2E [`ac2]%fset; rewrite dfinrestrE /= => <-.
  rewrite dmarginE !dletE /=; apply/eq_psum=> /=.
  by case=> [a' b'] /=; rewrite !dunit1E /=.
+ move=> a b /dinsupp_dlet[/=] [] ha [hb|] h /=; last first.
  * by rewrite dunit1E [X in (_ (X _))%:R]eqE /= andbF eqxx.
  rewrite dunit1E  [X in (_ (X _))%:R]eqE /=; case: andP.
  * by case=> /eqP<- /eqP[<-] _; move/hs1: h.
  * by rewrite eqxx.
+ move=> a b /dinsupp_dlet[/=] [] [ha|] hb h /=; last first.
  * by rewrite dunit1E [X in (_ (X _))%:R]eqE /= eqxx.
  rewrite dunit1E  [X in (_ (X _))%:R]eqE /=; case: andP.
  * by case=> /eqP[<-] /eqP<- _; move/hs2: h.
  * by rewrite eqxx.
+ move: hed; rewrite /edist; case: ltrP => // _.
  set v1 : R := sup _; set v2 : R := sup _; suff ->: v1 = v2 by [].
  congr (sup _); rewrite predeqE => /= z; split; last first.
  * case=> /= q ->; pose rq (xy : U) := q (omap val xy.1, omap val xy.2).
    exists rq => /=; congr (_ - _ * _).
    - by rewrite !pr_dmargin; apply/eq_in_pr.
    - by rewrite !pr_dmargin; apply/eq_in_pr.
  case=> /= q ->; pose qr (xy : option A * option B) :=
    let a : option c1 := obind (rlift some None) xy.1 in
    let b : option c2 := obind (rlift some None) xy.2 in
    q (a, b).
  exists qr; congr (_ - _ * _).
  - rewrite !pr_dmargin; apply/eq_in_pr=> /= -[a b] _ //=.
    rewrite /in_mem /qr /= rlift_val; case: b => //= b.
    by rewrite rlift_val.    
  - rewrite !pr_dmargin; apply/eq_in_pr => /= -[a b] _ //=.
    rewrite /in_mem /qr /= rlift_val; case: a => //= a.
    by rewrite rlift_val.    
Qed.

End FinSuppStrassen.

(* -------------------------------------------------------------------- *)
Section CountableStrassen.
Context {A B : countType}.
Context (ε δ : R) (μ1 : distr A) (μ2 : distr B) (S : pred (A * B)).

Hypothesis (ge0_ε : 0 <= ε) (ge0_δ : 0 <= δ).

Definition E {T : countType} i : {fset T} :=
  seq_fset tt (pmap choice.unpickle (iota 0 i)).

Definition imS (X : pred A) :=
  [pred y | `[< exists2 x, x \in X & S (x, y) >]].

Hypothesis mono :
  forall X, \P_[μ1] X <= Ω ε * \P_[μ2] (imS X) + δ.

Let η1 n := (drestr (mem (E n)) μ1).
Let η2 n := (drestr (mem (E n)) μ2).
Let Δ  n := (Ω ε * \P_[μ2] (predC (mem (E n))) + δ).

Lemma ge0_Δ n : 0 <= Δ n.
Proof. by rewrite addr_ge0 // mulr_ge0 ?(ge0_Ω, ge0_pr). Qed.

Lemma mono_drestr n X :
  \P_[η1 n] X <= Ω ε * \P_[η2 n] (imS X) + Δ n.
Proof.
apply/(@le_trans _ _ (\P_[μ1] X)).
+ apply/le_mu_pr => a _ _; rewrite drestrE.
  by case: ifP => // _; rewrite ge0_mu.
apply/(le_trans (mono X)); rewrite addrA ler_add2r.
rewrite -mulrDr ler_wpmul2l ?ge0_Ω // pr_drestr.
rewrite -pr_or_indep => [b /andP[/=]|]; first by rewrite !inE negbK.
by apply/le_in_pr=> b _; rewrite !inE => ->; rewrite andbT orbN.
Qed.

Local Notation T := (distr (A * option B) * distr (option A * B))%type.

Local Notation elift_r n η :=
 [/\ dfst η.1 =1 η1 n, dsnd η.2 =1 η2 n
   , (forall a b, (a, Some b) \in dinsupp η.1 -> S (a, b))
   , (forall a b, (Some a, b) \in dinsupp η.2 -> S (a, b))
   & edist ε (deliftL η.1) (deliftR η.2) <= Δ n].

Local Notation R η := (forall a b,
  η.2 (Some a, b) <= η.1 (a, Some b) <= Ω ε * η.2 (Some a, b)).

Lemma elift_dfinrestr n : { η : T | elift_r n η /\ R η }.
Proof.
suff: elift ε (Δ n) (η1 n) (η2 n) S by move/(elift_bnd ge0_ε).
apply/(FinSuppStrassen (c1 := E n) (c2 := E n)) => //.
+ by apply/ge0_Δ.
+ by move=> x; rewrite dinsupp_restr => /andP[].
+ by move=> x; rewrite dinsupp_restr => /andP[].
+ by apply/mono_drestr.
Qed.

Let ηL n : distr (A * option B) := (tag (elift_dfinrestr n)).1.
Let ηR n : distr (option A * B) := (tag (elift_dfinrestr n)).2.

Let ω : nat -> nat := tag (strcvg2 ηL ηR).

Local Lemma homo_ω : {homo ω : x y / (x < y)%N}.
Proof. by rewrite /ω; case: strcvg2. Qed.

Let ξL : distr (A * option B) := dlim (ηL \o ω).
Let ξR : distr (option A * B) := dlim (ηR \o ω).

Local Lemma iscvg_ηL x : iscvg (fun n => ηL (ω n) x).
Proof. by rewrite /ω; case: strcvg2 => /= h _ []. Qed.

Local Lemma iscvg_ηR x : iscvg (fun n => ηR (ω n) x).
Proof. by rewrite /ω; case: strcvg2 => /= h _ []. Qed.

Lemma Strassen : elift ε δ μ1 μ2 S.
Proof.
pose GL a := if a is Some a then       μ1 a else 1.
pose GR b := if b is Some b then Ω ε * μ2 b else 1.
have sblGl: summable GL by apply/summable_option/summable_mu.
have sblGR: summable GR by apply/summable_option/summableZ.
have le_μ1 n a : η1 n a <= μ1 a.
+ by rewrite drestrE; case: ifP => // _; apply/ge0_mu.
have le_μ2 n b : η2 n b <= μ2 b.
+ by rewrite drestrE; case: ifP => // _; apply/ge0_mu.
have hLL n a : psum (fun b => ηL n (a, b)) <= μ1 a.
+ by rewrite -dfstE exlift_dfstL le_μ1.
have hRR n b : psum (fun a => ηR n (a, b)) <= μ2 b.
+ by rewrite -dsndE exlift_dsndR le_μ2.
have hLR n a (b : option B) : ηL n (a, b) <= GR b.
+ case: b => /= [b|]; last by apply/le1_mu1.
  apply/(le_trans (exlift_leLR _ _ _)).
  rewrite ler_wpmul2l ?ge0_Ω // (le_trans _ (le_μ2 n _)) //.
  rewrite -(exlift_dsndR (elift_dfinrestr _)) -!/(ηR _) dsndE /=.
  rewrite (le_trans _ (gerfinseq_psum (r := [:: Some a]) _ _)) //.
  - by rewrite big_seq1 ler_norm. - by apply/summable_snd.
have hRL n (a : option A) b : ηR n (a, b) <= GL a.
+ case: a => /= [a|]; last by apply/le1_mu1.
  rewrite (le_trans (exlift_leRL _ _ _)) 1?(le_trans _ (le_μ1 n _)) //.
  rewrite -(exlift_dfstL (elift_dfinrestr _)) -!/(ηL _) dfstE /=.
  rewrite (le_trans _ (gerfinseq_psum (r := [:: Some b]) _ _)) //.
  - by rewrite big_seq1 ler_norm. - by apply/summable_fst.
pose FL a n (b : option B) := ηL (ω n) (a, b).
pose FR b n (a : option A) := ηR (ω n) (a, b).
exists (ξL, ξR) => /=; split => [a|b|||].
+ rewrite dfstE (eq_psum (F2 := fun b => real_of_er (nlim ((FL a)^~ b)))) /=.
  * by move=> b; rewrite [in LHS]dlimE.
  transitivity (real_of_er (nlim (fun n => psum (FL a n)))).
  * rewrite (@DCT_swap _ _ (fun b => ξL (a, b)) GR) => //=.
    - move=> b; rewrite dlimE /FL; case: (iscvg_ηL (a, b)).
      by move=> l hl; rewrite (nlimE hl).
    - by move=> n b; rewrite ger0_norm // (ge0_mu, hLR).
  pose pa := choice.pickle a; have ->: μ1 a = real_of_er (nlim (fun n => η1 (ω n) a)).
  * rewrite -(nlim_lift _ pa.+1) (eq_nlim (v := (μ1 a)%:S)) ?nlimC //.
    move=> n /=; rewrite drestrE /E /= sort_keysE mem_pmap.
    case: mapP => // -[]; exists pa; rewrite ?choice.pickleK //.
    rewrite mem_iota leq0n add0n (@leq_trans (n + pa.+1)) //.
    - by rewrite leq_addl.
    - by apply/homo_geidfun/homo_ω.
  congr real_of_er; apply/eq_nlim => n /=.
  by rewrite -(exlift_dfstL (elift_dfinrestr _)) dfstE.
+ rewrite dsndE (eq_psum (F2 := fun a => real_of_er (nlim ((FR b)^~ a)))) /=.
  * by move=> a; rewrite [in LHS]dlimE.
  transitivity (real_of_er (nlim (fun n => psum (FR b n)))).
  * rewrite (@DCT_swap _ _ (fun a => ξR (a, b)) GL) => //=.
    - move=> a; rewrite dlimE /FR; case: (iscvg_ηR (a, b)).
      by move=> l hl; rewrite (nlimE hl).
    - by move=> n a; rewrite ger0_norm // (ge0_mu, hRL).
  pose pb := choice.pickle b; have ->: μ2 b = real_of_er (nlim (fun n => η2 (ω n) b)).
  * rewrite -(nlim_lift _ pb.+1) (eq_nlim (v := (μ2 b)%:S)) ?nlimC //.
    move=> n /=; rewrite drestrE /E /= sort_keysE mem_pmap.
    case: mapP => // -[]; exists pb; rewrite ?choice.pickleK //.
    rewrite mem_iota leq0n add0n (@leq_trans (n + pb.+1)) //.
    - by rewrite leq_addl.
    - by apply/homo_geidfun/homo_ω.
  congr real_of_er; apply/eq_nlim => n /=.
  by rewrite -(exlift_dsndR (elift_dfinrestr _)) dsndE.
+ by move=> a b /dinsupp_dlim [K] /(_ _ (leqnn _)) /exlift_dsuppL.
+ by move=> a b /dinsupp_dlim [K] /(_ _ (leqnn _)) /exlift_dsuppR.
apply/edist_le_supp => //= X subX.
pose L n : elift.R := \P_[deliftL (ηL (ω n))] X.
pose R n : elift.R := \P_[deliftR (ηR (ω n))] X.
have cvgL: ncvg L (\P_[deliftL ξL] X)%:E.
* pose F n a b := (X (a, b))%:R * (deliftL (ηL (ω n)) (a, b)).
  pose G n := psum (fun a => psum (fun b => F n a b)).
  apply/(ncvg_eq (v := G)); rewrite {}/L {}/G /=.
  - by move=> n; rewrite /pr psum_pair //=; apply/summable_condl.
  pose G (a : option A) b := (X (a, b))%:R * deliftL ξL (a, b).
  rewrite /pr psum_pair /=; first by apply/summable_condl.
  move=> [: hcv1]; apply/(@DCT_ncvg _ _ (fun a => (psum (G a))) GL) => //=.
  - abstract: hcv1 => a /=; apply (@DCT_ncvg _ _ (G a) GR) => //=.
    + move=> b; apply/ncvgZ; case: a => /= [a|].
      * apply/(@ncvg_eq _ (fun n => ηL (ω n) (a, b))).
        - by move=> n /=; rewrite deliftLE.
        rewrite deliftLE /ξL; case: (iscvg_ηL (a, b)).
        by move=> l hl; rewrite dlimE (nlimE hl).
      * apply/(@ncvg_eq _ 0%:S) => [n|].
        - by rewrite deliftLE.
        - by rewrite deliftLE; apply/ncvgC.
    + move=> n b; rewrite ger0_norm ?mulr_ge0 ?(ler0n, ge0_mu) //.
      rewrite (@le_trans _ _ (deliftL (ηL (ω n)) (a, b))) //.
      * by rewrite ler_pimull ?ge0_mu // lern1 leq_b1.
      case: a => /= [a|]; first by rewrite deliftLE hLR.
      rewrite deliftLE /= /GR; case: b => /= [b|].
      * by rewrite mulr_ge0 ?(ge0_mu, ge0_Ω).
      * by rewrite ler01.
  - move=> n a; rewrite ger0_norm ?ge0_psum //; case: a => /=.
    + move=> a; apply/(le_trans _ (hLL (ω n) _))/le_psum => /=.
      * move=> b; rewrite /F deliftLE mulr_ge0 //= ?ler0n //.
        by rewrite ler_pimull // lern1 leq_b1.
      * by apply/summable_fst.
    + by rewrite psum_eq0 ?ler01 //= => b; rewrite /F deliftLE mulr0.
have cvgR: ncvg R (\P_[deliftR ξR] X)%:E.
* pose F n a b := (X (a, b))%:R * (deliftR (ηR (ω n)) (a, b)).
  pose G n := psum (fun b => psum (fun a => F n a b)).
  apply/(ncvg_eq (v := G)); rewrite {}/R  {}/G /=.
  - by move=> n; rewrite /pr psum_pair_swap //=; apply/summable_condl.
  rewrite /pr psum_pair_swap /=; first by apply/summable_condl.
  pose G (b : option B) a := (X (a, b))%:R * deliftR ξR (a, b).
  move=> [: hcv1]; apply/(@DCT_ncvg _ _ (fun b => (psum (G b))) GR) => //=.
  - abstract: hcv1 => b /=; apply (@DCT_ncvg _ _ (G b) GL) => //=.
    + move=> a; apply/ncvgZ; case: b => /= [b|].
      * apply/(@ncvg_eq _ (fun n => ηR (ω n) (a, b))).
        - by move=> n /=; rewrite deliftRE.
        rewrite deliftRE /ξR; case: (iscvg_ηR (a, b)).
        by move=> l hl; rewrite dlimE (nlimE hl).
      * apply/(@ncvg_eq _ 0%:S) => [n|].
        - by rewrite deliftRE.
        - by rewrite deliftRE; apply/ncvgC.
    + move=> n a; rewrite ger0_norm ?mulr_ge0 ?(ler0n, ge0_mu) //.
      rewrite (@le_trans _ _ (deliftR (ηR (ω n)) (a, b))) //.
      * by rewrite ler_pimull ?ge0_mu // lern1 leq_b1.
      case: b => /= [b|]; first by rewrite deliftRE hRL.
      rewrite deliftRE /= /GL; case: a => /= [a|].
      * by rewrite ge0_mu. * by rewrite ler01.
  - move=> n b; rewrite ger0_norm ?ge0_psum //; case: b => /=.
    + move=> b; apply/(@le_trans _ _ (μ2 b)); last first.
      * by rewrite ler_pemull // Ω_ge1.
      apply/(le_trans _ (hRR (ω n) _))/le_psum => /=.
      * move=> a; rewrite /F deliftRE mulr_ge0 //= ?ler0n //.
        by rewrite ler_pimull // lern1 leq_b1.
      * by apply/summable_snd.
    + by rewrite psum_eq0 ?ler01 //= => b; rewrite /F deliftRE mulr0.
rewrite addrC -ler_subl_addr; set V := (X in X <= _).
suff cvgΔ: ncvg Δ δ%:E.
* move/(ncvg_sub homo_ω)/ncvg_le: cvgΔ => /(_ (L \- Ω ε \*o R) V%:E) /=.
  apply=> [n|]; last by apply/ncvgB/ncvgZ.
  rewrite ler_subl_addr addrC /L /R.
  have := exlift_edist (elift_dfinrestr (ω n)) => /edist_le.
  by move/(_ ge0_ε X); rewrite -/(ηL _) -/(ηR _).
rewrite -[δ]add0r -[X in (X + _)%:E](mulr0 (Ω ε)).
apply/ncvgD/ncvgC/ncvgZ; rewrite -[X in X%:E](@psum0 _ B).
apply/(DCT_ncvg (g := μ2)) => //; last first.
* move=> n b; rewrite ger0_norm ?mulr_ge0 ?ler0n //.
  by rewrite ler_pimull // lern1 leq_b1.
move=> b; apply/ncvgMl; last first.
* apply/asboolP/nboundedP; exists 2%:R => // _.
  apply/(@le_lt_trans _ _ 1) => //; last by rewrite (@ltr_nat _ 1).
  by rewrite ger0_norm // le1_mu1.
elim/nbh_finW => /= e gt0_e; exists (choice.pickle b).+1 => n le_bn.
rewrite inE subr0; apply/(le_lt_trans _ gt0_e).
rewrite normr_le0 pnatr_eq0 eqb0 negbK /E seq_fsetE.
rewrite mem_pmap; apply/mapP; exists (choice.pickle b).
* by rewrite mem_iota /= add0n.
* by rewrite choice.pickleK.
Qed.
End CountableStrassen.
