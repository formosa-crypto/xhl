(* -------------------------------------------------------------------- *)
From HB       Require Import structures.
From mathcomp Require Import boot order algebra.
(* ------- *) Require Import xbigops misc lp.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Delimit Scope syntax_scope with T.

(* -------------------------------------------------------------------- *)
Section Vertex.
Context {T : Type}.

Inductive vertex := Vertex of (bool + T).

Definition vertex_val (v : vertex) : bool + T :=
  let: Vertex v := v in v.

HB.instance Definition _ := [isNew for vertex_val].

End Vertex.

Arguments vertex T : clear implicits.

HB.instance Definition _ (T : eqType) := [Equality of vertex T by <:].
HB.instance Definition _ (T : choiceType) := [Choice of vertex T by <:].
HB.instance Definition _ (T : countType) := [Countable of vertex T by <:].
HB.instance Definition _ (T : finType) := [Finite of vertex T  by <:].

(* -------------------------------------------------------------------- *)
Notation "↓ x" := (Vertex (inr x)) (at level 2).
Notation "⊤"   := (Vertex (inl true )) (at level 0).
Notation "⊥"   := (Vertex (inl false)) (at level 0).

Local Notation edge T := (vertex T * vertex T)%type.

(* -------------------------------------------------------------------- *)
Section MaxFlow.
Context {R : realFieldType}.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'network' T }"
  (at level 0, format "{ 'network'  T }").

Reserved Notation "{ 'flow' g }"
  (at level 0, format "{ 'flow'  g }").

Reserved Notation "g .-flow"
  (at level 2, format "g .-flow").

(* -------------------------------------------------------------------- *)
Section VertexW.
Context (T : Type) (P : vertex T -> Prop).

Hypothesis Psrc : P ⊤.
Hypothesis Pdst : P ⊥.
Hypothesis Pgrd : forall u, P ↓u.

Lemma vertexW : forall u, P u.
Proof. by case=> -[[]|]. Qed.
End VertexW.

(* -------------------------------------------------------------------- *)
Section Network.
Context {T : finType}.

Definition isnetwork (f : edge T -> R) := [forall e, 0 <= f e].

Lemma networkP (f : edge T -> R) :
  reflect (forall e, 0 <= f e) (isnetwork f).
Proof. by apply/forallP. Qed.

Record network : predArgType := Network
  { capacity :> {ffun edge T -> R}; _ : isnetwork capacity; }.

HB.instance Definition _ := [isSub of network for capacity].

HB.instance Definition _ := [Equality of network by <:].

End Network.

Notation "{ 'network' T }" := (@network T).

Lemma network_ge0 {T : finType} (g : {network T}) e : 0 <= g e.
Proof. by case: g => /= g /networkP /(_ e). Qed.

Hint Immediate network_ge0 : core.

(* -------------------------------------------------------------------- *)
Section Flow.
Context {T : finType}.

Definition isflow (g : {network T}) : pred (edge T -> R) :=
  [pred f : edge T -> R |
     [&& [forall e : edge T, f e <= g.(capacity) e]
       , [forall u, forall v, f (u, v) == - f (v, u)]
       & [forall u, (\sum_v f (↓u, v) == 0)]]].

Definition IsFlow (g : {network T}) : qualifier 1 _ :=
  Qualifier 1 (fun f => isflow g f).

Fact IsFlow_key g : pred_key (IsFlow g). Proof. by []. Qed.
Definition IsFlow_keyed g := KeyedQualifier (IsFlow_key g).

Notation "g .-flow" := (IsFlow g).

(* -------------------------------------------------------------------- *)
Definition fmass (f : edge T -> R) := \sum_v f(⊤, v).

Lemma fmassE f : fmass f = \sum_v f(⊤, v).
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Section IsFlowTh.
Context (g : {network T}) (f : edge T -> R).

Hypothesis fl_f : f \is a g.-flow.

Lemma isflow_lecp (e : edge T) : f e <= g e.
Proof. by have /and3P[h _ _] := fl_f; move/forallP: h. Qed.

Lemma isflow_antisym u v : f (u, v) = - f (v, u).
Proof. by have /and3P[_ h _] := fl_f; move/'forall_'forall_eqP: h. Qed.

Lemma isflow_kirchnoff u : \sum_v f (↓ u, v) = 0.
Proof. by have /and3P[_ _] := fl_f => /'forall_eqP. Qed.
End IsFlowTh.

Record flow (g : {network T}) : predArgType := Flow
  { fun_of_flow :> edge T -> R; _ : fun_of_flow \is a g.-flow }.

HB.instance Definition _ g := [isSub of flow g for @fun_of_flow g].

End Flow.

(* -------------------------------------------------------------------- *)
Notation "g .-flow" := (IsFlow g).

(* -------------------------------------------------------------------- *)
Lemma isflowP {T : finType} (g : {network T}) (f : edge T -> R) :
     (forall e, f e <= g e)
  -> (forall u v, f (u, v) = - f (v, u))
  -> (forall u, \sum_v f (↓u, v) = 0)
  -> f \is a g.-flow.
Proof.
move=> lecp asym eq0; apply/and3P; split.
+ by apply/forallP. + by apply/'forall_'forall_eqP.
by apply/forallP=> x; rewrite eq0 eqxx.
Qed.

(* -------------------------------------------------------------------- *)
Section CoreFlowTheory.
Context {T : finType} (g : {network T}) (f : flow g).

Lemma isflow_0 : (fun _ => 0) \is a g.-flow.
Proof. apply/isflowP => [e|_ _| _].
+ by apply/network_ge0. + by rewrite oppr0. + by rewrite big1.
Qed.

Lemma eq_isflow f1 f2 :
  (f1 =1 f2) -> f1 \is a g.-flow -> f2 \is a g.-flow.
Proof.
move=> eqf hf1; apply/isflowP=> [e|u v|u].
+ by rewrite -eqf; apply/(isflow_lecp hf1).
+ by rewrite -!eqf; apply/(isflow_antisym hf1).
+ rewrite -[RHS](isflow_kirchnoff hf1 u).
  by apply/eq_bigr=> v _; rewrite eqf.
Qed.

Lemma isflow_flow : (fun_of_flow f) \is a g.-flow.
Proof. by apply/valP. Qed.

Hint Resolve isflow_flow : core.

Lemma flow_lecp e : f e <= g e.
Proof. by apply/isflow_lecp. Qed.

Lemma flow_antisym u v : f (u, v) = - f (v, u).
Proof. by apply/(isflow_antisym isflow_flow). Qed.

Lemma flow_kirchnoff u : \sum_v f (↓u, v) = 0.
Proof. by apply/(isflow_kirchnoff isflow_flow). Qed.

Lemma flow_self u : f (u, u) = 0.
Proof.
have /eqP := flow_antisym u u; rewrite -addr_eq0 -mulr2n.
by rewrite -mulr_natl mulf_eq0 pnatr_eq0 => /eqP.
Qed.

Lemma flow_ge0 u v: g (u, v) = 0 -> 0 <= f (v, u).
Proof.
move=> zg; rewrite flow_antisym oppr_ge0.
by rewrite -zg; apply/flow_lecp.
Qed.

Lemma flow_eq0 u v: g (u, v) = 0 -> g(v, u) = 0 -> f (u, v) = 0.
Proof.
move=> zg1 zg2; apply/eqP; rewrite eq_le.
by rewrite flow_ge0 // andbT flow_antisym oppr_le0 flow_ge0.
Qed.
End CoreFlowTheory.

(* -------------------------------------------------------------------- *)
Section Residual.
Context {T : finType} (g : {network T}) (f : flow g).

Definition preresidual (e : edge T) : R := g e - f e.

Lemma network_residual : isnetwork (finfun preresidual).
Proof. by apply/networkP=> e; rewrite ffunE subr_ge0 flow_lecp. Qed.

Definition residual : {network T} := Network network_residual.

Lemma residualE e : residual e = g e - f e.
Proof. by rewrite ffunE. Qed.
End Residual.

(* -------------------------------------------------------------------- *)
Section AddFlow.
Context {T : finType} {g : {network T}}.
Context (f : flow g) (fp : flow (residual f)).

Lemma isflow_addflow : (f \+ fp) \is a g.-flow.
Proof. apply/isflowP => [e|u v|u] /=.
+ by have := flow_lecp fp e; rewrite residualE lerBrDl.
+ by rewrite opprD [f _]flow_antisym [fp _]flow_antisym.
+ by rewrite big_split /= !flow_kirchnoff addr0.
Qed.

Definition addflow := Flow isflow_addflow.

Lemma addflowE e : addflow e = f e + fp e.
Proof. by []. Qed.

Lemma fmassD : fmass addflow = fmass f + fmass fp.
Proof. by rewrite !fmassE big_split. Qed.
End AddFlow.

Local Notation "`| f |" := (fmass f).
Local Notation "f \+ g" := (addflow f g).

(* -------------------------------------------------------------------- *)
Section AugmentingPath.
Context {T : finType} (g : {network T}) (f : flow g).

Definition spath (s : seq T) :=
  let s : seq (vertex T) := [seq ↓u | u <- s] in
  path [rel x y | 0 < residual f (x, y)] ⊤ (rcons s ⊥).

Inductive apath := APath (s : seq T) of uniq s && spath s.

Definition apath_proj (p : apath) :=
  let: APath p _ := p in p.

HB.instance Definition _ := [isSub for apath_proj].
HB.instance Definition _ := [Equality of apath by <:].
HB.instance Definition _ := [Choice of apath by <:].
HB.instance Definition _ := [Countable of apath by <:].

Definition aenum : seq apath :=
  pmap insub (flatten
    [seq [seq val s | s <- enum {: n.-tuple T}] | n <- iota 0 #|T|.+1]).

Lemma uniq_aenum : uniq aenum.
Proof.
rewrite /aenum -(map_inj_uniq (@Some_inj _)) pmapS_filter.
rewrite map_inj_in_uniq.
+ move=> x y; rewrite !mem_filter => /andP[hx _] /andP[hy _].
  rewrite !insubT //=; try by rewrite !isSome_insub in hx, hy.
  by move=> py px; case.
apply/filter_uniq; elim: #|T|.+1 0%N => //= n ih k; rewrite cat_uniq.
rewrite (map_inj_uniq val_inj) enum_uniq /= ih andbT; apply/hasPn=> /=.
move=> s /flatten_mapP /= [j]; rewrite mem_iota ltn_neqAle.
case/andP=> /andP[] ne_kj _ _ /mapP /= [t _ ->]; apply/negP.
case/mapP=> /= t' _ /(congr1 size); rewrite !size_tuple.
by move=> eq; move: ne_kj; rewrite eq eqxx.
Qed.

Lemma aenum_finAxiom : Finite.axiom aenum.
Proof.
move=> s; rewrite count_uniq_mem ?uniq_aenum // (rwP eqP) eqb1.
case: s=> s Ps; rewrite -(mem_map (@Some_inj _)) pmapS_filter.
apply/mapP; exists s; rewrite ?insubT //.
rewrite mem_filter insubT; apply/flattenP.
pose t := map val (enum {: (size s).-tuple T}); exists t.
+ apply/mapP; exists (size s) => //; rewrite mem_iota /= add0n.
  by case/andP: Ps => /card_uniqP <- _; rewrite ltnS max_card.
by apply/mapP=> /=; exists (in_tuple s) => //; rewrite mem_enum.
Qed.

HB.instance Definition _ := @isFinite.Build _ aenum aenum_finAxiom.

Coercion path_of_apath (p : apath) :=
  let: APath p _ := p in ⊤ :: (rcons [seq ↓u | u <- p] ⊥).

Lemma size_apath (p : apath) : (size p <= #|T|.+2)%N.
Proof.
case: p => p /= /andP[uqP _]; rewrite size_rcons !ltnS size_map.
by move/card_uniqP: uqP => <-; apply/max_card.
Qed.

Lemma uniq_apath (a : apath) : uniq a.
Proof.
case: a => /= a /andP[uq _]; rewrite !(mem_rcons, rcons_uniq).
rewrite map_inj_uniq ?uq ?andbT => [u1 u2 [//]|].
by apply/andP; split; apply/negP => /mapP[].
Qed.

(* -------------------------------------------------------------------- *)
Definition asegment (a : seq (vertex T)) (e : edge T) :=
  [&& ((e.1 != ⊥) && (e.2 != ⊤)), e.1 != e.2 & next a e.1 == e.2].

Lemma asegmentP (a : apath) (e : edge T) :
  asegment a e -> f e < g e.
Proof.
pose ep := [rel x y | ((x, y) == (⊥, ⊤)) || (0 < residual f (x, y))].
move=> h; have hc: cycle ep (a : seq _); first rewrite (cycle_path ⊤).
+ case: {h} a => a /=; rewrite last_rcons /= => /andP[_].
  by apply/sub_path => /= u v /= h; rewrite /ep /= h orbT.
case/and3P: h => nz_e neq_e hnx; have: e.1 \in (a : seq _).
+ by move: hnx; rewrite next_nth; case: ifP => // _; apply/contraLR.
move/next_cycle => -/(_ _ hc); rewrite (eqP hnx) /eq /=.
case: {neq_e hnx} e nz_e => u v /=; rewrite [_ (u, v)]eqE /=.
case/andP=> [/negbTE->] _; rewrite ffunE /=.
by rewrite /preresidual subr_gt0.
Qed.

Lemma nz_apath (a : apath) : exists e, asegment a e.
Proof.
exists (nth ⊤ a 0, nth ⊤ a 1) => /=; case: a => /= a _.
by rewrite /asegment; case: a => /=.
Qed.

Lemma next_snk (a : apath) : next a ⊥ = ⊤.
Proof.
rewrite next_nth; case: a => /= a _.
rewrite mem_behead /= ?mem_rcons // -cats1.
rewrite index_cat; case: ifPn => [/mapP[//]|_].
rewrite size_map /= addn0; set s := _ ++ _.
case E: s => [|x s'] //; rewrite nth_default //.
move/(congr1 size): E; rewrite {}/s size_cat /= addn1.
by case=> <-; rewrite size_map.
Qed.

Lemma prev_src (a : apath) : prev a ⊤ = ⊥.
Proof.
rewrite (rwP eqP) -(inj_eq (can_inj (prev_next (uniq_apath a)))).
by rewrite next_prev ?uniq_apath // next_snk.
Qed.

Definition aweight (a : apath) : R :=
  residual f (arg_minr (residual f) (nz_apath a)).

Lemma aweight_gt0 (a : apath) : 0 < aweight a.
Proof.
rewrite /aweight; case: arg_minrP => /= e he _.
by rewrite ffunE /preresidual subr_gt0 (asegmentP he).
Qed.

Lemma aweight_ge0 (a : apath) : 0 <= aweight a.
Proof. by apply/ltW/aweight_gt0. Qed.

Lemma aweight_flow_le (a : apath) (e : edge T) :
  asegment a e -> aweight a <= residual f e.
Proof.
by move=> he; rewrite /aweight; case: arg_minrP => e' _ /(_ _ he).
Qed.

Lemma asegment_meml a e : asegment a e -> e.1 \in a.
Proof.
case: e => u v /= /and3P[/= _ /eqP ne_uv].
by rewrite next_nth; case: (_ \in _) => // /eqP.
Qed.

Lemma asegment_memr a e : asegment a e -> e.2 \in a.
Proof.
move=> h; have := asegment_meml h; case: e h => u v /=.
by case/and3P=> /= _ _ /eqP <-; rewrite mem_next.
Qed.

Lemma asegment_injr (a : apath) u v1 v2 :
  asegment a (u, v1) -> asegment a (u, v2) -> v1 = v2.
Proof. by move=> /and3P[/= _ _ /eqP <-] /and3P[/= _ _ /eqP <-]. Qed.

Lemma asegment_injl (a : apath) u1 u2 v :
  asegment a (u1, v) -> asegment a (u2, v) -> u1 = u2.
Proof.
move=> /and3P[/= _ ne1 /eqP h1] /and3P[/= _ ne2 /eqP h2].
by apply/(can_inj (prev_next (uniq_apath a))); rewrite h1 h2.
Qed.

Lemma asegment0 (a : apath) u v :
  val a = [::] -> asegment a (u, v) -> (u, v) = (⊤, ⊥).
Proof.
case: a => /= a _ -> /and3P[/= ne1 ne2].
case: ifPn => [/eqP->/eqP<-//|] ne3 /eqP vE.
by case: ifPn vE ne1 ne2 => [/eqP-><-//|_ ->]; rewrite eqxx.
Qed.

Lemma asegment_src (a : apath) : asegment a (⊤, next a ⊤).
Proof.
by apply/and3P; split=> //; case: a => /= a _; case: a.
Qed.

Lemma asegmentN_src_snk (a : apath) : ~~ asegment a (⊥, ⊤).
Proof. by apply/negP; case/and3P. Qed.

Lemma apath_neq_next (a : apath) u :
  ↓ u \in (a : seq _) -> ↓ u != next a (↓ u).
Proof.
have: (2 <= size a)%N by case: a => /= a; rewrite size_rcons !ltnS.
move=> sz ua; rewrite head_rot_index ?uniq_apath //.
move/path.splitP: ua sz (uniq_apath a) => [p1 p2]; rewrite rotS.
+ by rewrite index_mem mem_cat mem_rcons mem_head.
rewrite size_cat size_rcons addSn ltnS addnC -size_cat => sz.
rewrite -cats1 -catA uniq_catCA => /= /andP[h _].
move: h; rewrite mem_cat negb_or => /andP[h1 h2].
rewrite index_cat (negbTE h1) /= eqxx addn0 rot_size_cat.
have h: ↓ u \notin (p2 ++ p1) by rewrite mem_cat (negbTE h2).
move: sz; rewrite /= rot1_cons; case: (p2 ++ p1) h => //.
by move=> x s; rewrite in_cons negb_or => /andP[].
Qed.

Lemma apath_neq_prev (a : apath) u :
  ↓ u \in (a : seq _) -> ↓ u != prev a (↓ u).
Proof.
rewrite -(inj_eq (can_inj (prev_next (uniq_apath a)))).
by rewrite next_prev ?uniq_apath // eq_sym; apply/apath_neq_next.
Qed.

Lemma asegment_next (a : apath) v :
  ↓ v \in (a : seq _) -> asegment a (↓ v, next a (↓ v)).
Proof.
move=> va; apply/and3P; split=> //=; last by apply/apath_neq_next.
rewrite -(inj_eq (can_inj (next_prev (uniq_apath a)))).
by rewrite prev_next ?uniq_apath // prev_src.
Qed.

Lemma asegment_prev (a : apath) v :
  ↓ v \in (a : seq _) -> asegment a (prev a (↓ v), ↓ v).
Proof.
move=> va; apply/and3P; split=> //=; rewrite ?andbT.
+ rewrite -(inj_eq (can_inj (prev_next (uniq_apath a)))).
  by rewrite next_prev ?uniq_apath // next_snk.
+ by rewrite eq_sym apath_neq_prev.
+ by rewrite next_prev ?uniq_apath.
Qed.

Lemma asegment_asym (a : apath) u v :
  asegment a (u, v) -> ~~ asegment a (v, u).
Proof.
move=> ae; case: (val a =P [::]) => [|nz_a].
+ by move/asegment0/(_ ae)=> [-> ->]; apply/asegmentN_src_snk.
case/and3P: ae => /= _ _ /eqP<-; apply/negP; case/and3P=> /= ne.
rewrite {1}next_nth; case/boolP: (u \in (_ a)) => //; last first.
+ by move=> _; rewrite eqxx.
move=> ua _; suff: exists v1 v2, exists s, [/\ u <> v1, u <> v2 &
  rot (index u a) a = u :: v1 :: v2 :: s].
+ case=> [v1] [v2] [s] [/eqP ne1 /eqP ne2 eq] /=.
  rewrite -[next a u](next_rot (index u a)) ?uniq_apath // eq.
  rewrite /= eqxx -[next a v1](next_rot (index u a)) ?uniq_apath //.
  by rewrite eq /= ![_==u]eq_sym (negbTE ne1) eqxx (negbTE ne2).
have: (3 <= size a)%N.
+ case: {ne ua} a nz_a => /= a _; case: a => //.
  by move=> x a _; rewrite size_rcons !ltnS.
case: (path.splitP ua) (uniq_apath a) => p1 p2.
rewrite size_cat size_rcons addSn ltnS -size_cat.
rewrite -{1}cats1 -catA -(rot_uniq (size p1)) rot_size_cat /=.
rewrite mem_cat negb_or => /andP[/andP[hm2 hm1] _].
rewrite index_cat mem_rcons mem_head -{1}cats1.
rewrite index_cat (negbTE hm1) /= eqxx addn0.
rewrite -cats1 -catA rot_size_cat /= size_cat addnC -size_cat.
have: u \notin (p2 ++ p1) by rewrite mem_cat negb_or hm2.
case: (p2 ++ p1) => // v1 [] // v2 s h _; exists v1, v2, s.
move: h; rewrite !in_cons !negb_or => /and3P.
by case=> /eqP h1 /eqP h2 _; split.
Qed.

(* -------------------------------------------------------------------- *)
Definition preflow_of_apath (a : apath) := fun (e : edge T) =>
  if asegment a (e.1, e.2) then   aweight a else
  if asegment a (e.2, e.1) then - aweight a else 0.

Lemma preflow_of_apath_is_flow (a : apath) :
  preflow_of_apath a \is a (residual f).-flow.
Proof. apply/isflowP => [e|u v|v].
- rewrite /preflow_of_apath; case: ifPn => [|_].
  + by move=> /aweight_flow_le; case: e.
  case: ifPn => _; last by rewrite network_ge0.
  apply/(@le_trans _ _ 0)/network_ge0.
  by rewrite oppr_le0 aweight_ge0.
- rewrite /preflow_of_apath /=; case: ifPn.
  + by move/asegment_asym/negbTE=> ->; rewrite opprK.
  by move=> _; case: ifPn => // _; rewrite oppr0.
- case/boolP: (↓ v \in (a : seq _)) => va; last first.
  + rewrite big1 //= => u _; rewrite /preflow_of_apath /=.
    case: ifP; last case: ifP => //.
    * by move/asegment_meml=> /=; rewrite (negbTE va).
    * by move/asegment_memr=> /=; rewrite (negbTE va).
  rewrite (bigD1 (next a (↓ v))) 1?(bigD1 (prev a (↓ v))) //=.
  + have := asegment_asym (asegment_next va); apply/contra.
    by move=> /eqP <-; apply/asegment_prev.
  rewrite big1 ?addr0 => [u /andP [hu1 hu2]|].
  + rewrite /preflow_of_apath /=; do! case: ifPn=> //.
    * by case/and3P=> /= _ _; rewrite eq_sym (negbTE hu1).
    * case/and3P=> /= _ _ => /eqP /(congr1 (prev a)).
      by rewrite prev_next ?uniq_apath // (rwP eqP) (negbTE hu2).
    rewrite /preflow_of_apath /= asegment_next //=.
    by rewrite -if_neg asegment_asym ?asegment_prev // subrr.
Qed.

(* -------------------------------------------------------------------- *)
Definition flow_of_apath (a : apath) :=
  Flow (preflow_of_apath_is_flow a).

Lemma flow_of_apath_neq0 a : 0 < `|flow_of_apath a|.
Proof.
rewrite fmassE (bigD1 (next a ⊤)) //= big1 ?addr0.
+ move=> v Nva; rewrite /preflow_of_apath /=.
  case: ifPn => [/(asegment_injr (asegment_src a))|].
  * by move/eqP; rewrite eq_sym (negbTE Nva).
  by move=> _; rewrite -if_neg /asegment /= andbF.
by rewrite /preflow_of_apath /= asegment_src aweight_gt0.
Qed.
End AugmentingPath.

(* -------------------------------------------------------------------- *)
Notation cut T := (pred T) (only parsing).

Section CutDef.
Context {T : finType} (C : cut T).

Definition cleft : pred (vertex T) :=
  [pred x | if x is ↓x then C x else x == ⊤].

Definition cright : pred (vertex T) :=
  [pred x | if x is ↓x then ~~ C x else x == ⊥].

(* -------------------------------------------------------------------- *)
Definition cweight (g : {network T}) :=
  \sum_(u in cleft ) \sum_(v in cright) g (u, v).

Definition cflow (f : edge T -> R) :=
  \sum_(u in cleft) \sum_(v in cright) f (u, v).

(* -------------------------------------------------------------------- *)
Lemma cleft_grdE u : ↓u \in cleft = C u.
Proof. by []. Qed.

Lemma cright_grdE u : ↓u \in cright = ~~ C u.
Proof. by []. Qed.

Definition cut_grdE := (cleft_grdE, cright_grdE).

(* -------------------------------------------------------------------- *)
Lemma cut_span u : (u \in cleft) || (u \in cright).
Proof. by elim/vertexW: u => //= u; rewrite !cut_grdE orbN. Qed.

(* -------------------------------------------------------------------- *)
Lemma cut_disjoint : [disjoint cleft & cright].
Proof.
rewrite disjoint_subset; apply/subsetP; elim/vertexW => //=.
by move=> u; rewrite !(cut_grdE) inE negbK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cright_cleft : cright =1 predC cleft.
Proof. by elim/vertexW. Qed.

(* -------------------------------------------------------------------- *)
Lemma cflowE f : cflow f =
  \sum_(u | u \in cleft) \sum_(v | v \notin cleft) f (u, v).
Proof.
apply/eq_bigr=> /= u _; apply/eq_bigl=> v /=.
by rewrite -!topredE /= cright_cleft.
Qed.

(* -------------------------------------------------------------------- *)
Lemma cweightE (g : {network T}) : cweight g =
  \sum_(u | u \in cleft) \sum_(v | v \notin cleft) g (u, v).
Proof.
apply/eq_bigr=> /= u _; apply/eq_bigl=> v /=.
by rewrite -!topredE /= cright_cleft.
Qed.
End CutDef.

(* -------------------------------------------------------------------- *)
Section FlowMeasure.
Context {T : finType} {g : {network T}} (C : cut T) (f : flow g).

Lemma flow_cflow : `|f| = cflow C f.
Proof.
have eq0: \sum_(u in cleft C | u != ⊤) \sum_v f (u, v) = 0.
  by rewrite big1 //=; elim/vertexW => // u _; rewrite flow_kirchnoff.
rewrite fmassE cflowE -[LHS]addr0 -{}[X in _+X]eq0.
rewrite -bigD1 //= (eq_bigr _ (fun _ _ => bigID (cleft C) _ _)) /=.
rewrite big_split /= [X in X+_](_ : _ = 0) ?add0r //.
apply/(@mulfI _ 2%:R); first by rewrite pnatr_eq0.
rewrite mulr0 mulr_natl mulr2n {1}exchange_big /= -big_split /=.
rewrite big1 // => u _; rewrite -big_split big1 //= => v _.
by rewrite [X in _+X]flow_antisym subrr.
Qed.
End FlowMeasure.

(* -------------------------------------------------------------------- *)
Section FMass.
Context {T : finType} (g : {network T}) (f : flow g).

Lemma fmass_snkE : `|f| = \sum_v f (v, ⊥).
Proof.
rewrite (flow_cflow predT) /cflow exchange_big /=.
rewrite (bigD1 ⊥) //= addrC big1 ?add0r; first by case=> -[[]|].
apply/esym; rewrite (bigD1 ⊥) //= flow_self add0r.
by apply/eq_bigl; case=> -[[|]|].
Qed.
End FMass.

(* -------------------------------------------------------------------- *)
Section WeakMaxFlowMinCut.
Context {T : finType} (g : {network T}) (C : cut T) (f : flow g).

Lemma weak_maxflow_mincut : `|f| <= cweight C g.
Proof.
rewrite (flow_cflow C) cflowE cweightE !pair_big /=.
by apply/ler_sum=> e _; apply/flow_lecp.
Qed.
End WeakMaxFlowMinCut.

(* -------------------------------------------------------------------- *)
Section MaxFlowMinCut.
Context {T : finType} (g : {network T}).

Local Notation nv := #|{: vertex T}|.
Local Notation ne := #|{: edge T}|.

(* -------------------------------------------------------------------- *)
Let eswap (e : edge T) : edge T := (e.2, e.1).

Let evar (e : edge T) : 'cV[R]_ne :=
  delta_mx (enum_rank e) 0.

Definition flow_eqs : (ne + ne + #|T|).-tuple (lpeq ne) :=
    [tuple of
      (  [seq (evar e <= g e)%T | e <- enum {: edge T}]
      ++ [seq (evar e + evar (eswap e) == 0)%T | e <- enum {: edge T}])
      ++ [seq (\sum_v evar (↓u, v) == 0)%T | u <- enum T]].

Definition flow_of_vector (x : 'rV[R]_ne) :=
  fun e : edge T => x 0 (enum_rank e).

(* -------------------------------------------------------------------- *)
Definition flow_cost (x : 'rV[R]_ne): R^o :=
  fmass (flow_of_vector x).

Lemma flow_cost_is_linear : scalar flow_cost.
Proof.
move=> c u v; rewrite /flow_cost /fmass mulr_sumr -big_split /=.
by apply/eq_bigr=> x _; rewrite /flow_of_vector !mxE.
Qed.

(* -------------------------------------------------------------------- *)

HB.instance Definition _ :=
  GRing.isLinear.Build _ _ _ _ flow_cost flow_cost_is_linear.

Definition flow_pb :=
  {| lppb_eqs  := flow_eqs;
     lppb_bnd  := \sum_e g e;
     lppb_cost := flow_cost |}.

(* -------------------------------------------------------------------- *)
Lemma flow_pbP (x : 'rV[R]_ne) (f : edge T -> R) :
     (forall e, f e = x 0 (enum_rank e))
  -> (x \in flow_pb) = (f \is a g.-flow).
Proof.
move=> eq_fx; have xE e: (x *m evar e) 0 0 = f e.
+ rewrite mulmx_sum_rowE (bigD1 (enum_rank e)) //= !mxE !eqxx mulr1.
  rewrite big1 ?addr0 ?eq_fx // => i ne.
  by rewrite !mxE (negbTE ne) mulr0.
apply/idP/idP => [/lppbP[h _]|].
+ apply/isflowP => [e|u v|u].
  * move/(_ (lshift _ (lshift _ (enum_rank e)))): h => /=.
    rewrite /flow_eqs !tnth_catlr tnth_map mem_lpeqE /=.
    by rewrite (tnth_nth e) /= nth_enum_rank xE.
  * move/(_ (lshift _ (rshift _ (enum_rank (u, v))))): h.
    rewrite /flow_eqs !tnth_catlr tnth_map mem_lpeqE /=.
    rewrite !(tnth_nth (u, v)) !nth_enum_rank /eswap /=.
    by rewrite mulmxDr !(xE, mxE) addr_eq0 => /eqP.
  * move/(_ (rshift _ (enum_rank u))): h; rewrite /flow_eqs.
    rewrite !tnth_catlr tnth_map mem_lpeqE /= mulmx_sumr summxE.
    move/eqP=> h; rewrite -{}[RHS]h; apply/eq_bigr=> v _.
    by rewrite xE; rewrite (tnth_nth u) nth_enum_rank.
+ move=> hf; apply/lppbP; split; last first.
  * move=> e; rewrite -[e]enum_valK -eq_fx /flow_pb /=.
    case: (enum_val e) => {e} u v; rewrite ler_norml.
    rewrite {1}(bigD1 (v, u)) //= (bigD1 (P := predT) (u, v)) //=.
    rewrite lerNl -(isflow_antisym hf) !ler_wpDr //; solve
      [ by rewrite sumr_ge0 // => i _; rewrite network_ge0
      | by apply/(isflow_lecp hf)].
  (do! elim/splitW) => i; rewrite !tnth_catlr tnth_map mem_lpeqE /=.
  * by rewrite xE; apply/(isflow_lecp hf).
  * rewrite mulmxDr !(xE, mxE); case: (tnth _ _) => u v.
    by rewrite /eswap /= addr_eq0; apply/eqP/(isflow_antisym hf).
  * rewrite mulmx_sumr summxE -(rwP eqP); set u := tnth _ _.
    rewrite -[RHS](isflow_kirchnoff hf u).
    by apply/eq_bigr=> v _; rewrite xE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma flow_pb_of_vector (x : 'rV[R]_ne) :
  (x \in flow_pb) = (flow_of_vector x \is a g.-flow).
Proof. by apply/flow_pbP => e. Qed.

(* -------------------------------------------------------------------- *)
Lemma maxflow_mincut :
  {f : flow g |
        (forall C : cut T, `|f| <= cweight C g)
     /\ (exists C : cut T, `|f|  = cweight C g)}.
Proof.
case: (lppbsolve (pb := flow_pb)).
+ exists 0; rewrite flow_pb_of_vector (eq_isflow _ (isflow_0 g)) //.
  by move=> e; rewrite /flow_of_vector mxE.
move=> x; rewrite flow_pb_of_vector => -[solx maxx].
exists (Flow solx); split => [C|]; first by apply/weak_maxflow_mincut.
pose r := residual (Flow solx).
pose P u := [exists i : 'I_#|T|, [exists s : i.-tuple T,
  uniq (rcons s u) && path
    [rel x y | 0 < r (x, y)] ⊤ [seq ↓ x | x <- rcons s u]]].
exists P; rewrite cweightE (flow_cflow P) cflowE.
apply/eq_bigr=> /= u uP; apply/eq_bigr=> /= v vNP.
have /(_ (u, v)) := isflow_lecp solx; rewrite le_eqVlt.
case/orP=> [/eqP->//|]; elim/vertexW: v vNP => // [|v] vNP h.
+ have: exists _ : apath (Flow solx), true.
  * case: u uP h => -[[_|_]|u uP] h //.
    - have: uniq ([::] : seq T) && spath (Flow solx) [::].    
      + by rewrite /spath /= andbT ffunE /preresidual subr_gt0.
      by move=> ha; exists (APath ha).
    move: uP; rewrite cut_grdE => /existsP[/= i].
    move/existsP=> [/= s] /andP[uqs hp].
    have: uniq (rcons s u) && spath (Flow solx) (rcons s u).
    - rewrite uqs /= /spath rcons_path hp /= ffunE.
      by rewrite map_rcons last_rcons /preresidual subr_gt0.
    by move=> ha; exists (APath ha).
  case=> ap _; pose fa := addflow (flow_of_apath ap).
  have ltf: `|Flow solx| < `|fa|.
  * by rewrite fmassD /= ltrDl flow_of_apath_neq0.
  pose z : 'rV[R]_#|{: edge T}| := \row_i fa (enum_val i).
  have /(maxx z): z \in flow_pb.
  * rewrite flow_pb_of_vector; set fb := (X in X \is a _).
    apply/(@eq_isflow _ _ fa fb); last by apply/isflow_flow.
    by move=> y; rewrite /fb /flow_of_vector mxE enum_rankK.
  suff ->: flow_pb.(lppb_cost) z = `|fa| by rewrite leNgt ltf.
  rewrite {}/z /flow_pb /flow_cost /= !fmassE.
  apply/eq_bigr=> /= v _; rewrite /flow_of_vector.
  by rewrite !mxE !(enum_valK, enum_rankK).
+ suff {vNP} Pv: P v by move: vNP; rewrite inE Pv.
  elim/vertexW: u uP h => // => [_ |u uP] h.
  * have := leq0n #|T|; rewrite leq_eqVlt => /orP[/eqP /esym T0|].
    - have: v \in enum T by rewrite mem_enum.
      by move/eqP: T0; rewrite cardT size_eq0 => /eqP->.
    move=> gt0_T; apply/existsP; exists (Ordinal gt0_T).
    apply/existsP; exists [tuple] => /=; rewrite andbT.
    by rewrite ffunE /preresidual subr_gt0.
  case: (u =P v) uP => [->|]; rewrite cut_grdE //.
  move=> ne_uv /existsP[/= i] /existsP[/= s].
  case/andP=> uqs hp; case/boolP: (v \in s) => vs.
  * pose j := index v s; have lt_ji: (j < i)%N.
    - by rewrite -[X in (_ < X)%N](size_tuple s) index_mem.
    apply/existsP; exists (Ordinal (ltn_trans lt_ji (ltn_ord i))).
    have hs: size (take j s) == j by rewrite size_take index_mem vs.
    apply/existsP; exists (Tuple hs) => /=; apply/andP; split.
    - rewrite rcons_uniq /=; apply/andP; split; last first.
      + move: uqs; rewrite rcons_uniq => /andP[_].
        by rewrite -{1}[_ s](cat_take_drop j) cat_uniq => /and3P[].
      apply/negP=> vjs; move: hs; rewrite {2}/j.
      rewrite -{2}[_ s](cat_take_drop j) index_cat vjs /=.
      by rewrite gtn_eqF // index_mem.
    move: hp; rewrite -cats1 -{1}[_ s](cat_take_drop j) -catA.
    rewrite map_cat cat_path => /andP[hv1 hv2].
    rewrite map_rcons rcons_path {}hv1 andTb /= ffunE.
    move: hv2; rewrite cats1 headI /= => /andP[hv _].
    by move: hv; rewrite -nth0 nth_drop addn0 nth_index // ffunE.
  * have: (size (rcons s u) <= #|T|)%N by rewrite size_rcons size_tuple.
    rewrite leq_eqVlt => /orP[hz|hz]; last first.
    - apply/existsP; exists (Ordinal hz); apply/existsP => /=.
      exists (in_tuple (rcons s u)) => /=; apply/andP; split.
      + rewrite rcons_uniq uqs andbT mem_rcons in_cons.
        by rewrite negb_or vs andbT; apply/eqP=> /esym.
      rewrite map_rcons rcons_path hp /= ffunE.
      by rewrite map_rcons last_rcons /= /preresidual subr_gt0.
    case: (@uniq_min_size _ (rcons s u) (enum T)) => //.
    - by move=> y _; rewrite mem_enum.
    - by rewrite (eqP hz) cardT.
    move=> _ /(_ v); rewrite mem_rcons in_cons (negbTE vs) orbF.
    by rewrite mem_enum => /eqP /= /esym.
Qed.
End MaxFlowMinCut.
End MaxFlow.

(* -------------------------------------------------------------------- *)
Notation "{ 'network' T }" := (@network T).
