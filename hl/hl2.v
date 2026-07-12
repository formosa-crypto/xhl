(* -------------------------------------------------------------------- *)
From mathcomp           Require Import all_boot all_order.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.
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

Section hl.
   Context {X Y : eqType} {mem : memType X}.

Notation "`[ 'forall' x 'in' mu => Q ]" :=
  (@forall_in  mem _ mu%A (fun x => Q)).

Notation "`[ 'forall' x 'in' mu | m => Q ]" :=
  (@forall_in _ mem _ mu%A (fun x m => Q)).

Notation assn := (@assn _ mem).
Notation assn2 := (@assn2 _ mem).

Notation phi := (@phi X Y mem).
Notation psi := (@psi _ Y mem).

Section Logic.

Context (ps: psi).

(* -------------------------------------------------------------------- *)

Inductive derivable : phi -> assn -> cmd -> assn -> Prop :=
  | H_Skip : forall P cl,
      derivable cl P skip P
  | H_Abort : forall P Q cl,
      derivable cl P abort Q
  | H_Asgn : forall {T : IhbType.type} x (e:expr_ X mem T) (Q : assn) cl,
      derivable cl [pred m | Q m.[x <- `[{e}]%A m]] (x <<- e) Q
  | H_Random : forall {T : IhbType.type} x (d:expr_ X mem (Distr T)) (Q : assn) cl,
      derivable cl `[forall v in `[{d}] | m => Q m.[x <- v]]%A (x <$- d) Q
  | H_Seq : forall P c Q d R cl,
      derivable cl Q d R -> derivable cl P c Q -> derivable cl P (c;;d) R
  | H_If : forall (Pr Po : assn) (e:expr_ X mem bool) (c1 c2:cmd) cl,
      derivable cl (Pr /\ `[{e}])%A   c1 Po ->
      derivable cl (Pr /\ `[{~~e}])%A c2 Po ->
      derivable cl Pr (If e then c1 else c2)%S Po
  | H_While : forall (I : assn) (e:expr_ X mem bool) (c:cmd) cl,
      derivable cl (I /\ `[{e}])%A c I ->
      derivable cl I (While e Do c) (I /\ `[{~~e}])%A
  | H_Consequence : forall (P2 Q2 P1 Q1 : assn)(c : cmd) cl,
      (forall m, P1 m -> P2 m) ->
      (forall m, Q2 m -> Q1 m) ->
      derivable cl P2 c Q2 -> derivable cl P1 c Q1
  | H_khl : forall P Q c cl,
     derivable2 cl P c (fun _ => Q) -> derivable cl P c Q
  with derivable2 : phi -> assn -> cmd -> assn2 -> Prop :=
   | H_hl: forall P Q c cl,
       (forall s0, derivable cl (xpredI P (fun s => s == s0)) c (Q s0)) ->
       derivable2 cl P c Q
   | H_call : forall cl f,
       derivable2 cl (get_pre (cl f)) (call f) (get_post (cl f))
   | H_rec : forall P Q c cl cl',
       (forall p', derivable2 cl (get_pre (cl p')) (ps p') (get_post (cl p'))) ->
       derivable2 cl P c Q ->
       derivable2 cl' P c Q
   | H_adapt : forall (P1 P2 : assn) (Q1 Q2 : assn2) c cl,
       (forall m, P1 m -> P2 m) ->
       (forall m0, P1 m0 -> forall m, Q2 m0 m -> Q1 m0 m) ->
       derivable2 cl P2 c Q2 -> derivable2 cl P1 c Q1.

Scheme derivable_min := Minimality for derivable Sort Prop
  with derivable2_min := Minimality for derivable2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

End Logic.

Section Sound.
Context {ps:psi}.

Section Rules.
Definition ahl (l : Y * mem -> Distr mem) (P : assn) (c : cmd) (Q : assn) :=
  forall m, P m -> range Q (ssem_aux l c m).
Definition akhl (l : Y * mem -> Distr mem) (P : assn) (c : cmd) (Q : assn2) :=
  forall m, P m -> range (Q m) (ssem_aux l c m).

Arguments ahl l P%_A c%_S Q%_A.
Arguments akhl l P%_A c%_S Q%_A.

Lemma ahl_skip l (P : assn) : ahl l P skip P.
Proof. by move=> m hm /=; apply: range_dunit. Qed.

Lemma ahl_abort l (P Q : assn) : ahl l P abort Q.
Proof. by move=> m hm /=; apply: range_dnull. Qed.

Lemma ahl_assign l {T : IhbType.type} x (e : expr_ X mem T) (Q : assn) :
  ahl l [pred m | Q m.[x <- `[{e}]%A m]] (x <<- e) Q.
Proof. by move=> m hm /=; apply: range_dunit. Qed.

Lemma ahl_random l {T : IhbType.type} x (d : expr_ X mem (Distr T)) (Q : assn) :
  ahl l `[forall v in `[{d}] | m => Q m.[x <- v]] (x <$- d) Q.
Proof.
move=> m /asboolP /= h /=.
apply (@range_dlet _ _ [pred v | Q m.[x <- v]]) => v /=.
  by apply h. by apply range_dunit.
Qed.

Lemma ahl_seq l (R Pr Po : assn) (c1 c2 : cmd) :
  ahl l Pr c1 R -> ahl l R c2 Po -> ahl l Pr (c1;;c2) Po.
Proof. by move=> H1 H2 m /H1 Hm /=; apply/(range_dlet Hm H2). Qed.

Lemma ahl_if l (Pr Po : assn) (e : expr_ X mem bool) (c1 c2 : cmd) :
  ahl l (Pr /\ `[{e}]) c1 Po -> ahl l (Pr /\ `[{~~e}]) c2 Po ->
  ahl l Pr (If e then c1 else c2)%S Po.
Proof.
by move=> H1 H2 m Hm /=; case: ifPn => He; [apply H1 | apply H2] => /=; rewrite Hm.
Qed.

Lemma ahl_while l (I : assn) (e : expr_ X mem bool) (c : cmd) :
  ahl l (I /\ `[{e}]) c I -> ahl l I (While e Do c) (I /\ `[{~~e}]).
Proof.
move=> Hc m Hm /=; apply/range_dlim => k.
elim: k m Hm => [|k IHk] m Hm /=; first by apply: range_dnull.
case: ifPn => He.
+ apply: (range_dlet (PA := I)).
  - by apply: Hc => /=; rewrite Hm.
  - by move=> m' Im'; apply: IHk.
+ by apply: range_dunit => /=; rewrite Hm.
Qed.

Lemma ahl_conseq l (P2 Q2 P1 Q1 : assn) (c : cmd) :
  (forall m, P1 m -> P2 m) -> (forall m, Q2 m -> Q1 m) ->
  ahl l P2 c Q2 -> ahl l P1 c Q1.
Proof. by move=> HP HQ H2 m /HP /H2 Hr; apply: (range_weaken HQ Hr). Qed.

Lemma akhl_hl l P c Q :
  akhl l P c Q <-> (forall s0, ahl l (xpredI P (fun s => s == s0)) c (Q s0)).
Proof.
split.
+ by move=> h s0 ? /andP [] ? /eqP ?; subst s0; apply h.
move => h s hP; apply: (h s); by apply/andP.
Qed.

Lemma ahl_khl l P c Q : akhl l P c (fun _ => Q) <-> ahl l P c Q.
Proof. by split; move => h s hP; apply h. Qed.

Definition valid_cl_n n cl :=
  forall  f, akhl (ubnf ps n) (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma ind_calls cl :
  (forall (f : Y) (n : nat), valid_cl_n n cl ->
        akhl (ubnf ps n) (get_pre (cl f)) (ps f) (get_post (cl f))) ->
  (forall (f : Y) (n : nat),  akhl (ubnf ps n) (get_pre (cl f)) (call f) (get_post (cl f))).
Proof.
move => IH_body f n.
elim: n f => [|k IHk] f  m pf; first by apply: range_dnull.
apply: (IH_body f k _ m pf).
move=> g. exact: IHk.
Qed.

Lemma ahl_calls cl c P Q:
  (forall (f : Y) (n : nat), valid_cl_n n cl ->
        akhl (ubnf ps n) (get_pre (cl f)) (ps f) (get_post (cl f))) ->
  (forall (n : nat), valid_cl_n n cl ->  akhl (ubnf ps n) P c Q) ->
  forall n, akhl (ubnf ps n) P c Q.
Proof.
  move => IH_f IH_body n.
  apply IH_body => f.
  by apply ind_calls.
Qed.

End Rules.

Lemma soundness_n :
  (forall cl P c Q, derivable ps cl P c Q ->
     forall n, valid_cl_n n cl -> ahl (ubnf ps n) P c Q) /\
  (forall cl P c Q, derivable2 ps cl P c Q ->
     forall n, valid_cl_n n cl -> akhl (ubnf ps n) P c Q).
Proof.
apply: derivable_mut.
- (* H_Skip *) by move=> P cl n _; exact: ahl_skip.
- (* H_Abort *) by move=> P Q cl n _; exact: ahl_abort.
- (* H_Asgn *) by move=> T x e Q cl n _; exact: ahl_assign.
- (* H_Random *) by move=> T x d Q cl n _; exact: ahl_random.
- (* H_Seq *)
  by move=> P c Q d R cl _ IHd _ IHc n Hv; apply: (ahl_seq (IHc n Hv) (IHd n Hv)).
- (* H_If *)
  by move=> Pr Po e c1 c2 cl _ IH1 _ IH2 n Hv;
     apply: ahl_if; [exact: IH1 | exact: IH2].
- (* H_While *) by move=> I e c cl _ IH n Hv; apply: ahl_while; exact: IH.
- (* H_Consequence *)
  by move=> P2 Q2 P1 Q1 c cl HP HQ _ IH n Hv; apply: (ahl_conseq HP HQ (IH n Hv)).
- (* H_khl *) by move=> P Q c cl _ IH n Hv; apply/ahl_khl; exact: IH.
- (* H_hl *) by move=> P Q c cl _ IH n Hv; apply/akhl_hl=> s0; exact: (IH s0 n Hv).
- (* H_call *) by move=> cl f n Hv; exact: Hv.
- (* H_rec *)
  move=> P Q c cl cl' _ IH_body _ IH_c n Hv.
  by apply: (ahl_calls (cl:=cl)).
- (* H_adapt *)
  move=> P1 P2 Q1 Q2 c cl Hpre Hpost _ IH n Hv m P1m.
  apply: (range_weaken _ (IH n Hv m (Hpre m P1m))).
  by move=> s; exact: (Hpost m P1m s).
Qed.

Definition valid_cl cl :=
  forall f, khl_ ps (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma valid_cl_to_n cl : valid_cl cl -> forall n, valid_cl_n n cl.
Proof.
move=> Hv n f m pf.
have Hlim := Hv f m pf; rewrite ssem_callE in Hlim.
apply: (range_le (nu := \dlim_(k) ubnf ps k (f, m))) => //.
by apply: dlim_ub => k1 k2 le; exact: (homo_ubnf le (f, m)).
Qed.

Theorem ahl_to_hl cl P c Q :
  (forall n, valid_cl_n n cl -> ahl (ubnf ps n) P c Q) ->
  valid_cl cl -> hl_ ps P c Q.
Proof.
move => H Hv m Pm; rewrite test8; apply: range_dlim => n.
 have Hvn : valid_cl_n n cl := @valid_cl_to_n cl Hv n.
by apply: H.
Qed.

Theorem hoare_sound cl P c Q :
  valid_cl cl -> derivable ps cl P c Q -> hl_ ps P c Q.
Proof.
  move => Hv Hd.
  apply: (ahl_to_hl (cl := cl)) => // n Hvn.
  exact: (proj1 soundness_n  _ _ _ _ Hd n Hvn).
Qed.

Corollary hoare_sound0 P c Q : derivable ps empty_phi P c Q -> hl_ ps P c Q.
Proof. by apply: hoare_sound. Qed.

Theorem akhl_to_khl cl P c Q :
  (forall n, valid_cl_n n cl -> akhl (ubnf ps n) P c Q) ->
  valid_cl cl -> khl_ ps P c Q.
Proof.
move => H Hv m Pm; rewrite test8; apply: range_dlim => n.
 have Hvn : valid_cl_n n cl := @valid_cl_to_n cl Hv n.
by apply: H.
Qed.

Theorem khoare_sound cl P c Q :
  valid_cl cl -> derivable2 ps cl P c Q -> khl_ ps P c Q.
Proof.
  move => Hv Hd.
  apply: (akhl_to_khl (cl := cl)) => // n Hvn.
  exact: (proj2 soundness_n  _ _ _ _ Hd n Hvn).
Qed.

Corollary khoare_sound0 P c Q : derivable2 ps empty_phi P c Q -> khl_ ps P c Q.
Proof. by apply: khoare_sound. Qed.

End Sound.

Section Complete.
Context (ps: psi).

(* Most-general procedure contract *)
Definition cl_mgt : phi :=
  fun f => (xpredT, (fun s0 s => s \in dinsupp (ssem_ ps (ps f) s0))).

Lemma in_dinsupp_dunit (T : choiceType) (t : T) :
  t \in dinsupp (dunit t : {distr T / R}).
Proof. by rewrite in_dinsupp dunit1E eqxx oner_neq0. Qed.

Lemma rel_complete_d (c : cmd) (P Q : assn) :
  hl_ ps P c Q -> derivable ps cl_mgt P c Q.
Proof.
elim: c P Q => [ | | T x e | T x d | e c1 ih1 c2 ih2 | e c0 ih0 | c1 ih1 c2 ih2 | f ] P Q Hhl.
- (* abort *) exact: H_Abort.
- (* skip *)
  apply: (H_Consequence (P2 := P) (Q2 := P)) => //.
  + move=> m Pm; have H := Hhl m Pm; rewrite ssem_skipE in H.
    by apply: (H m); exact: in_dinsupp_dunit.
  + exact: H_Skip.
- (* assign *)
  apply: (H_Consequence (P2 := [pred m | Q m.[x <- `[{e}]%A m]]) (Q2 := Q)).
  + move=> m Pm /=; have H := Hhl m Pm; rewrite ssem_assnE in H.
    by apply: (H (m.[x <- `[{e}]%A m])); exact: in_dinsupp_dunit.
  + by [].
  + exact: H_Asgn.
- (* random *)
  apply: (H_Consequence
            (P2 := `[forall v in `[{d}] | m => Q m.[x <- v]]%A) (Q2 := Q)).
  + move=> m Pm; apply/asboolP => v vd; have H := Hhl m Pm; rewrite ssem_rndE in H.
    apply: (H (m.[x <- v])); apply: dlet_dinsupp; first exact: vd.
    exact: in_dinsupp_dunit.
  + by [].
  + exact: H_Random.
- (* if *)
  apply: H_If.
  + apply: ih1 => m /andP[Pm em]; have H := Hhl m Pm.
    by rewrite ssem_ifE em in H.
  + apply: ih2 => m /andP[Pm em]; have H := Hhl m Pm.
    have em' : esem e m = false by apply/negbTE; exact: em.
    by rewrite ssem_ifE em' in H.
- (* while *)
  pose I : assn := [pred s | `[< range Q (ssem_ ps (While e Do c0) s) >]].
  apply: (H_Consequence (P2 := I) (Q2 := (I /\ `[{~~e}])%A)).
  + by move=> m Pm; apply/asboolP; exact: (Hhl m Pm).
  + move=> s /andP[/asboolP HIs es].
    have es' : ~~ esem e s by exact: es.
    by apply: (HIs s); rewrite ssem_while0 //; exact: in_dinsupp_dunit.
  + apply: H_While; apply: ih0 => s /andP[/asboolP HIs es] s' s'in.
    apply/asboolP => t tin.
    have es' : esem e s by exact: es.
    apply: (HIs t); rewrite ssem_whileS // ssem_seqE.
    by apply: dlet_dinsupp; [exact: s'in | exact: tin].
- (* seq *)
  pose R : assn := [pred s' | `[< exists2 m, P m & s' \in dinsupp (ssem_ ps c1 m) >]].
  apply: (H_Seq (Q := R)).
  + apply: ih2 => s' /asboolP[m Pm s'in] y yin.
    have H := Hhl m Pm; rewrite ssem_seqE in H.
    by apply: (H y); apply: dlet_dinsupp; [exact: s'in | exact: yin].
  + apply: ih1 => m Pm s' s'in; apply/asboolP; by exists m.
- (* call *)
  apply: H_khl.
  apply: (H_adapt (P2 := get_pre (cl_mgt f)) (Q2 := get_post (cl_mgt f))) => //.
  + move=> m0 Pm0 m hm; have H := Hhl m0 Pm0; rewrite ssem_call_eq in H.
    exact: (H m hm).
  + by apply: H_call; right.
Qed.

Lemma rel_complete (c : cmd) (P : assn) (Q : assn2) :
  khl_ ps P c Q -> derivable2 ps cl_mgt P c Q.
Proof.
move=> /khl_hl h; apply: H_hl => s0; exact: (rel_complete_d (h s0)).
Qed.

Theorem khoare_complete: forall P c Q cl,
  khl_ ps P c Q -> derivable2 ps cl P c Q.
Proof.
move=> P c Q cl Hvalid.
apply: (H_rec (cl:=cl_mgt)).
- by move=> p'; apply: rel_complete  => m _ s hs.
- exact: rel_complete Hvalid.
Qed.

Theorem hoare_complete: forall P c Q cl,
  hl_ ps P c Q -> derivable ps cl P c Q.
Proof.
move=> P c Q cl Hvalid.
apply: H_khl.
apply khoare_complete.
by apply hl_khl.
Qed.

End Complete.

End hl.
