(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
From mathcomp.analysis  Require Import counting_distr.
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

Section HL.
Context {X Y : eqType} {mem : memType X}.

Notation "`[ 'forall' x 'in' mu => Q ]" :=
  (@forall_in  mem _ mu%A (fun x => Q)).

Notation "`[ 'forall' x 'in' mu | m => Q ]" :=
  (@forall_in _ mem _ mu%A (fun x m => Q)).

Notation assn := (@assn _ mem).
Notation assn2 := (@assn2 _ mem).

Notation phi := (@phi X Y mem).

Section Logic.

Inductive derivable : psi -> phi -> assn -> cmd -> assn -> Prop :=
  | H_Skip : forall P cl ps,
      derivable ps cl P skip P
  | H_Abort : forall P Q cl ps,
      derivable ps cl P abort Q
  | H_Asgn : forall {T : IhbType.type} x (e:expr_ X mem T) (Q : assn) cl ps,
      derivable ps cl [pred m | Q m.[x <- `[{e}]%A m]] (x <<- e) Q
  | H_Random : forall {T : IhbType.type} x (d:expr_ X mem (Distr T)) (Q : assn) cl ps,
      derivable ps cl `[forall v in `[{d}] | m => Q m.[x <- v]]%A (x <$- d) Q
  | H_Seq : forall P c Q d R cl ps,
      derivable ps cl Q d R -> derivable ps cl P c Q -> derivable ps cl P (c;;d) R
  | H_If : forall (Pr Po : assn) (e:expr_ X mem bool) (c1 c2:cmd) cl ps,
      derivable ps cl (Pr /\ `[{e}])%A   c1 Po ->
      derivable ps cl (Pr /\ `[{~~e}])%A c2 Po ->
      derivable ps cl Pr (If e then c1 else c2)%S Po
  | H_While : forall (I : assn) (e:expr_ X mem bool) (c:cmd) cl ps,
      derivable ps cl (I /\ `[{e}])%A c I ->
      derivable ps cl I (While e Do c) (I /\ `[{~~e}])%A
  | H_Consequence : forall (P2 Q2 P1 Q1 : assn)(c : cmd) cl ps,
      (forall m, P1 m -> P2 m) ->
      (forall m, Q2 m -> Q1 m) ->
      derivable ps cl P2 c Q2 -> derivable ps cl P1 c Q1
  | H_khl : forall P Q c cl ps,
     derivable2 ps cl P c (fun _ => Q) -> derivable ps cl P c Q
  with derivable2 : psi -> phi -> assn -> cmd -> assn2 -> Prop :=
   | H_hl: forall P Q c cl ps,
       (forall s0, derivable ps cl (xpredI P (fun s => s == s0)) c (Q s0)) ->
       derivable2 ps cl P c Q
   | H_call : forall cl f ps,
       derivable2 ps cl (get_pre (cl f)) (call f) (get_post (cl f))
   | H_rec : forall P Q c cl cl' ps',
       (forall p' ps , derivable2 ps cl (get_pre (cl p')) (ps' p') (get_post (cl p'))) ->
       (forall ps, derivable2 ps cl P c Q) ->
       derivable2 ps' cl' P c Q
   | H_adapt : forall (P1 P2 : assn) (Q1 Q2 : assn2) c cl ps,
       (forall m, P1 m -> P2 m) ->
       (forall m0, P1 m0 -> forall m, Q2 m0 m -> Q1 m0 m) ->
       derivable2 ps cl P2 c Q2 -> derivable2 ps cl P1 c Q1.

Scheme derivable_min := Minimality for derivable Sort Prop
  with derivable2_min := Minimality for derivable2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

End Logic.

Section Sound.

Section Rules.
Context (ps: @psi _ Y mem).

Notation hl   := (hl_ ps).
Notation khl   := (khl_ ps).

(* -------------------------------------------------------------------- *)
(* Core rules                                                           *)
(* -------------------------------------------------------------------- *)
Lemma hl_eq (P Q: assn) (c c' : cmd) :
     (forall m, P m -> ssem_ ps c m = ssem_ ps c' m)
  -> hl P c Q
  -> hl P c' Q.
Proof. by move=> Hc Hw m Pm;rewrite -Hc //;apply Hw. Qed.

(* -------------------------------------------------------------------- *)

Instance hl_m : Proper (eq ==> @eqcmd _ _ mem ps ==> eq ==> iff) hl.
Proof. by move=> ??-> ??? ??->;split;apply hl_eq. Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_conseq (P2 Q2 P1 Q1 : assn)(c : cmd):
 (forall m, P1 m -> P2 m) ->
 (forall m, Q2 m -> Q1 m) ->
 hl P2 c Q2 -> hl P1 c Q1.
Proof. by move=> HP HQ H2 m /HP /H2 Hr m' /Hr /HQ. Qed.

Lemma hl_F (c : cmd) P: hl pred0 c P.
Proof. by []. Qed.

Lemma hl_T (c : cmd) P: hl P c predT.
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_skip (P : assn) : hl P skip P.
Proof. by move=> ??; rewrite ssemE;apply range_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_abort (P Q : assn) : hl P abort Q.
Proof. by move=> ??;rewrite ssemE;apply range_dnull. Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_assign {T : IhbType.type} x (e:expr_ X mem T) (Q : assn):
   hl [pred m | Q m.[x <- `[{e}]%A m]] (x <<- e) Q.
Proof. by move=> m /=;rewrite !semE;apply range_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_random {T : IhbType.type} x (d:expr_ X mem (Distr T)) (Q : assn):
   hl `[forall v in `[{d}] | m => Q m.[x <- v]] (x <$- d) Q.
Proof.
move=> m /asboolP /= h; rewrite !semE.
apply (@range_dlet _ _ [pred v | Q m.[x<- v]]) => v /=.
  by apply h. by apply range_dunit.
Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_seq (R Pr Po : assn) (c1 c2:cmd):
  hl Pr c1 R -> hl R c2 Po -> hl Pr (c1;;c2) Po.
Proof.
by move=> H1 H2 m /H1 Hm; rewrite ssemE; apply/(range_dlet Hm H2).
Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_if (Pr Po : assn) (e:expr_ X mem bool) (c1 c2:cmd):
  hl (Pr /\ `[{e}])%A   c1 Po ->
  hl (Pr /\ `[{~~e}])%A c2 Po ->
  hl Pr (If e then c1 else c2)%S Po.
Proof.
by move=> H1 H2 m Hm; rewrite ssemE; case: ifPn => He;
  [apply H1 | apply H2] => /=; rewrite Hm.
Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_while (I : assn) (e:expr_ X mem bool) (c:cmd):
  hl (I /\ `[{e}])%A c I ->
  hl I (While e Do c) (I /\ `[{~~e}])%A.
Proof.
move=> Hc m Hm; rewrite ssemE; apply/range_dlim=> n.
elim: n m Hm => [|n Hn] m Hm /=.
+ by rewrite ssemE; apply range_dnull.
apply (@hl_if I)=> //; last by apply hl_skip.
by apply (hl_seq Hc)=> ??; apply Hn.
Qed.

Lemma range_while e (c:cmd):
  forall m,  range (`[{~~e}]) (ssem_ ps (While e Do c) m).
Proof.
  move => m.
  by apply (@hl_while xpredT e c).
Qed.

Lemma pr_while_e e (c:cmd):
  forall m, \P_[ssem_ ps (While e Do c) m] (`[{e}]) = 0%R.
Proof.
  move => m.
  have := (@range_while e c m).
  move => /pr_range <-.
  apply eq_in_pr.
  move => ? ? //=.
  rewrite !unfold_in => //=.
  by rewrite Bool.negb_involutive.
Qed.

(* -------------------------------------------------------------------- *)
Lemma hl_ll (P Q : assn) (c:cmd) m:
  hl P c Q -> P m -> \P_[ssem_ ps c m] predT = 1 -> \P_[ssem_ ps c m] Q = 1.
Proof.
 by move=> Hhl /Hhl HP <-; rewrite !pr_exp;apply/eq_exp => x /HP ->.
Qed.

(* -------------------------------------------------------------------- *)

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx (cl : phi) (ps: psi) (P: assn) (Q: assn2) (c: cmd) :=
  (forall p, khl_ ps (get_pre (cl p)) (call p) (get_post (cl p))) ->
  khl_ ps P c Q.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx (cl : phi) (ps_init :psi):=
  forall p ps, hoare_triple_ctx cl ps (get_pre (cl p)) (get_post (cl p)) (ps_init p).

Lemma recursive_proc ps' cl' :
  hoare_triple_proc_ctx cl' ps' ->
  (forall p, khl_ ps' (get_pre (cl' p)) (call p) (get_post (cl' p))).
Proof.
  move => h p s hP.
  rewrite /range.
  rewrite /dinsupp.
  rewrite -test1.
  apply/range_dlim=> n.
  revert hP; revert p; revert s.
  elim : n => [| n Hn].
  + move => ???. rewrite ssem_false_ps.
    by  apply range_dnull.
  move => s p hP.
  rewrite (inline2_split n 1).
  apply: h => // p0 s0 hP0.
  by apply: Hn.
Qed.

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple :
  forall P Q c cl,
    hoare_triple_proc_ctx cl ps  ->
    hoare_triple_ctx cl ps P Q c ->
    khl P c Q.
Proof.
  move => ???? H H0.
  apply H0.
  by apply: recursive_proc.
Qed.

End Rules.

Definition valid_cl (cl:phi) (ps:psi) :=
  forall f, khl_ ps (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma soundness :
  (forall (ps:psi) (cl:phi) (P: assn) (c:cmd) Q, derivable ps cl P c Q ->
      valid_cl cl ps -> hl_ ps P c Q) /\
  (forall ps cl P c Q, derivable2 ps cl P c Q ->
     valid_cl cl ps -> khl_ ps P c Q).
Proof.
apply: derivable_mut.
- (* H_Skip *)  by move=> *; exact: hl_skip.
- (* H_Abort *) by move=> *; exact: hl_abort.
- (* H_Asgn *) by move=> *; exact: hl_assign.
- (* H_Random *) by move=> *; exact: hl_random.
- (* H_Seq *)
   by move=> P c Q d R cl ? ? IHd ? IHc Hv; apply: (hl_seq (IHc Hv) (IHd Hv)).
- (* H_If *)
  by move=> Pr Po e c1 c2 cl ? ? IH1 ? IH2 Hv;
     apply: hl_if; [exact: IH1 | exact: IH2].
- (* H_While *)by  move=> I e c cl ? ? IH Hv; apply: hl_while; exact: IH.
- (* H_Consequence *)
  by  move=> P2 Q2 P1 Q1 c cl ? HP HQ ? IH Hv; apply: (hl_conseq HP HQ (IH Hv)).
- (* H_khl *) by move=> P Q c cl ? ? IH Hv; apply/hl_khl; exact: IH.
- (* H_hl *) by move=> P Q c cl ? ? IH Hv; apply/khl_hl=> s0; exact: (IH s0 Hv).
- (* H_call *) by move=> cl f ? Hv; exact: Hv.
- (* H_rec *)
-  move=> P Q c cl cl' ps' IH_body ? ? HI Hv.
   apply: (recursion_hoare_triple (cl:=cl)) => //.
   rewrite /hoare_triple_ctx.
   by move => h; apply: HI.
- (* H_adapt *)
  move=> P1 P2 Q1 Q2 c cl ? Hpre Hpost ?  IH Hv m P1m.
  have := (IH Hv m (Hpre m P1m)).
  apply: range_weaken => m'.
  exact: (Hpost m P1m m').
Qed.

Corollary hoare_sound0 P c Q ps : derivable ps empty_phi P c Q -> hl_ ps P c Q.
Proof.
  move => Hd; exact: (proj1 soundness _ empty_phi).
Qed.

Corollary khoare_sound0 P c Q ps : derivable2 ps empty_phi P c Q -> khl_ ps P c Q.
Proof.   move => Hd;  exact: (proj2 soundness _ empty_phi).
Qed.

End Sound.

Section Complete.

(* Most-general procedure contract *)
Definition cl_mgt ps : phi :=
  fun f => (xpredT, (fun s0 s => s \in dinsupp (ssem_ ps (ps f) s0))).

Lemma in_dinsupp_dunit (T : choiceType) (t : T) :
  t \in dinsupp (dunit t : {distr T / R}).
Proof. by rewrite in_dinsupp dunit1E eqxx oner_neq0. Qed.

Lemma rel_complete_d (c : cmd) (P Q : assn) ps' :
  hl_ ps' P c Q -> (forall ps, derivable ps (cl_mgt ps') P c Q).
Proof.
elim: c P Q => [ | | T x e | T x d | e c1 ih1 c2 ih2 | e c0 ih0 | c1 ih1 c2 ih2 | f ] P Q Hhl ps.
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
  pose I : assn := [pred s | `[< range Q (ssem_ ps' (While e Do c0) s) >]].
  apply: (H_Consequence (P2 := I) (Q2 := (I /\ `[{~~e}])%A)).
  +  move=> m Pm; apply/asboolP ; exact: (Hhl m Pm).
  + move=> s /andP[/asboolP HIs es].
    have es' : ~~ esem e s by exact: es.
    by apply: (HIs s); rewrite ssem_while0 //; exact: in_dinsupp_dunit.
  + apply: H_While; apply: ih0 => s /andP[/asboolP HIs es] s' s'in.
    apply/asboolP => t tin.
    have es' : esem e s by exact: es.
    apply: (HIs t); rewrite ssem_whileS // ssem_seqE.
    by apply: dlet_dinsupp; [exact: s'in | exact: tin].
- (* seq *)
  pose R : assn := [pred s' | `[< exists2 m, P m & s' \in dinsupp (ssem_ ps' c1 m) >]].
  apply: (H_Seq (Q := R)).
  + apply: ih2 => s' /asboolP[m Pm s'in] y yin.
    have H := Hhl m Pm; rewrite ssem_seqE in H.
    by apply: (H y); apply: dlet_dinsupp; [exact: s'in | exact: yin].
  + apply: ih1 => m Pm s' s'in; apply/asboolP; by exists m.
- (* call *)
  apply: H_khl.
  apply: (H_adapt (P2 := get_pre (cl_mgt ps' f)) (Q2 := get_post (cl_mgt ps' f))) => //.
  + move=> m0 Pm0 m hm; have H := Hhl m0 Pm0; rewrite ssem_call_eq in H.
    exact: (H m hm).
  + by apply: H_call; right.
Qed.

Lemma rel_complete (c : cmd) (P : assn) (Q : assn2) ps:
  khl_ ps P c Q -> forall ps', derivable2 ps' (cl_mgt ps) P c Q.
Proof.
move=> /khl_hl h ps'; apply: H_hl => s0; exact: (rel_complete_d (h s0)).
Qed.

Theorem khoare_complete: forall P c Q ps cl,
  khl_ ps P c Q -> derivable2 ps cl P c Q.
Proof.
move=> P c Q ps cl Hvalid.
apply: (H_rec  (cl:=(cl_mgt ps))).
- by move=> p' ps'; apply: rel_complete=> m _ s hs.
- exact: rel_complete Hvalid.
Qed.

Theorem hoare_complete: forall P c Q ps cl,
  hl_ ps P c Q -> derivable ps cl P c Q.
Proof.
move=> P c Q ps cl Hvalid.
apply: H_khl.
apply khoare_complete.
by apply hl_khl.
Qed.

End Complete.

End HL.

Section Misc.

Notation cmd := (@cmd ident ident cmem).

(* -------------------------------------------------------------------- *)
Definition eqon (X : pred { t : IhbType.type & vars t } ) (m : cmem) :=
  (fun m' : cmem => forall x, x \in X -> m.[tagged x] = m'.[tagged x]).

Arguments eqon : simpl never.

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
  | call n => pred0
end.

Fixpoint nocall (c:cmd) : Prop :=
  match c with
  | abort    => True
  | skip     => True
  | x <<- _  => True
  | x <$- _  => True
  | c1 ;; c2 => nocall c1 /\ nocall c2

  | If _ then c1 else c2 => nocall c1 /\ nocall c2
  | While _ Do c         => nocall c
  | call n => False
  end.

(* -------------------------------------------------------------------- *)
Definition eaccess {t} (e : expr t) : pred { t : IhbType.type & vars t } :=
  match e with
  | var_ _ x => [pred y | `[<y = Tagged _ x>]]
  | _ => pred0
  end.

(* -------------------------------------------------------------------- *)
Global Instance eqon_R Z : Equivalence (eqon Z).
Proof.
constructor=> //; first by move=> c1 c2 eq x /eq ->.
by move=> c1 c2 c3 eq1 eq2 x xX; rewrite eq1 ?eq2.
Qed.

(* -------------------------------------------------------------------- *)

Lemma mod_spec c m ps :
  nocall c ->
   hl_ ps [pred m' | m == m'] c
       [pred m' | `[<eqon (predC (mod c)) m m'>] ].
Proof.
  elim: c m.
+ by move=> m hcall ; apply hl_abort.
+ move=>  m hcall; pose P := [pred m' | m == m'].
  apply (hl_conseq (P2 := P) (Q2 := P))=> //; last exact/hl_skip.
  by move=> m' /eqP ->; apply/asboolT.
+ move=> t x e m hcall; set Q := (Q in hl_ ps _ _ Q).
  pose R := [pred m' | Q m'.[x <- `[{e}] m']].
  apply (hl_conseq (P2 := R) (Q2 := Q))=> //; last exact/hl_assign.
  move=> m' /eqP <-; apply/asboolP=> -[u y] /asboolP /=.
  move/eq_vars=> neq; rewrite mget_neq //.
  by case: eqP neq; intuition.
+ move=> t x d m hcall; set Q := (Q in hl_ ps _ _ Q).
  pose R := forall_in `[{d}] (fun v m => Q m.[x <- v]).
  apply (hl_conseq (P2 := R) (Q2 := Q)) => //; last exact/hl_random.
  move=> m' /= /eqP <-; apply/asboolP => z.
  move=> zQ; apply/asboolP => -[u y] /asboolP /eq_vars /= neq.
  by rewrite mget_neq //; case: eqP neq; intuition.
+ move=> e c1 ih1 c2 ih2 m /= [hcall1 hcall2]; apply hl_if.
  * pose P := [pred m' | m == m'].
    pose Q := [pred m' | `[<eqon (predC (mod c1)) m m'>]].
    apply (hl_conseq (P2 := P) (Q2 := Q)); last exact /ih1.
    - by move=> m' /= /andP [/eqP <-].
    move=> m' /asboolP eq_m_m'; apply/asboolP=> z.
    by case/norP => [cz1 cz2]; rewrite eq_m_m'.
  * pose P := [pred m' | m == m'].
    pose Q := [pred m' | `[<eqon (predC (mod c2)) m m'>]].
    apply (hl_conseq (P2 := P) (Q2 := Q)); last exact/ih2.
    - by move=> m' /= /andP [/eqP <-].
    move=> m' /asboolP eq_m_m'; apply/asboolP=> z.
    by case/norP => [cz1 cz2]; rewrite eq_m_m'.
+ move=> e c ihc m /= hcall.
  pose P := ([pred m' | `[< eqon (~ mod c)%A m m' >]])%A.
  pose Q := ([pred m' | `[< eqon (~ mod c)%A m m' >]] /\ `[{~~ e}])%A.
  apply (hl_conseq (P2 := P) (Q2 := Q)).
  + by move=> m' /eqP <-; apply /asboolP.
  + by move=> m' /andP [].
  apply/hl_while=> m1 /andP[] /asboolP Hm1 _.
  apply: (@range_weaken _ [pred m' | `[< eqon (~ mod c)%A m1 m' >]]).
  + move=> x /asboolP eq_m1_x; apply/asboolP=> z Hz.
    by rewrite Hm1 // eq_m1_x.
  by apply (ihc m1)=> //=.
+ move=> c1 ih1 c2 ih2 m /= [hcall1 hcall2] ; eapply hl_seq; first by apply (ih1 m).
  move=> m1 /asboolP Hm1.
  apply: (@range_weaken _ [pred m' | `[< eqon (~ mod c2)%A m1 m' >]]).
  + move=> x /asboolP Hx; apply/asboolP=> z /=.
    by case/norP => [/= zc1 zc2]; rewrite Hm1 // Hx.
    by apply (ih2 m1) => /=.
+ by move => ?? /=.
Qed.

(* -------------------------------------------------------------------- *)
Lemma modll c mu m ps :   nocall c -> lossless predT c ->
  \P_[mu]         [pred m' | `[<eqon (predC (mod c)) m m'>] ] =
  \P_[dssem ps c mu] [pred m' | `[<eqon (predC (mod c)) m m'>] ].
Proof.
move=> hcall ll; rewrite pr_dlet pr_exp; apply/eq_exp => m' _.
apply/esym; rewrite !inE; case/boolP: (X in (_ X)%:R) => /= /asboolP h.
+ pose P := [pred m' | `[< eqon (~ mod c)%A m m' >]]; suff: hl_ ps P c P.
  - by move=> Hr; rewrite (hl_ll Hr) ?ll //; apply/asboolP.
  move=> m''; rewrite !inE => /asboolP eqm''.
  apply: (range_weaken (P1 := [pred m' | `[< eqon (~ mod c)%A m'' m' >]])).
  + by move=> m3 /asboolP eqm3; apply/asboolP; rewrite eqm''.
  by apply/mod_spec => //=; rewrite inE.
+ rewrite (eq_in_pr (B := pred0)) ?pr_pred0 // => m''.
  move/mod_spec=> /(_ _ hcall (eqxx _)) => /asboolP eq_m'_m''.
  by apply/asboolPn => eq_m_m''; apply/h; rewrite eq_m'_m''.
Qed.

End Misc.
