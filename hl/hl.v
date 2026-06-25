(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp           Require Import all_boot all_order.
From mathcomp.algebra   Require Import all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals.
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
Section Hl.
Context {X Y : eqType} {mem : memType X} (ps: Y -> (@cmd_ X mem Y)).

Notation assn := (pred mem).
Notation assn2 := (mem -> pred mem).
Notation cmd  := (@cmd_ X mem Y).

Definition psi := Y -> (@cmd_ X mem Y).

(* -------------------------------------------------------------------- *)
(* Classical Hoare triple                                               *)
(* -------------------------------------------------------------------- *)

Definition hl_ (ps: psi) (P : assn) (c : cmd) (Q : assn) :=
  forall m, P m -> range Q (ssem_ ps c m).

Arguments hl_ ps P%_A c%_S Q%_A.

Notation hl   := (hl_ ps).

Definition forall_in {T : IhbType.type} (mu : mem -> Distr T) (P : T -> assn) : assn :=
  `[< fun m => forall t,  t \in dinsupp (mu m) -> P t m >]%A.

Notation "`[ 'forall' x 'in' mu => Q ]" :=
  (@forall_in _ mu%A (fun x => Q)): assn.

Notation "`[ 'forall' x 'in' mu | m => Q ]" :=
  (@forall_in _ mu%A (fun x m => Q)): assn.

(* -------------------------------------------------------------------- *)
(* Pratical Hoare triple                                                *)
(* -------------------------------------------------------------------- *)

Definition khl_ (ps: psi) (P : assn) (c : cmd) (Q : assn2) :=
  forall m, P m -> range (Q m) (ssem_ ps c m).

Arguments khl_ ps P%_A c%_S Q%_A.

Notation khl   := (khl_ ps).

Lemma khl_hl P c Q :
  khl P c Q <-> (forall s0, hl (xpredI P (fun s => s == s0)) c (Q s0)).
Proof.
  split.
  + by move=> h s0 ? /andP [] ? /eqP ?; subst s0; apply h.
    move => h s hP.
    apply: (h s).
    by apply/andP.
Qed.

Lemma hl_khl P c Q :
  khl P c (fun _ => Q) <-> hl P c Q.
Proof.
  by split; move => h s hP; apply h.
Qed.

Lemma khl_khl P c Q :
  khl xpredT c (fun s0 s =>  P s0 ==> Q s0 s) <-> khl P c Q.
Proof.
  split.
  + move => h s HP.
  have := (h s isT).
  rewrite /range => H m He.
  revert HP.
  apply /implyP.
  by apply H.
  + move => h s HP.
  have := (h s).
  rewrite /range => H m He.
  apply /implyP => ?.
  by apply: H.
Qed.

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
  hl (Pr /\ `[{e}])   c1 Po ->
  hl (Pr /\ `[{~~e}]) c2 Po ->
  hl Pr (If e then c1 else c2)%S Po.
Proof.
by move=> H1 H2 m Hm; rewrite ssemE; case: ifPn => He;
  [apply H1 | apply H2] => /=; rewrite Hm.
Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_while (I : assn) (e:expr_ X mem bool) (c:cmd):
  hl (I /\ `[{e}]) c I ->
  hl I (While e Do c) (I /\ `[{~~e}]).
Proof.
move=> Hc m Hm; rewrite ssemE; apply/range_dlim=> n.
elim: n m Hm => [|n Hn] m Hm /=.
+ by rewrite ssemE; apply range_dnull.
apply (@hl_if I)=> //; last by apply hl_skip.
by apply (hl_seq Hc)=> ??; apply Hn.
Qed.

(* -------------------------------------------------------------------- *)

(** Definition of a procedure contract **)

Definition clause : Type := assn * assn2.

Definition get_pre (an:clause) :=
  let (pre,post) := an in
  pre.

Definition get_post (an:clause) :=
  let (pre,post) := an in
  post.

Definition phi : Type := Y -> clause.

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx (cl : phi) (ps: psi) (P: assn) (Q: assn2) (c: cmd) :=
  (forall p, khl_ ps (get_pre (cl p)) (call p) (get_post (cl p))) ->
  khl_ ps P c Q.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx (cl : phi) (ps_init :psi):=
  forall p ps, hoare_triple_ctx cl ps (get_pre (cl p)) (get_post (cl p)) (ps_init p).


Fixpoint inliner (c:cmd) inline :=
  match c with
  | seqc p1 p2 => seqc (inliner p1 inline) (inliner p2 inline)
  | cond b p1 p2 => cond b (inliner p1 inline) (inliner p2 inline)
  | while b p => while b (inliner p inline)
  | call f => inline f
  | _ => c
  end.

Fixpoint k_inliner1 n (c:cmd) (ps : psi) :=
  match n with
  | 0 => while (cst_ true) skip
  | S n' => inliner c (fun f => k_inliner1 n' (ps f) ps)
  end.

Definition k_inliner_ps1 n ps := fun p => k_inliner1 n (ps p) ps.

Fixpoint k_inliner2 n (c:cmd) (ps : psi) :=
  match n with
  | 0 => c
  | S n' => inliner c (fun f => k_inliner2 n' (ps f) ps)
  end.

Definition k_inliner_ps2 n ps := fun p => k_inliner2 n (ps p) ps.

Definition false_ps : psi := (fun _ => while (cst_ true) skip).

Lemma while_true_null s :
  dnull = \dlim_(n) ubn [eta dunit (T:=mem)] xpredT n s.
Proof.
  rewrite -(dlimC dnull).
  apply eq_dlim => n0.
  elim n0 => //=.
  move => n1 h.
  by rewrite dlet_unit h.
Qed.

Lemma ssem_loop_while (ps' : psi) s:
  ssem_ ps' (While true%:S Do skip) s = dnull.
Proof.
  rewrite semE //=.
  rewrite (eq_dlim (gn := fun _ => dnull)); last by rewrite dlimC.
  move=> k /=.
  elim k => [|{}k IHk] //=.
  +   by rewrite semE.
  by rewrite !semE dlet_unit IHk.
Qed.

Lemma ubnf_dnull n p s:
  (ubnf false_ps) n (p, s) = dnull.
Proof.
case n => [|{}n] //=.
rewrite (eq_dlim (gn := fun _ => dnull)); last by rewrite dlimC.
move=> k /=.
elim k => [|{}k IHk] //=.
by rewrite dlet_unit IHk.
Qed.

Lemma ssem_false_ps p s :
  ssem_ false_ps (call p) s = dnull.
Proof.
rewrite semE.
rewrite (eq_dlim (gn := fun _ => dnull)); last by rewrite dlimC.
move => n.
exact: ubnf_dnull.
Qed.

Lemma kinliner1_cseq n ps' p1 p2: k_inliner1 (S n) (seqc p1 p2) ps' =
                                seqc (k_inliner1 (S n) p1 ps') (k_inliner1 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner1_cif n ps' b p1 p2: k_inliner1 (S n) (cond b p1 p2) ps' =
                                 cond b (k_inliner1 (S n) p1 ps') (k_inliner1 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner1_cwhile n ps' p b: k_inliner1 (S n) (while b p) ps' =
                                           while b (k_inliner1 (S n) p ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner1_ccall n f ps' :
  k_inliner1 (S n) (call f) ps' = k_inliner1 n (ps' f) ps'.
Proof.
  reflexivity.
Qed.


Lemma kinliner2_cseq n ps' p1 p2: k_inliner2 (S n) (seqc p1 p2) ps' =
                                seqc (k_inliner2 (S n) p1 ps') (k_inliner2 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner2_cif n ps' b p1 p2: k_inliner2 (S n) (cond b p1 p2) ps' =
                                 cond b (k_inliner2 (S n) p1 ps') (k_inliner2 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner2_cwhile n ps' p b: k_inliner2 (S n) (while b p) ps' =
                                           while b (k_inliner2 (S n) p ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner2_ccall n f ps' :
  k_inliner2 (S n) (call f) ps' = k_inliner2 n (ps' f) ps'.
Proof.
  reflexivity.
Qed.

Lemma inline12_split n m (ps1 : psi) c :
  k_inliner1 (S n) (k_inliner2 m c ps1) ps1 =
  k_inliner1 ((S n) + m) c ps1.
Proof.
  move: n c ps1.
  elim m.
  + move => n c ps1 //=.
    by rewrite addn0.
  + move => {}m h n c ps1.
    elim c.
    1-4 : move => //=.
    + move => e ? hc1 ? hc2.
      rewrite kinliner2_cif.
      rewrite kinliner1_cif.
      rewrite hc1 hc2.
      by rewrite (kinliner1_cif (n + m.+1)).
    + move => e ? hc1.
      rewrite kinliner2_cwhile.
      rewrite kinliner1_cwhile.
      rewrite hc1.
      by rewrite (kinliner1_cwhile (n + m.+1)).
    + move => ? hc1 ? hc2.
      rewrite kinliner2_cseq.
      rewrite kinliner1_cseq.
      rewrite hc1 hc2.
      by rewrite (kinliner1_cseq (n + m.+1)).
    + move => s.
      rewrite kinliner2_ccall.
      rewrite h.
      rewrite (kinliner1_ccall (n + m.+1)).
      by rewrite addSnnS.
Qed.

Lemma dlim_whilen n e c0 (ps':psi) s:
  ssem_aux (ubnf ps' n) (While e Do c0) s =
    \dlim_(n0) ssem_aux (ubnf ps' n) (whilen e c0 n0) s.
Proof.
rewrite /=.
apply: eq_dlim => n0.
move: s; elim: n0 => [|n0 IHn0] s //=.
case: (`[{e}] s) => //=.
apply: eq_in_dlet; [by move=> s' _; rewrite IHn0 | by []].
Qed.


Lemma le_whilen_aux (l : (Y * mem) -> {distr mem / R}) n e c m m' :
  ssem_aux l (whilen e c n) m m' <= ssem_aux l (whilen e c n.+1) m m'.
Proof.
elim: n m m' => /= [|n ih] m m'.
  by rewrite dnullE ge0_mu.
case: (esem e m) => //.
apply/le_in_dlet.
by move=> {m'} m _ m'; apply/ih.
Qed.

Lemma hmono_whilen (l  : (Y * mem) -> {distr mem / R})
  e c m n p :
  (n <= p)%N ->
  ssem_aux l (whilen e c n) m <=1  ssem_aux l (whilen e c p) m.
Proof.
elim: p n => [|p ih] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le_np m'.
by apply/(le_trans (ih _ le_np m'))/le_whilen_aux.
Qed.

Lemma test8 (ps' : psi) c s:
  ssem_ ps' c s =
  \dlim_(n) ssem_aux (ubnf ps' n) c s.
Proof.
  move : s.
  elim c.
  1-4: by move => * //=; rewrite /ssem_ unlock /ssem_r dlimC.
  + move => e ? hc1 ? hc2 s //=.
    rewrite semE.
    case (`[{e}] s).
    + by rewrite hc1.
    + by rewrite hc2.
  + move => e c0 h s.
    rewrite semE.
    symmetry; under eq_dlim do rewrite dlim_whilen.
    rewrite dlim_dlim_com.
    + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
    + by move => k *; rewrite hmono_whilen .
    apply eq_dlim => n.
    move : s.
    elim n.
    + by move => ? //=;rewrite semE dlimC.
    + move => {}n hi s //=.
      rewrite semE.
      case :(`[{e}] s); [|by rewrite semE dlimC].
      + rewrite semE -dlet_dlim_diag' //=.
        + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
        + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
        + apply /eq_in_dlet;[| by rewrite h].
          by move => ??;rewrite hi.
  + move => c1 hc1 c2 hc2 s //=.
    rewrite semE.
    rewrite -dlet_dlim_diag' //=.
    + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
    + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
    + apply eq_in_dlet;[|by rewrite hc1].
      by move => *; rewrite hc2.
  + by move => f s; rewrite semE.
Qed.

Lemma ssem_ubnf_dnull (ps' : psi) c n s:
 ssem_aux (ubnf ps' n) c s =
   ssem_aux (fun _ => dnull) (k_inliner2 n c ps') s.
Proof.
  move : c s.
  elim n => [//=|n0 h c].
  elim c .
  1-4: move => * //=.
  + move => e ? hc1 ? hc2 s //=.
    case (`[{e}] s).
    + by rewrite hc1.
    + by rewrite hc2.
  + move => e c0 //= hi s.
    apply eq_dlim.
    move => n1.
    move :s.
    elim n1 => //=.
    move => n2 hii s.
    case (`[{e}] s) => //=.
    apply eq_in_dlet.
    + by move => s' ?;rewrite hii.
    + by rewrite hi.
  + move => ? hc1 ? hc2 s //=.
    apply: eq_in_dlet.
    + by move => ??; rewrite hc2.
    + by rewrite hc1.
  + move => f s //=.
Qed.

Lemma ubnf_ssem  c s:
  ssem_aux (fun _ => dnull) c s =
  ssem_ false_ps c s.
Proof.
  move :s.
  elim c.
  + 1-4: by move => * //=; rewrite !semE.
  + move => e ? hc1 ? hc2 s //=.
    rewrite semE.
    case (`[{e}] s).
    + by rewrite hc1.
    + by rewrite hc2.
  + move => e c0 //= hi s.
    rewrite semE.
    apply eq_dlim.
    move => n1.
    move :s.
    elim n1 => //=.
    + by move => s; rewrite semE.
    move => n2 hii s; rewrite semE.
    case (`[{e}] s) => //=.
    rewrite semE.
    apply eq_in_dlet.
    + by move => s' ?;rewrite hii.
    + by rewrite hi.
     by rewrite semE.
  + move => ? hc1 ? hc2 s //=.
    rewrite semE.
    apply: eq_in_dlet.
    + by move => ??; rewrite hc2.
    + by rewrite hc1.
    + move => f s //=.
      rewrite semE.
      rewrite -(dlimC dnull).
      apply eq_dlim => n0.
      case : n0 => //= ?.
      by rewrite -while_true_null.
Qed.

Lemma test9 (ps' : psi) c n s:
  forall ps0,
    ssem_ false_ps (k_inliner2 n c ps') s =
    ssem_ ps0 (k_inliner1 (S n) c ps') s.
Proof.
move=> ps0.
move: c s.
elim: n => [|n IH] c s.
- (* n = 0 *)
  move: s.
  elim: c.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    by rewrite ssem_false_ps ssem_loop_while.
- (* n.+1 *)
  move: s.
  elim: c.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    exact: IH.
Qed.

Lemma ssem_call_eq (ps0 : psi) f s:
  ssem_ ps0 (call f) s = ssem_ ps0 (ps0 f) s.
Proof.
rewrite [LHS]semE  [RHS]test8.
transitivity (\dlim_(n) ubnf ps0 n.+1 (f, s)).
  by apply/distr_eqP => x; rewrite (dlim_bump (fun n => ubnf ps0 n (f, s))).
by apply: eq_dlim => n /=.
Qed.

Lemma test5 (ps1 ps2: psi) c s n:
  ssem_ ps2 (k_inliner1 (S n) c ps1) s = ssem_ (k_inliner_ps1 n ps1) c s.
Proof.
move: ps2 c s.
elim: n => [|n IH] ps2 c s.
- (* n = 0 *)
  move: s.
  elim: c.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    by rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    by rewrite ssem_loop_while ssem_false_ps.
- (* n.+1 *)
  move: s.
  elim: c.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    by rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    rewrite IH.
    symmetry; rewrite ssem_call_eq /=.
    by rewrite IH.
Qed.

Lemma inline2_split n m (ps1 : psi) c s:
  ssem_ (k_inliner_ps1 (m + n) ps1) c s  =
  ssem_ (k_inliner_ps1 n ps1) (k_inliner2 m c ps1) s.
Proof.
move: c s.
elim: m => [|m IH] c s.
- by [].
- move: s.
  elim: c.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    by rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    rewrite -IH ssem_call_eq /= addSn.
    by rewrite test5.
Qed.

Lemma test1 (ps' : psi) c s:
  \dlim_(n) ssem_ (k_inliner_ps1 n ps') c s =  ssem_ ps' c s.
Proof.
  rewrite test8.
  apply: eq_dlim.
  + by move => ?; rewrite ssem_ubnf_dnull ubnf_ssem (test9 _ _ _ _ ps') test5.
Qed.

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

(* -------------------------------------------------------------------- *)
Lemma hl_ll (P Q : assn) (c:cmd) m:
  hl P c Q -> P m -> \P_[ssem_ ps c m] predT = 1 -> \P_[ssem_ ps c m] Q = 1.
Proof.
 by move=> Hhl /Hhl HP <-; rewrite !pr_exp;apply/eq_exp => x /HP ->.
Qed.

Definition ctxt := assn -> Y  -> assn2 -> Prop.

Definition addspecs (G : ctxt) (cl : phi) : ctxt :=
  fun P f Q =>
    G P f Q \/ [/\ P = get_pre (cl f) & Q = get_post (cl f)].

Inductive derivable : ctxt -> assn -> cmd -> assn -> Prop :=
  | H_Skip : forall P G,
      derivable G P skip P
  | H_Abort : forall P Q G,
      derivable G P abort Q
  | H_Asgn : forall {T : IhbType.type} x (e:expr_ X mem T) (Q : assn) G,
      derivable G [pred m | Q m.[x <- `[{e}]%A m]] (x <<- e) Q
  | H_Random : forall {T : IhbType.type} x (d:expr_ X mem (Distr T)) (Q : assn) G,
      derivable G `[forall v in `[{d}] | m => Q m.[x <- v]]%A (x <$- d) Q
  | H_Seq : forall P c Q d R G,
      derivable G Q d R -> derivable G P c Q -> derivable G P (c;;d) R
  | H_If : forall (Pr Po : assn) (e:expr_ X mem bool) (c1 c2:cmd) G,
      derivable G (Pr /\ `[{e}])%A   c1 Po ->
      derivable G (Pr /\ `[{~~e}])%A c2 Po ->
      derivable G Pr (If e then c1 else c2)%S Po
  | H_While : forall (I : assn) (e:expr_ X mem bool) (c:cmd) G,
      derivable G (I /\ `[{e}])%A c I ->
      derivable G I (While e Do c) (I /\ `[{~~e}])%A
  | H_Consequence : forall (P2 Q2 P1 Q1 : assn)(c : cmd) G,
      (forall m, P1 m -> P2 m) ->
      (forall m, Q2 m -> Q1 m) ->
      derivable G P2 c Q2 -> derivable G P1 c Q1
  | H_khl : forall P Q c G,
     derivable2 G P c (fun _ => Q) -> derivable G P c Q
  with derivable2 : ctxt -> assn -> cmd -> assn2 -> Prop :=
   | H_hl: forall P Q c G,
       (forall s0, derivable G (xpredI P (fun s => s == s0)) c (Q s0)) ->
       derivable2 G P c Q
   | H_call : forall P Q G f,
       G P f Q ->
       derivable2 G P (call f) Q
   | H_rec : forall P Q c cl G,
       (forall p', derivable2 (addspecs G cl) (get_pre (cl p')) (ps p') (get_post (cl p'))) ->
       derivable2 (addspecs G cl) P c Q ->
       derivable2 G P c Q.

Theorem hoare_complete: forall P c Q,
  khl_ ps P c Q -> derivable2 (fun _ _ _ => False) P c Q.
Proof.
Admitted.

End Hl.

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
Global Instance eqon_R X : Equivalence (eqon X).
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
