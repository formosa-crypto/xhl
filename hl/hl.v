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

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope sem_scope.
Local Open Scope mem_scope.

(* -------------------------------------------------------------------- *)
Section Hl.
Context {X Y : eqType} {mem : memType X} (ps: Y -> (@cmd_ X mem Y)).

Notation assn := (pred mem).
Notation cmd  := (@cmd_ X mem Y).

Definition psi := Y -> (@cmd_ X mem Y).

Definition hl_ (ps: psi) (P : assn) (c : cmd) (Q : assn) :=
  forall m, P m -> range Q (ssem_ ps c m).

Arguments hl_ ps P%_A c%_S Q%_A.

Notation hl   := (@hl_ ps).

Definition forall_in {T : IhbType.type} (mu : mem -> Distr T) (P : T -> assn) : assn :=
  `[< fun m => forall t,  t \in dinsupp (mu m) -> P t m >]%A.

Notation "`[ 'forall' x 'in' mu => Q ]" :=
  (@forall_in _ mu%A (fun x => Q)): assn.

Notation "`[ 'forall' x 'in' mu | m => Q ]" :=
  (@forall_in _ mu%A (fun x m => Q)): assn.

(* -------------------------------------------------------------------- *)
(* Core rules                                                           *)
(* -------------------------------------------------------------------- *)
Lemma hl_eq (P Q : assn) (c c' : cmd) :
     (forall m, P m -> ssem_ ps c m = ssem_ ps c' m)
  -> hl P c Q
  -> hl P c' Q.
Proof. by move=> Hc Hw m Pm;rewrite -Hc //;apply Hw. Qed.

(* -------------------------------------------------------------------- *)

Instance hl_m : Proper (eq ==> @eqcmd _ _ mem ps ==> eq ==> iff) hl.
Proof. by move=> ??-> ??? ??->;split;apply hl_eq. Qed.

(* -------------------------------------------------------------------- *)

Lemma hl_conseq (P2 Q2 P1 Q1 : assn) (c : cmd):
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
Proof. by move=> ??;rewrite ssemE;apply range_dunit. Qed.

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

Definition clause : Type := assn * assn.

Definition get_pre (an:clause) :=
  let (pre,post) := an in
  pre.

Definition get_post (an:clause) :=
  let (pre,post) := an in
  post.

Definition phi : Type := Y -> clause.

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx (cl : phi) (ps: psi) (P: assn) (Q: assn) (c: cmd) :=
  (forall p, hl_ ps (get_pre (cl p)) (call p) (get_post (cl p))) ->
  hl_ ps P c Q.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx (cl : phi) (ps_init :psi):=
  forall p ps, hoare_triple_ctx cl ps (get_pre (cl p)) (get_post (cl p)) (ps_init p).

Lemma recursive_proc :
  forall ps cl,
  hoare_triple_proc_ctx cl ps ->
  (forall p, hl_ ps (get_pre (cl p)) (call p) (get_post (cl p))).
Proof.
  Admitted.
(*   intros. *)
(*   apply i_hoare_triple_hoare_triple. *)
(*   intros n. *)
(*   generalize dependent p. *)
(*   induction n. *)
(*   - intros p s s' HPre Heval. *)
(*     inversion Heval;subst. *)
(*     apply ceval_inf_loop in H1. *)
(*     contradiction H1. *)
(*   - intros p s s' HPre Heval. *)
(*     eapply H. *)
(*     + apply IHn. *)
(*     + apply HPre. *)
(*     + apply Inline1.n_inline_ps_inline in Heval. *)
(*       apply Heval. *)
(* Qed. *)

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple :
  forall P Q c cl,
    hoare_triple_proc_ctx cl ps  ->
    hoare_triple_ctx cl ps P Q c ->
    hl P c Q.
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
   hl ps [pred m' | m == m'] c
       [pred m' | `[<eqon (predC (mod c)) m m'>] ].
Proof. elim: c m.
+ by move=> m; apply hl_abort.
+ move=> m; pose P := [pred m' | m == m'].
  apply (hl_conseq (P2 := P) (Q2 := P))=> //; last exact/hl_skip.
  by move=> m' /eqP ->; apply/asboolT.
+ move=> t x e m; set Q := (Q in hl ps _ _ Q).
  pose R := [pred m' | Q m'.[x <- `[{e}] m']].
  apply (hl_conseq (P2 := R) (Q2 := Q))=> //; last exact/hl_assign.
  move=> m' /eqP <-; apply/asboolP=> -[u y] /asboolP /=.
  move/eq_vars=> neq; rewrite mget_neq //.
  by case: eqP neq; intuition.
+ move=> t x d m; set Q := (Q in hl ps _ _ Q).
  pose R := forall_in `[{d}] (fun v m => Q m.[x <- v]).
  apply (hl_conseq (P2 := R) (Q2 := Q)) => //; last exact/hl_random.
  move=> m' /= /eqP <-; apply/asboolP => z.
  move=> zQ; apply/asboolP => -[u y] /asboolP /eq_vars /= neq.
  by rewrite mget_neq //; case: eqP neq; intuition.
+ move=> e c1 ih1 c2 ih2 m; apply hl_if.
  * pose P := [pred m' | m == m'].
    pose Q := [pred m' | `[<eqon (predC (mod c1)) m m'>]].
    apply (hl_conseq (P2 := P) (Q2 := Q)); last exact/ih1.
    - by move=> m' /= /andP [/eqP <-].
    move=> m' /asboolP eq_m_m'; apply/asboolP=> z.
    by case/norP => [cz1 cz2]; rewrite eq_m_m'.
  * pose P := [pred m' | m == m'].
    pose Q := [pred m' | `[<eqon (predC (mod c2)) m m'>]].
    apply (hl_conseq (P2 := P) (Q2 := Q)); last exact/ih2.
    - by move=> m' /= /andP [/eqP <-].
    move=> m' /asboolP eq_m_m'; apply/asboolP=> z.
    by case/norP => [cz1 cz2]; rewrite eq_m_m'.
+ move=> e c ihc m.
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
+ move=> c1 ih1 c2 ih2 m; eapply hl_seq; first by apply (ih1 m).
  move=> m1 /asboolP Hm1.
  apply: (@range_weaken _ [pred m' | `[< eqon (~ mod c2)%A m1 m' >]]).
  + move=> x /asboolP Hx; apply/asboolP=> z /=.
    by case/norP => [/= zc1 zc2]; rewrite Hm1 // Hx.
    by apply (ih2 m1) => /=.
+ admit.
    Admitted.
(* Qed. *)

(* -------------------------------------------------------------------- *)
Lemma modll c mu m ps : lossless predT c ->
  \P_[mu]         [pred m' | `[<eqon (predC (mod c)) m m'>] ] =
  \P_[dssem ps c mu] [pred m' | `[<eqon (predC (mod c)) m m'>] ].
Proof.
move=> ll; rewrite pr_dlet pr_exp; apply/eq_exp => m' _.
apply/esym; rewrite !inE; case/boolP: (X in (_ X)%:R) => /= /asboolP h.
+ pose P := [pred m' | `[< eqon (~ mod c)%A m m' >]]; suff: hl ps P c P.
  - by move=> Hr; rewrite (hl_ll Hr) ?ll //; apply/asboolP.
  move=> m''; rewrite !inE => /asboolP eqm''.
  apply: (range_weaken (P1 := [pred m' | `[< eqon (~ mod c)%A m'' m' >]])).
  + by move=> m3 /asboolP eqm3; apply/asboolP; rewrite eqm''.
  by apply/mod_spec; rewrite inE.
+ rewrite (eq_in_pr (B := pred0)) ?pr_pred0 // => m''.
  move/mod_spec=> /(_ _ (eqxx _)) => /asboolP eq_m'_m''.
  by apply/asboolPn => eq_m_m''; apply/h; rewrite eq_m'_m''.
Qed.
