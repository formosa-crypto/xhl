From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp.analysis  Require Import sequences normedtype topology.
From mathcomp           Require finmap.
From xhl                Require Import misc rsum.
From xhl.pwhile         Require Import notations inhabited mem pwhile psemantic passn range.
From xhl.prhl           Require Import prhl.
From xhl.ehl            Require Import ehl_stmt.
From xhl.strassen       Require Import deficiency.

Import GRing.Theory Order.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope sem_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Section Star.
Context {R : realType}.

Local Notation Distr T := {distr T%type / R}.

Lemma esumEFinE {T : choiceType} (f : T -> R) :
  esummable [set: T] (EFin \o f) ->
  esum [set: T] (EFin \o f) = (rsum f)%:E.
Proof. by move=> sf; rewrite /rsum fineK// (esummable_esum_fin_num sf). Qed.


(* ==================================================================== *)
(* Star-extension of a sub-distribution                                  *)
(*                                                                      *)
(*   d^*(Some a) = d a       d^*(None) = 1 - |d|                        *)
(*                                                                      *)
(* [None] plays the role of the paper's distinguished element [*].       *)
(* ==================================================================== *)
Section DStar.
Context {A : choiceType}.

Implicit Types (d : Distr A).

Definition dstar_fun d (o : option A) : R :=
  if o is Some a then d a else 1 - rsum d.

Lemma ge0_dstar_fun d o : 0 <= dstar_fun d o.
Proof. by case: o => [a|] /=; [exact: ge0_mu | rewrite subr_ge0 le1_rsum]. Qed.

Lemma summable_dstar_fun d : esummable [set: option A] (EFin \o dstar_fun d).
Proof. by apply: esummable_optionT; exact: (summable_mu d). Qed.

Lemma esum_dstar_fun d : esum [set: option A] (EFin \o dstar_fun d) = 1%E.
Proof.
rewrite (esum_option (summable_dstar_fun d)).
have -> : (EFin \o dstar_fun d) \o some = EFin \o d by [].
by rewrite (esumEFinE d (summable_mu d)) /= -EFinD addrC subrK.
Qed.

Lemma le1_dstar_fun d : (esum [set: option A] (EFin \o dstar_fun d) <= 1)%E.
Proof. by rewrite esum_dstar_fun. Qed.

HB.instance Definition _ d :=
  @isDistribution.Build R (option A) (dstar_fun d)
    (ge0_dstar_fun d) (summable_dstar_fun d) (le1_dstar_fun d).

Definition dstar d := @locked (Distr (option A)) (dstar_fun d).

Lemma dstarE d o : dstar d o = dstar_fun d o.
Proof. by unlock dstar. Qed.

Lemma dstar_someE d a : dstar d (Some a) = d a.
Proof. by rewrite dstarE. Qed.

Lemma dstar_noneE d : dstar d None = 1 - dweight d.
Proof. by rewrite dstarE dweightE. Qed.

(* A star-extension is always a full distribution -- this is what lets   *)
(* eRHL relate programs with different termination probabilities.        *)
Lemma dweight_dstar d : dweight (dstar d) = 1.
Proof.
rewrite dweightE /rsum.
have -> : \esum_(o in [set: option A]) ((dstar d) o)%:E
        = esum [set: option A] (EFin \o dstar_fun d).
+ by apply: eq_esum => o _; rewrite dstarE.
by rewrite esum_dstar_fun.
Qed.

(* Lemma 3.4: on full distributions, [dstar] is the identity.            *)
Lemma dstar_full d : dweight d = 1 -> dstar d None = 0.
Proof. by move=> h; rewrite dstar_noneE h subrr. Qed.

Lemma cvg_dstar_dlim (mu : nat -> Distr A) :
  (forall n p, (n <= p)%N -> mu n <=1 mu p) ->
  forall a, ((fun n => dstar (mu n) a) @ \oo --> dstar (dlim mu) a)%classic.
Proof.
(* Only the *image filters* need to agree, not the sequences themselves:   *)
(* [near_eq_cvg_eq] gets that from a pointwise equality, so no             *)
(* extensionality is needed.                                              *)
move=> hmono [x|].
+ have -> : ((fun n => dstar (mu n) (Some x)) @ \oo) = ((fun n => mu n x) @ \oo).
  - by apply: near_eq_cvg_eq; apply: nearW => n; rewrite dstar_someE.
  rewrite dstar_someE; apply: cvg_dlim_pt.
  apply: nondecreasing_is_cvgn; first by move=> n p le; exact: hmono.
  by exists 1 => _ [n _ <-]; exact: le1_mu1.
have -> : ((fun n => dstar (mu n) None) @ \oo)
        = ((fun n => 1 - dweight (mu n)) @ \oo).
+ by apply: near_eq_cvg_eq; apply: nearW => n; rewrite dstar_noneE.
rewrite dstar_noneE.
by apply: cvgnB; [exact: cvg_cst | exact: cvg_dweight_dlim].
Qed.

End DStar.

Lemma eq_dstar {T : choiceType} {d d' : Distr T} : d =1 d' -> dstar d = dstar d'.
Proof.
move=> e; apply/distr_eqP => -[a|]; rewrite !dstarE /=; first exact: e.
by rewrite (eq_rsum e).
Qed.

(* ==================================================================== *)
(* [dstar] is a monad morphism  D -> D o option.                         *)
(*                                                                      *)
(* This is the lemma the whole soundness development rests on: skip,     *)
(* abort, assignment, sampling, sequence, block and every one-sided rule *)
(* are instances of it.                                                 *)
(* ==================================================================== *)

(* [dletE_rsum] and [espE_rsum] now live in rsum.v. *)

Lemma dweight_dlet {A B : choiceType} (d : Distr A) (t : A -> Distr B) :
  dweight (\dlet_(a <- d) t a) = rsum (fun a => d a * dweight (t a)).
Proof.
by rewrite (pr_dlet predT t d) espE_rsum; apply: eq_rsum => a; rewrite mulrC.
Qed.

Lemma rsum_dlet {A B : choiceType} (d : Distr A) (t : A -> Distr B) :
  rsum (\dlet_(a <- d) t a) = rsum (fun a => d a * rsum (t a)).
Proof.
rewrite -dweightE dweight_dlet.
by apply: eq_rsum => a; rewrite dweightE.
Qed.

Definition ostar {A B : choiceType} (t : A -> Distr B) (o : option A)
  : Distr (option B) :=
  if o is Some a then dstar (t a) else dunit None.

Lemma dstar_dlet {A B : choiceType} (d : Distr A) (t : A -> Distr B) :
  \dlet_(o <- dstar d) ostar t o = dstar (\dlet_(a <- d) t a).
Proof.
have key : forall o, rsum (fun o' => dstar d o' * ostar t o' o)
                   = rsum (fun a : A => d a * ostar t (Some a) o)
                   + (1 - rsum d) * (dunit None : Distr (option B)) o.
+ move=> o.
  have sm : esummable [set: option A]
              (EFin \o (fun o' => dstar d o' * ostar t o' o)).
  * by have := summable_dlet (ostar t) (dstar d) o; apply/eq_esummable.
  rewrite (rsum_option sm); congr (_ + _).
  * by apply: eq_rsum => a /=; rewrite dstarE.
  by rewrite /= dstarE.
have hd : forall a : A, 0 <= d a * rsum (t a) <= d a.
+ move=> a; apply/andP; split.
  * by rewrite mulr_ge0 ?ge0_mu ?ge0_rsum.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l ?ge0_mu ?le1_rsum.
apply/distr_eqP => o; rewrite dletE_rsum dstarE key.
case: o => [z|] /=.
+ rewrite dunit1E /= mulr0 addr0 dletE_rsum.
  by apply: eq_rsum => a /=; rewrite dstarE.
rewrite dunit_id mulr1 rsum_dlet.
have -> : rsum (fun a : A => d a * ostar t (Some a) None)
        = rsum d - rsum (fun a : A => d a * rsum (t a)).
+ rewrite -(rsumB hd (summable_mu d)); apply: eq_rsum => a /=.
  by rewrite dstarE /= mulrBr mulr1.
by rewrite addrAC addrCA subrr addr0.
Qed.

Lemma dstar_dunit {A : choiceType} (a : A) : dstar (dunit a) = dunit (Some a).
Proof.
apply/distr_eqP => -[b|]; rewrite dstarE /=; first by rewrite !dunit1E.
by rewrite -dweightE pr_dunit /= subrr dunit1E.
Qed.

Lemma dstar_dmargin {A B : choiceType} (h : A -> B) (d : Distr A) :
  dmargin (omap h) (dstar d) = dstar (dmargin h d).
Proof.
rewrite !dmarginE -(dstar_dlet d (fun a => dunit (h a))).
apply: eq_in_dlet => //; case=> [a|] _ //=.
by rewrite dstar_dunit.
Qed.

Lemma dstar_dnull {A : choiceType} : dstar (@dnull R A) = dunit None.
Proof.
have rn : rsum (@dnull R A) = 0.
+ by rewrite -[RHS](@rsum0 R A); apply: eq_rsum => x; exact: dnullE.
apply/distr_eqP => -[a|]; rewrite dstarE /=.
+ by rewrite dnullE dunit1E.
by rewrite rn subr0 dunit_id.
Qed.

(* -------------------------------------------------------------------- *)
(* Small expectation / marginal utilities used throughout.               *)
(* -------------------------------------------------------------------- *)

Lemma le_espe {T : choiceType} (mu : Distr T) (f g : T -> \bar R) :
  (forall x, (f x <= g x)%E) -> (espe mu f <= espe mu g)%E.
Proof.
move=> h; rewrite /espe; apply: le_esum => x _; apply: lee_wpmul2r.
+ by apply: lee_tofin; apply: ge0_mu.
exact: h.
Qed.

(* [dmargin_comp] and [eq_dmargin] now live in rsum.v. *)

Lemma eexp_dmargin {T U : choiceType} (mu : Distr T) (h : T -> U)
    (F : U -> \bar R) :
  (forall x, (0 <= F x)%E) -> espe (dmargin h mu) F = espe mu (F \o h).
Proof.
move=> hF; rewrite dmarginE eexp_dlet //.
by apply: eexp_eq => x; rewrite eexp_dunit.
Qed.

Lemma pr_dstar {T : choiceType} (d : Distr T) (E : pred T) :
  \P_[dstar d] [pred o | if o is Some a then E a else false] = \P_[d] E.
Proof.
rewrite !prE_rsum.
have sm : esummable [set: option T]
  (EFin \o (fun o => ([pred o | if o is Some a then E a else false] o)%:R
                     * dstar d o)).
+ by have := summable_pr [pred o | if o is Some a then E a else false] (dstar d);
     apply/eq_esummable.
rewrite (rsum_option sm) /= mul0r addr0.
by apply: eq_rsum => a /=; rewrite dstarE.
Qed.

(* ==================================================================== *)
(* Star-couplings (Definition 3.3)                                       *)
(*                                                                      *)
(* Contrast with [prhl.iscoupling]: a star-coupling is a *full*          *)
(* distribution on [option A * option B] whose marginals are the         *)
(* star-extensions, so the two programs need not terminate with the      *)
(* same probability.                                                     *)
(* ==================================================================== *)
Section SCoupling.
Context {A B : choiceType}.

Definition scoupling (d1 : Distr A) (d2 : Distr B)
    (nu : Distr (option A * option B)%type) :=
  dfst nu = dstar d1 /\ dsnd nu = dstar d2.

Lemma scoupling_eq (d1 d1' : Distr A) (d2 d2' : Distr B) nu :
  d1 =1 d1' -> d2 =1 d2' -> scoupling d1 d2 nu -> scoupling d1' d2' nu.
Proof.
by move=> e1 e2 [h1 h2]; split; [rewrite h1 (eq_dstar e1) | rewrite h2 (eq_dstar e2)].
Qed.

(* Every pair of sub-distributions admits a star-coupling: the product   *)
(* of the two star-extensions.  Used for Lemma 4.6 and to show that      *)
(* validity is never vacuous.                                           *)
Definition dprod {T U : choiceType} (m1 : Distr T) (m2 : Distr U) :=
  \dlet_(x <- m1) (\dlet_(y <- m2) dunit (x, y)).

Lemma dfst_dprod {T U : choiceType} (m1 : Distr T) (m2 : Distr U) :
  dweight m2 = 1 -> dfst (dprod m1 m2) = m1.
Proof.
move=> w2.
have inner : forall y : T, dmargin fst (\dlet_(t <- m2) dunit (y, t)) = dunit y.
+ move=> y; rewrite dmargin_dlet.
  have -> : \dlet_(t <- m2) dmargin fst (dunit (y, t)) = \dlet_(_ <- m2) dunit y.
  - by apply: eq_in_dlet => // t _; rewrite dmargin_dunit.
  by apply/distr_eqP => z; rewrite dletC w2 mul1r.
rewrite /dprod dmargin_dlet.
have -> : \dlet_(y <- m1) dmargin fst (\dlet_(t <- m2) dunit (y, t))
        = \dlet_(y <- m1) dunit y.
+ by apply: eq_in_dlet => // y _; exact: inner.
by rewrite dlet_dunit_id.
Qed.

Lemma dsnd_dprod {T U : choiceType} (m1 : Distr T) (m2 : Distr U) :
  dweight m1 = 1 -> dsnd (dprod m1 m2) = m2.
Proof.
move=> w1.
have inner : forall y : T, dmargin snd (\dlet_(t <- m2) dunit (y, t)) = m2.
+ move=> y; rewrite dmargin_dlet.
  have -> : \dlet_(t <- m2) dmargin snd (dunit (y, t)) = \dlet_(t <- m2) dunit t.
  - by apply: eq_in_dlet => // t _; rewrite dmargin_dunit.
  by rewrite dlet_dunit_id.
rewrite /dprod dmargin_dlet.
have -> : \dlet_(y <- m1) dmargin snd (\dlet_(t <- m2) dunit (y, t))
        = \dlet_(_ <- m1) m2.
+ by apply: eq_in_dlet => // y _; exact: inner.
by apply/distr_eqP => y; rewrite dletC w1 mul1r.
Qed.

Lemma scoupling_prod (d1 : Distr A) (d2 : Distr B) :
  scoupling d1 d2 (dprod (dstar d1) (dstar d2)).
Proof.
by split; [apply: dfst_dprod | apply: dsnd_dprod]; exact: dweight_dstar.
Qed.

Lemma exists_scoupling (d1 : Distr A) (d2 : Distr B) :
  exists nu, scoupling d1 d2 nu.
Proof. by exists (dprod (dstar d1) (dstar d2)); exact: scoupling_prod. Qed.

Lemma scoupling_dunit (a : A) (b : B) :
  scoupling (dunit a) (dunit b) (dunit (Some a, Some b)).
Proof. by split; rewrite dmargin_dunit /= dstar_dunit. Qed.

(* An *ordinary* coupling is a star-coupling once the missing mass -- the *)
(* same on both sides, since [iscoupling] forces |d1| = |nu| = |d2| -- is  *)
(* parked on (None, None).                                                *)
Definition slift (nu : Distr (A * B)%type) : Distr (option A * option B)%type :=
  dmargin (fun o => if o is Some p then (Some p.1, Some p.2) else (None, None))
          (dstar nu).

Lemma scoupling_slift (d1 : Distr A) (d2 : Distr B) nu :
  iscoupling d1 d2 nu -> scoupling d1 d2 (slift nu).
Proof.
have e1 : (fun o : option (A * B)%type =>
    fst (if o is Some p then (Some p.1, Some p.2) else (None, None)))
  =1 omap fst by case.
have e2 : (fun o : option (A * B)%type =>
    snd (if o is Some p then (Some p.1, Some p.2) else (None, None)))
  =1 omap snd by case.
case=> h1 h2; split; rewrite /slift dmargin_comp /comp.
+ by rewrite (eq_dmargin _ e1) dstar_dmargin h1.
by rewrite (eq_dmargin _ e2) dstar_dmargin h2.
Qed.

End SCoupling.

(* A star-coupling with [dunit m2] on the right is concentrated on the      *)
(* slice _ x {Some m2}.  This is what makes one-sided judgments unary.      *)
Lemma scoupling_supp2 {C : choiceType} (mu : Distr C) (m2 : C)
    (nu : Distr (option C * option C)%type) :
  scoupling mu (dunit m2) nu -> forall p, p \in dinsupp nu -> p.2 = Some m2.
Proof.
case=> _ h2 p hp; apply/eqP; apply: contraT => hne.
have h0 : dsnd nu p.2 = 0.
+ by rewrite h2 dstar_dunit dunit1E eq_sym (negbTE hne).
have hle := le_dsnd nu p; rewrite h0 in hle.
have hz : nu p = 0 by apply/eqP; rewrite eq_le hle ge0_mu.
by move: hp; rewrite in_dinsupp hz eqxx.
Qed.

(* Pushing a pair of deterministic maps through a star-coupling.  Used by  *)
(* the [block] rules (return-value restoration).                           *)
Lemma scoupling_dmargin {C: choiceType} (d1 d2 : Distr C)
    (nu : Distr (option C * option C)%type) (k1 k2 : C -> C) :
  scoupling d1 d2 nu ->
  scoupling (dmargin k1 d1) (dmargin k2 d2)
            (dmargin (fun p => (omap k1 p.1, omap k2 p.2)) nu).
Proof.
case=> h1 h2; split; rewrite dmargin_comp /comp.
+ have -> : (fun p : option C * option C => (omap k1 p.1, omap k2 p.2).1)
          = omap k1 \o fst by [].
  by rewrite -dmargin_comp h1 dstar_dmargin.
have -> : (fun p : option C * option C => (omap k1 p.1, omap k2 p.2).2)
        = omap k2 \o snd by [].
by rewrite -dmargin_comp h2 dstar_dmargin.
Qed.

(* Star-couplings are full distributions. *)
Lemma dweight_scoupling {C: choiceType} (d1 d2 : Distr C)
    (nu : Distr (option C * option C)%type) :
  scoupling d1 d2 nu -> dweight nu = 1.
Proof.
case=> h1 _; have := dweight_dstar d1; rewrite -h1 (pr_dmargin predT fst nu).
by rewrite (eq_pr (B := predT)).
Qed.

(* When both sides are lossless, a star-coupling puts no mass on a pair    *)
(* with a [None] component: [dstar_full] kills the [None] cell of either   *)
(* marginal, and [le_dfst] / [le_dsnd] propagate that to the joint.        *)
Lemma scoupling_full_supp {C: choiceType} (D1 D2 : Distr C)
    (nu : Distr (option C * option C)%type) :
  dweight D1 = 1 -> dweight D2 = 1 -> scoupling D1 D2 nu ->
  forall p, p \in dinsupp nu ->
    (if p is (Some _, Some _) then true else false).
Proof.
move=> w1 w2 hnu.
have hz1 : forall b, nu (None, b) = 0.
+ move=> b; apply/eqP; rewrite eq_le ge0_mu andbT.
  by have := le_dfst nu (None, b); rewrite (proj1 hnu) /= (dstar_full D1 w1).
have hz2 : forall a, nu (a, None) = 0.
+ move=> a; apply/eqP; rewrite eq_le ge0_mu andbT.
  by have := le_dsnd nu (a, None); rewrite (proj2 hnu) /= (dstar_full D2 w2).
case=> [[a|] [b|]] hin //.
+ have h : (Some a, @None C) \notin dinsupp nu by apply/dinsuppPn; exact: hz2.
  by rewrite hin in h.
+ have h : (@None C, Some b) \notin dinsupp nu by apply/dinsuppPn; exact: hz1.
  by rewrite hin in h.
have h : (@None C, @None C) \notin dinsupp nu
  by apply/dinsuppPn; exact: hz1.
by rewrite hin in h.
Qed.

Lemma espe_dstar {T : choiceType} (d : Distr T) (F : option T -> \bar R) :
  (forall o, (0 <= F o)%E) -> F None = 0%E ->
  espe (dstar d) F = espe d (F \o some).
Proof.
move=> hF hN; rewrite /espe.
have hge0 : forall o, (0 <= F o * (dstar d o)%:E)%E.
+ by move=> o; rewrite mule_ge0 // lee_fin ge0_mu.
rewrite (esum_option_ge0 hge0) hN mul0e adde0.
by apply: eq_esum => x _ /=; rewrite dstarE.
Qed.

Lemma scoupling_dlet {A B A' B' : choiceType}
    (d1 : Distr A) (d2 : Distr B) (nu : Distr (option A * option B)%type)
    (t1 : A -> Distr A') (t2 : B -> Distr B')
    (k : option A * option B -> Distr (option A' * option B')%type) :
  scoupling d1 d2 nu ->
  (forall p, dfst (k p) = ostar t1 p.1) ->
  (forall p, dsnd (k p) = ostar t2 p.2) ->
  scoupling (\dlet_(a <- d1) t1 a) (\dlet_(b <- d2) t2 b) (\dlet_(p <- nu) k p).
Proof.
case=> h1 h2 k1 k2; split; rewrite dmargin_dlet.
+ have -> : \dlet_(p <- nu) dfst (k p) = \dlet_(p <- nu) ostar t1 p.1.
  * by apply: eq_in_dlet => // p _; exact: k1.
  by rewrite -dlet_dmargin h1 dstar_dlet.
have -> : \dlet_(p <- nu) dsnd (k p) = \dlet_(p <- nu) ostar t2 p.2.
+ by apply: eq_in_dlet => // p _; exact: k2.
by rewrite -dlet_dmargin h2 dstar_dlet.
Qed.

(* Stated outside the section: the two sides swap types. *)
Lemma scoupling_swap {A B : choiceType}
    (d1 : Distr A) (d2 : Distr B) (nu : Distr (option A * option B)%type) :
  scoupling d1 d2 nu -> scoupling d2 d1 (dswap nu).
Proof.
case=> h1 h2; split.
+ by apply/distr_eqP => o; rewrite dfst_dswap h2.
by apply/distr_eqP => o; rewrite dsnd_dswap h1.
Qed.

End Star.
