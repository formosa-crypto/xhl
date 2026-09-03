From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp           Require finmap.
From xhl                Require Import misc rsum.
From xhl.pwhile         Require Import notations inhabited pwhile psemantic passn range.
From xhl.prhl           Require Import prhl.
From xhl.ehl            Require Import ehl_stmt.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope sem_scope.
Local Open Scope classical_set_scope.

Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Local Notation cmd := (@cmd_ ident cmem ident).

Lemma esumEFinE {T : choiceType} (f : T -> R) :
  esummable [set: T] (EFin \o f) ->
  esum [set: T] (EFin \o f) = (rsum f)%:E.
Proof. by move=> sf; rewrite /rsum fineK// (esummable_esum_fin_num sf). Qed.

Lemma dweightE {T : choiceType} (d : Distr T) : dweight d = rsum d.
Proof. by rewrite prE_rsum; apply: eq_rsum => x /=; rewrite mul1r. Qed.

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

Lemma dletE_rsum {A B : choiceType} (mu : Distr A) (f : A -> Distr B) y :
  (\dlet_(x <- mu) f x) y = rsum (fun x => mu x * f x y).
Proof. by rewrite dletE. Qed.

Lemma espE_rsum {A : choiceType} (mu : Distr A) (g : A -> R) :
  \E_[mu] g = rsum (fun x => g x * mu x).
Proof. by []. Qed.

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

Lemma dmargin_comp {A B C : choiceType} (f : B -> C) (g : A -> B) (mu : Distr A) :
  dmargin f (dmargin g mu) = dmargin (f \o g) mu.
Proof. by rewrite [LHS]dmarginE dlet_dmargin. Qed.

(* Congruence for [dmargin] under a pointwise equality -- avoids needing    *)
(* functional extensionality to change the mapped function.                 *)
Lemma eq_dmargin {A B : choiceType} (k k' : A -> B) (mu : Distr A) :
  k =1 k' -> dmargin k mu = dmargin k' mu.
Proof.
by move=> e; rewrite !dmarginE; apply: eq_in_dlet => // a _; rewrite e.
Qed.

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
  = omap fst by apply/funext; case.
have e2 : (fun o : option (A * B)%type =>
    snd (if o is Some p then (Some p.1, Some p.2) else (None, None)))
  = omap snd by apply/funext; case.
case=> h1 h2; split; rewrite /slift dmargin_comp /comp.
+ by rewrite e1 dstar_dmargin h1.
by rewrite e2 dstar_dmargin h2.
Qed.

End SCoupling.

(* [misc.esum_option] needs summability, which fails as soon as the         *)
(* integrand can be +oo.  For a non-negative integrand [esumID] suffices.    *)
Lemma esum_option_ge0 {T : choiceType} (S : option T -> \bar R) :
  (forall o, (0 <= S o)%E) ->
  esum [set: option T] S = (esum [set: T] (S \o some) + S None)%E.
Proof.
move=> hS; rewrite (esumID [set None]) //.
rewrite setTI esum_set1 hset esum_image; first by move=> x y _ _ [->].
by rewrite addeC.
Qed.

Lemma espe_dstar {T : choiceType} (d : Distr T) (F : option T -> \bar R) :
  (forall o, (0 <= F o)%E) -> F None = 0%E ->
  espe (dstar d) F = espe d (F \o some).
Proof.
move=> hF hN; rewrite /espe.
have hge0 : forall o, (0 <= F o * (dstar d o)%:E)%E.
+ by move=> o; rewrite mule_ge0 // lee_fin ge0_mu.
rewrite (esum_option_ge0 _ hge0) hN mul0e adde0.
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

(* ==================================================================== *)
(* Relational pre- and post-expectations                                 *)
(* ==================================================================== *)
Section RCond.

(* Assertions are quantitative: [rmem = cmem * cmem -> \bar R].  The     *)
(* paper's [E<1>] / [E<2>] are pwhile's [e#'1] / [e#'2].                 *)
Definition rcond  := rmem -> \bar pwhile.R.

(* The "generic" post-expectation also reads the *initial* pair of       *)
(* memories.  This replaces the paper's type [Z] of logical variables    *)
(* (cf. [hl_stmt.assn2] and [ehl_stmt.cond2]).                          *)
Definition rcond2 := rmem -> rmem -> \bar pwhile.R.

(* [psi*]: the 0-extension of a post-expectation to starred memories.    *)
Definition rstar (g : rcond) (p : option cmem * option cmem) : \bar pwhile.R :=
  if p is (Some m1, Some m2) then g (m1, m2) else 0%E.

Lemma ge0_rstar g p : (forall m, (0 <= g m)%E) -> (0 <= rstar g p)%E.
Proof. by move=> h; rewrite /rstar; case: p => -[m1|] [m2|] //=; exact: h. Qed.

Lemma rstar_eq g g' : g =1 g' -> rstar g =1 rstar g'.
Proof. by move=> h; rewrite /rstar => -[[m1|] [m2|]] //=; rewrite h. Qed.

(* Symmetric assertion: [chi~ z (m1, m2) = chi z (m2, m1)]. *)
Definition rswap (f : rcond) : rcond := fun m => f (m.2, m.1).
Definition rswap2 (g : rcond2) : rcond2 :=
  fun m0 m => g (m0.2, m0.1) (m.2, m.1).

Lemma rswapK f : rswap (rswap f) =1 f.
Proof. by move=> [m1 m2]. Qed.

Lemma rswap2K g : forall m0 m, rswap2 (rswap2 g) m0 m = g m0 m.
Proof. by move=> [??] [??]. Qed.

(* Guard operator [P | phi] of the paper, at the relational type.        *)
Notation rlift := (@ehl_stmt.lift rident rmem).

(* Image of a set of memories under a relation, the paper's [R(M)].      *)
Definition rimage (Rl : rel cmem) (M : pred cmem) : pred cmem :=
  [pred m2 | `[< exists m1, M m1 && Rl m1 m2 >]].

End RCond.

Notation rlift := (@ehl_stmt.lift rident rmem).

(* Expectation through [slift]: the mass parked on (None, None) is        *)
(* invisible to [rstar], so nothing is lost.                              *)
Lemma espe_slift (nu : Distr (cmem * cmem)%type) (g : rcond) :
  (forall m, (0 <= g m)%E) -> espe (slift nu) (rstar g) = espe nu g.
Proof.
move=> hg.
have hpos : forall o : option (cmem * cmem)%type,
  (0 <= (rstar g \o (fun o' => if o' is Some p then (Some p.1, Some p.2)
                               else (@None cmem, @None cmem))) o)%E.
+ by move=> o; exact: ge0_rstar.
have hnone : (rstar g \o (fun o' => if o' is Some p then (Some p.1, Some p.2)
                                    else (@None cmem, @None cmem))) None = 0%E.
+ by [].
transitivity (espe (dstar nu)
  (rstar g \o (fun o' => if o' is Some p then (Some p.1, Some p.2)
                         else (@None cmem, @None cmem)))).
+ by rewrite /slift; apply: eexp_dmargin => p; exact: ge0_rstar.
rewrite (espe_dstar _ _ hpos hnone).
by apply: eexp_eq; case=> a b.
Qed.

(* [psemantic.mselect_mset] for global variables; missing upstream. *)
Lemma mselect_msetg {T : IhbType.type} s s' (m : rmem) (x : vars T) (v : T) :
  ((m.{x#s <- v})#s')%M = if s == s' then ((m#s).{x <- v})%M else (m#s')%M.
Proof. by case: s s' x => [] [] []. Qed.

(* Updating a variable with its own current value is the identity.         *)
(*                                                                        *)
(* NOT derivable from [isMemType], whose only laws about [mset] are        *)
(* [mget]-observations: a [memType] could carry a timestamp bumped by      *)
(* every [mset] and satisfy all of them.  For the concrete [coremem] it    *)
(* holds, but only via functional extensionality (equality of a record of  *)
(* dependent functions).  Proved here rather than in pwhile.v so the core  *)
(* files stay untouched.  Only [erhl_nmodL] / [erhl_nmodR] use it.         *)
Lemma hupd_id (F : IhbType.type -> Type)
    (f : forall U : IhbType.type, ident -> F U) (T : IhbType.type) (x : ident) :
  @hupd F f T x (f T x) = f.
Proof.
apply: functional_extensionality_dep => U; apply/funext => y.
case: (pselect (T = U)) => [eq|nT]; last by rewrite hupd_net.
case: (eqVneq x y) => [<-|nx]; last by rewrite hupd_nex.
by case: U / eq; rewrite hupd_eq.
Qed.

Lemma mset_get {T : IhbType.type} (m : cmem) (x : vars T) :
  (m.[x <- m.[x]])%M = m.
Proof.
by case: m => m1 m2;
   rewrite /mset /mget /cmem /mset_ /mget_ /= /coremem_set /= hupd_id.
Qed.

(* One-sided updates of a relational memory, in explicit pair form.       *)
Lemma rmset1E {T : IhbType.type} (m : rmem) (x : vars T) (v : T) :
  (m.[~1 x <- v])%M = (((m.1).[x <- v])%M, m.2).
Proof. by rewrite mset_iE. Qed.

Lemma rmset2E {T : IhbType.type} (m : rmem) (x : vars T) (v : T) :
  (m.[~2 x <- v])%M = (m.1, ((m.2).[x <- v])%M).
Proof. by rewrite mset_iE. Qed.

Lemma rmset_get1 {T : IhbType.type} (m : rmem) (x : vars T) :
  (m.[~1 x <- ((m.1).[x])%M])%M = m.
Proof. by rewrite rmset1E mset_get -surjective_pairing. Qed.

Lemma rmset_get2 {T : IhbType.type} (m : rmem) (x : vars T) :
  (m.[~2 x <- ((m.2).[x])%M])%M = m.
Proof. by rewrite rmset2E mset_get -surjective_pairing. Qed.

(* A star-coupling all of whose mass has [None] on the left sees nothing  *)
(* of the post-expectation.  Note this needs no sign condition on [g] --  *)
(* which is what lets [erhl_abort] hold for an arbitrary post.            *)
Lemma espe_rstar_left0 (X : Distr (option cmem)) (g : rcond) :
  espe (dmargin (fun o => (@None cmem, o)) X) (rstar g) = 0%E.
Proof.
rewrite /espe -[RHS](@esum0 R (option cmem * option cmem)%type [set: _]).
apply: eq_esum; case=> [[a|] b] _ /=; last by rewrite /rstar mul0e.
have -> : dmargin (fun o => (@None cmem, o)) X (Some a, b) = 0.
+ rewrite dmarginE dletE_rsum -[RHS](@rsum0 R (option cmem)).
  by apply: eq_rsum => o; rewrite dunit1E xpair_eqE /= mulr0.
by rewrite mule0.
Qed.

Lemma espe_rstar_right0 (X : Distr (option cmem)) (g : rcond) :
  espe (dmargin (fun o => (o, @None cmem)) X) (rstar g) = 0%E.
Proof.
rewrite /espe -[RHS](@esum0 R (option cmem * option cmem)%type [set: _]).
apply: eq_esum; case=> [[a|] [b|]] _; rewrite /rstar /=;
  try by rewrite mul0e.
have -> : dmargin (fun o => (o, @None cmem)) X (Some a, Some b) = 0.
+ rewrite dmarginE dletE_rsum -[RHS](@rsum0 R (option cmem)).
  by apply: eq_rsum => o; rewrite dunit1E xpair_eqE /= andbF mulr0.
by rewrite mule0.
Qed.

(* Transporting an expectation across [dswap].  Needs [0 <= g] because it   *)
(* goes through [eexp_dmargin].                                             *)
Lemma espe_dswap (nu : Distr (option cmem * option cmem)%type) (g : rcond) :
  (forall m, (0 <= g m)%E) ->
  espe (dswap nu) (rstar g) = espe nu (rstar (rswap g)).
Proof.
move=> hg.
have -> : espe (dswap nu) (rstar g)
        = espe nu (rstar g \o (fun xy : option cmem * option cmem => (xy.2, xy.1))).
+ by rewrite /dswap; apply: eexp_dmargin => p; exact: ge0_rstar.
by apply: eexp_eq; case=> [[a|] [b|]]; rewrite /comp /rstar /rswap.
Qed.

(* Off the support the integrand is multiplied by 0, so only its values on *)
(* the support matter.  [eexp_eq] asks for a global [=1].                   *)
Lemma eexp_eq_in {T : choiceType} (mu : Distr T) (F1 F2 : T -> \bar R) :
  {in dinsupp mu, F1 =1 F2} -> espe mu F1 = espe mu F2.
Proof.
move=> h; rewrite /espe; apply: eq_esum => x _.
case/boolP: (x \in dinsupp mu) => [/h -> //|/dinsuppPn ->].
by rewrite !mule0.
Qed.

Lemma le_dfst {A B : choiceType} (nu : Distr (A * B)%type) (p : A * B) :
  nu p <= dfst nu p.1.
Proof.
rewrite dmarginE dletE_rsum.
have -> : nu p = \sum_(z <- [:: p]) (nu z * dunit z.1 p.1).
+ by rewrite big_seq1 dunit_id mulr1.
apply: gerfinseq_rsum => //.
+ by move=> z; rewrite mulr_ge0 ?ge0_mu.
by have := summable_dlet (fun z : (A * B)%type => dunit z.1) nu p.1;
   apply/eq_esummable.
Qed.

Lemma le_dsnd {A B : choiceType} (nu : Distr (A * B)%type) (p : A * B) :
  nu p <= dsnd nu p.2.
Proof.
rewrite dmarginE dletE_rsum.
have -> : nu p = \sum_(x <- [:: p]) (nu x * dunit x.2 p.2).
+ by rewrite big_seq1 dunit_id mulr1.
apply: gerfinseq_rsum => //.
+ by move=> x; rewrite mulr_ge0 ?ge0_mu.
by have := summable_dlet (fun x : (A * B)%type => dunit x.2) nu p.2;
   apply/eq_esummable.
Qed.

(* A star-coupling with [dunit m2] on the right is concentrated on the      *)
(* slice _ x {Some m2}.  This is what makes one-sided judgments unary.      *)
Lemma scoupling_supp2 {A : choiceType} (D : Distr A) (m2 : A)
    (nu : Distr (option A * option A)%type) :
  scoupling D (dunit m2) nu -> forall p, p \in dinsupp nu -> p.2 = Some m2.
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
Lemma scoupling_dmargin (d1 d2 : Distr cmem)
    (nu : Distr (option cmem * option cmem)%type) (k1 k2 : cmem -> cmem) :
  scoupling d1 d2 nu ->
  scoupling (dmargin k1 d1) (dmargin k2 d2)
            (dmargin (fun p => (omap k1 p.1, omap k2 p.2)) nu).
Proof.
case=> h1 h2; split; rewrite dmargin_comp /comp.
+ have -> : (fun p : option cmem * option cmem => (omap k1 p.1, omap k2 p.2).1)
          = omap k1 \o fst by [].
  by rewrite -dmargin_comp h1 dstar_dmargin.
have -> : (fun p : option cmem * option cmem => (omap k1 p.1, omap k2 p.2).2)
        = omap k2 \o snd by [].
by rewrite -dmargin_comp h2 dstar_dmargin.
Qed.

Lemma espe_dmargin_rstar (nu : Distr (option cmem * option cmem)%type)
    (k1 k2 : cmem -> cmem) (g : rcond) :
  (forall m, (0 <= g m)%E) ->
  espe (dmargin (fun p => (omap k1 p.1, omap k2 p.2)) nu) (rstar g)
  = espe nu (rstar (fun m' : rmem => g (k1 m'.1, k2 m'.2))).
Proof.
move=> hg.
have -> : espe (dmargin (fun p => (omap k1 p.1, omap k2 p.2)) nu) (rstar g)
        = espe nu (rstar g \o (fun p => (omap k1 p.1, omap k2 p.2))).
+ by apply: eexp_dmargin => p; exact: ge0_rstar.
by apply: eexp_eq; case=> [[a|] [b|]]; rewrite /comp /rstar.
Qed.

(* Star-couplings are full distributions. *)
Lemma dweight_scoupling (d1 d2 : Distr cmem)
    (nu : Distr (option cmem * option cmem)%type) :
  scoupling d1 d2 nu -> dweight nu = 1.
Proof.
case=> h1 _; have := dweight_dstar d1; rewrite -h1 (pr_dmargin predT fst nu).
by rewrite (eq_pr (B := predT)).
Qed.

Lemma espe_indic {T : choiceType} (mu : Distr T) (E : pred T) :
  espe mu (fun x => ((E x)%:R)%:E) = (\P_[mu] E)%:E.
Proof. by rewrite prE; apply: eq_esum => x _; rewrite EFinM. Qed.

(* [rstar] is additive, and so is [espe] on non-negative integrands. *)
Lemma espe_rstarD (nu : Distr (option cmem * option cmem)%type)
    (A B : rcond) :
  (forall m, (0 <= A m)%E) -> (forall m, (0 <= B m)%E) ->
  espe nu (rstar (fun m => (A m + B m)%E))
  = (espe nu (rstar A) + espe nu (rstar B))%E.
Proof.
move=> hA hB; rewrite /espe -esumD.
+ by move=> p _; apply: mule_ge0; [apply: ge0_rstar; exact: hA
                                 | rewrite lee_fin ge0_mu].
+ by move=> p _; apply: mule_ge0; [apply: ge0_rstar; exact: hB
                                 | rewrite lee_fin ge0_mu].
apply: eq_esum; case=> [[a|] [b|]] _; rewrite /rstar /=;
  try by rewrite mul0e adde0.
have hAb : (0 <= A (a, b))%E by exact: hA.
have hBb : (0 <= B (a, b))%E by exact: hB.
by rewrite (ge0_muleDl _ hAb hBb).
Qed.

(* ==================================================================== *)
(* Validity                                                              *)
(* ==================================================================== *)
Section Validity.

Definition psi := ident -> (@cmd_ ident cmem ident).

Implicit Types (f g : rcond) (c d : cmd) (ps : psi).

(* Definition 4.1: validity witnessed by a star-coupling. *)
Definition erhl_ ps f c d g :=
  forall m : rmem, exists2 nu,
      scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
    & (espe nu (rstar g) <= f m)%E.

(* Generic (Z-free) judgment: the post may read the initial memories. *)
Definition kerhl_ ps f c d (g : rcond2) :=
  forall m : rmem, exists2 nu,
      scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
    & (espe nu (rstar (g m)) <= f m)%E.

(* Lemma 4.2: the same, phrased with the infimum [psi#]. *)
Definition scouplings (d1 d2 : Distr cmem) :
    set (Distr (option cmem * option cmem)%type) :=
  [set nu | scoupling d1 d2 nu].

Definition psharp g (d1 d2 : Distr cmem) : \bar pwhile.R :=
  ereal_inf [set espe nu (rstar g) | nu in scouplings d1 d2].

Definition ierhl_ ps f c d g :=
  forall m : rmem, (psharp g (ssem_ ps c m.1) (ssem_ ps d m.2) <= f m)%E.

(* -------------------------------------------------------------------- *)
Lemma erhl_kerhl ps f c d g : kerhl_ ps f c d (fun _ => g) <-> erhl_ ps f c d g.
Proof. by split=> h m; case: (h m) => nu ??; exists nu. Qed.

Lemma kerhl_erhl ps f c d (g : rcond2) :
  kerhl_ ps f c d g <-> (forall s0, erhl_ ps (bound f s0) c d (g s0)).
Proof.
rewrite /bound; split.
+ move=> h s0 m; case: (h m) => nu hnu hle; exists nu => //.
  by case: ifP => [/eqP <-|_]; [exact: hle | exact: leey].
+ move=> h m; case: (h m m) => nu hnu; rewrite eqxx => hle.
  by exists nu.
Qed.

(* Lemma 4.2.                                                            *)
(*                                                                       *)
(* [->] is immediate: [psharp] is by definition a lower bound of the set  *)
(* it is the infimum of, so [ereal_inf_lbound] (analysis/ereal.v) and     *)
(* transitivity suffice.  Beware the renamings in this version of         *)
(* mathcomp-analysis: [ereal_inf_lb] is now [ereal_inf_lbound],           *)
(* [lb_ereal_inf] is [le_ereal_inf_tmp] (its alias is commented out), and *)
(* [ereal_inf_le] is [ge_ereal_inf].                                      *)
(*                                                                       *)
(* [<-] is a different matter: it *is* the statement that the infimum is  *)
(* attained, i.e. an optimal-transport existence theorem.  Compare        *)
(* [ereal_inf_leP] (analysis/ereal.v), which takes [S (ereal_inf S)] as   *)
(* an explicit hypothesis -- the library too treats attainment as the     *)
(* missing input.  Contrary to what an earlier version of this comment    *)
(* claimed, strassen/strassen.v cannot simply be invoked here.  Four      *)
(* independent obstacles:                                                 *)
(*                                                                       *)
(* (1) The [R] parameter.  strassen/elift.v declares its own              *)
(*     [Parameter R : realType], which strassen.v inherits, and pwhile.v  *)
(*     declares a second one.  No file under strassen/ requires           *)
(*     xhl.pwhile, and a [Parameter] cannot be instantiated after the     *)
(*     fact, so every strassen result is about a *different* [{distr _ /  *)
(*     _}].  Reuse means first making elift.v/strassen.v R-polymorphic,   *)
(*     i.e. [Context {R : realType}] in place of the [Parameter].         *)
(*                                                                       *)
(* (2) Countability.  [strcvg] / [strcvg2] (strassen.v) -- the Cantor     *)
(*     diagonal extraction of a pointwise-convergent subsequence, which   *)
(*     is the compactness one would want -- require a [countType].        *)
(*     [cmem] is not one and cannot be: [coremem] is                      *)
(*     [forall T : IhbType.type, ident -> T] (pwhile.v), a dependent      *)
(*     function type, and it carries only [gen_choiceMixin].  The way     *)
(*     round is to work inside [dinsupp (dstar d1) * dinsupp (dstar d2)], *)
(*     in which every competitor is supported; but "summable => countable *)
(*     support" is not available in mathcomp-analysis either.             *)
(*                                                                       *)
(* (3) No Fatou / lower semicontinuity for [esum].  [esum_dlim_r]         *)
(*     (analysis/probability_theory/counting_distr.v) has exactly the     *)
(*     right shape -- [espe (dlim f) E <= r] out of                       *)
(*     [forall n, espe (f n) E <= r] -- but is gated on [nd f], and a     *)
(*     minimising sequence is not monotone.  [prhl.iscoupling_dlim] is    *)
(*     restricted the same way ([nu n <=1 nu m]), so passing the          *)
(*     marginals to a merely convergent limit needs dominated             *)
(*     convergence; cf. the [DCT_swap] argument in strassen.v.            *)
(*                                                                       *)
(* (4) strassen.v is not axiom-free anyway: it assumes [Axiom DCT].       *)
(*                                                                       *)
(* Positivity.  As stated, this lemma puts no sign condition on [g].      *)
(* But [esum] is a signed Jordan-decomposition difference                 *)
(* (analysis/esum.v) and every lemma the [<-] direction needs             *)
(* ([ge0_esum], [esum_ge], [esum_dlim_r], [eexp_dlet]) assumes [0 <= f].  *)
(* So the statement will very likely have to gain                         *)
(* [forall m, (0 <= g m)%E], together with a matching side condition on   *)
(* [H_Consequence] / [H_adapt] in erhl.v -- the way ehl.v carries         *)
(* [forall m, 0 <= g m] on [H_Seq] / [H_While] / [H_Block].               *)
(*                                                                       *)
(* Escape hatch.  [<-] is only ever used to prove soundness of            *)
(* [H_Consequence] / [H_adapt], the sole clients of [psharp].  Restating  *)
(* those two rules with the *existential* side condition that ehl.v's     *)
(* [H_adapt] already uses removes the need for [<-] entirely, leaving     *)
(* only the easy, provable [->] direction.                                *)
(* The easy half, as a standalone lemma. *)
Lemma psharp_lbound (D1 D2 : Distr cmem) (g : rcond)
    (nu : Distr (option cmem * option cmem)%type) :
  scoupling D1 D2 nu -> (psharp g D1 D2 <= espe nu (rstar g))%E.
Proof. by move=> h; apply: ereal_inf_lbound; exists nu. Qed.

(* --------------------------------------------------------------------- *)
(* THE single analytic fact this development assumes: the infimum over     *)
(* star-couplings is ATTAINED.  Everything else about Lemma 4.2 -- and     *)
(* hence [erhl_conseq] / [kerhl_conseq] -- is derived from it below, so    *)
(* this is the only hole left by the [Conseq] rules.                       *)
(* The non-negativity hypothesis is NOT cosmetic: [esum] on a signed family *)
(* is a Jordan difference [pos_esum f^+ - pos_esum f^-], and for a [g]      *)
(* unbounded below the infimum need not be attained (nor even meaningful    *)
(* when both parts diverge).  For [0 <= g] the objective is lower           *)
(* semicontinuous and the standard compactness argument applies.            *)
Lemma psharp_attained (D1 D2 : Distr cmem) (g : rcond) :
  (forall m, (0 <= g m)%E) ->
  exists2 nu, scoupling D1 D2 nu & espe nu (rstar g) = psharp g D1 D2.
Proof. Admitted.
(* --------------------------------------------------------------------- *)

(* The [->] half of Lemma 4.2 needs no hypothesis. *)
Lemma erhl_ierhl_ptL (D1 D2 : Distr cmem) (g : rcond) (r : \bar pwhile.R) :
  (exists2 nu, scoupling D1 D2 nu & (espe nu (rstar g) <= r)%E) ->
  (psharp g D1 D2 <= r)%E.
Proof.
by case=> nu hnu hle; apply: (le_trans _ hle); exact: psharp_lbound.
Qed.

(* Lemma 4.2, pointwise in the pair of output distributions. *)
Lemma erhl_ierhl_pt (D1 D2 : Distr cmem) (g : rcond) (r : \bar pwhile.R) :
  (forall m, (0 <= g m)%E) ->
  ((exists2 nu, scoupling D1 D2 nu & (espe nu (rstar g) <= r)%E)
   <-> (psharp g D1 D2 <= r)%E).
Proof.
move=> hg; split=> [h|h]; first exact: erhl_ierhl_ptL.
have [nu hnu heq] := psharp_attained D1 D2 g hg.
by exists nu => //; rewrite heq.
Qed.

Lemma erhl_ierhl ps f c d g :
  (forall m, (0 <= g m)%E) -> (erhl_ ps f c d g <-> ierhl_ ps f c d g).
Proof.
by move=> hg; split=> h m; apply/(erhl_ierhl_pt _ _ _ _ hg); exact: h.
Qed.

(* --------------------------------------------------------------------- *)
(* The second (and last) analytic fact assumed: a bound on [psharp] that   *)
(* holds at every stage of a monotone approximation survives the limit.    *)
(* This is what the paper calls "the sequence of star-couplings converges, *)
(* in a certain sense, to a star-coupling"; it is the exact analogue of    *)
(* [esum_dlim_r], which does the same job for the unary logic [ehl].       *)
(*                                                                        *)
(* Note it cannot be proved by exhibiting a monotone family of             *)
(* star-couplings: they all have weight 1 (see [dweight_scoupling]), so a   *)
(* nondecreasing family is constant.  Used by [erhl_while] and             *)
(* [recursive_proc].                                                       *)
Lemma psharp_dlim (mu1 mu2 : nat -> Distr cmem) (g : rcond)
    (r : \bar pwhile.R) :
  (forall n p, (n <= p)%N -> mu1 n <=1 mu1 p) ->
  (forall n p, (n <= p)%N -> mu2 n <=1 mu2 p) ->
  (forall m, (0 <= g m)%E) ->
  (forall n, (psharp g (mu1 n) (mu2 n) <= r)%E) ->
  (psharp g (dlim mu1) (dlim mu2) <= r)%E.
Proof. Admitted.
(* --------------------------------------------------------------------- *)

End Validity.

(* ==================================================================== *)
(* Relational procedure contracts                                        *)
(*                                                                      *)
(* A contract relates a *pair* of procedures; one-sided calls relate a   *)
(* procedure to [skip].  Indexing by [option ident] covers both, with    *)
(* [None] standing for [skip].                                          *)
(* ==================================================================== *)
Section RContract.

Definition ocmd (o : option ident) : cmd :=
  if o is Some f then call f else skip.

Definition obody (ps : psi) (o : option ident) : cmd :=
  if o is Some f then ps f else skip.

Definition rclause : Type := rcond * rcond2.

Definition get_pre (an : rclause) := let: (pre, _) := an in pre.
Definition get_post (an : rclause) := let: (_, post) := an in post.

Definition rphi : Type := option ident -> option ident -> rclause.

(** Empty procedure contract **)

Definition empty_rprecondition  : rcond  := (fun _ => +oo)%E.
Definition empty_rpostcondition : rcond2 := (fun _ _ => 0)%E.

Definition empty_rclause : rclause :=
  (empty_rprecondition, empty_rpostcondition).

Definition rcl_empty : rphi := fun _ _ => empty_rclause.

(** Well-formedness of contracts.  Note that [ehl_stmt]'s [post_mono]    *)
(*  and [cond2_independent] are not needed here: [rcond2] carries no     *)
(*  distribution argument, so independence holds by construction.        *)

Definition rcl_pre_pos (cl : rphi) :=
  forall o1 o2 m, (0 <= get_pre (cl o1 o2) m)%E.

Definition rcl_post_pos (cl : rphi) :=
  forall o1 o2 m0 m, (0 <= get_post (cl o1 o2) m0 m)%E.

(* The [(None, None)] clause of a contract relates [skip] to [skip], so it  *)
(* never degenerates to [dnull] and the induction in [recursive_proc] has   *)
(* no base case for it: it must be assumed.  A trivial obligation, and that *)
(* instance of [H_call] is subsumed by [H_Skip] anyway.                     *)
Definition rcl_skip_valid (cl : rphi) :=
  forall s : rmem, (get_post (cl None None) s s <= get_pre (cl None None) s)%E.

End RContract.

HB.mixin Record isRPhi (cl : rphi) := {
  rpre_pos  : rcl_pre_pos  cl;
  rpost_pos : rcl_post_pos cl;
}.

HB.structure Definition RPhi := {f of isRPhi f}.

Lemma rpre_pos_rcl_empty : rcl_pre_pos rcl_empty.
Proof. by move=> ???; exact: leey. Qed.

Lemma rpost_pos_rcl_empty : rcl_post_pos rcl_empty.
Proof. by []. Qed.

HB.instance Definition _ :=
  isRPhi.Build rcl_empty rpre_pos_rcl_empty rpost_pos_rcl_empty.
