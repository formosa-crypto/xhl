(* -------------------------------------------------------------------- *)
(* ----------------- *) Require Import Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum counting_distr.
From xhl.pwhile         Require Import notations inhabited pwhile psemantic passn range.
                        Require Import phl.
From xhl                Require Import misc.
(* [Require] without [Import]: prhl.v defines its own [psi], [derivable]  *)
(* and [soundness], and hl/hl.v its own [derivable], [derivable2],        *)
(* [soundness], [assn2], [clause], [phi], [get_pre], [get_post], all of   *)
(* which would shadow phl.v's.  Accessed qualified, as erhl/erhl.v does.  *)
From xhl.prhl           Require prhl.
From xhl.hl             Require hl.

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
Implicit Types P Q S I : assn.
Implicit Types c       : cmd.
Implicit Types d       : R.
Implicit Types ps     : ident -> (@cmd_ ident cmem ident).
Implicit Types r      : bd.

(* ==================================================================== *)
(*                                                                      *)
(*   The rules of EasyCrypt's probabilistic Hoare logic (pHL/phoare)    *)
(*                                                                      *)
(*   This file states, as Coq lemmas over [phl_] of phl.v, every rule   *)
(*   of the catalogue in RULES-PHL.md.  Each lemma carries the number   *)
(*   of the section of that document which it formalizes.              *)
(*                                                                      *)
(*   *** All the lemmas of this file are [Admitted]. ***                *)
(*   This pass states the rules only, so that the statements can be     *)
(*   checked against the catalogue before any proof effort.  A later    *)
(*   pass discharges them.  Proof sketches are given in the comments.   *)
(*                                                                      *)
(* -------------------------------------------------------------------- *)
(*   GLOBAL CORRESPONDENCES between EasyCrypt and this formalization.    *)
(*   Referred to below as (G1)..(G5).                                    *)
(*                                                                      *)
(*   (G1) The bound.  EasyCrypt's [bd] is an [ss_inv], i.e. a formula    *)
(*        over the judgement's memory.  Here [d : R] is a *constant*.    *)
(*        Consequently every EasyCrypt premise of the shape             *)
(*        [forall &m, P => ...b...] collapses to a plain side condition  *)
(*        on reals, and the side conditions that exist only to keep the  *)
(*        bound stable become vacuous: [condnm] (S1.2),                 *)
(*        [is_bd_indep]/[pre_bound] (S1.6) and [check_form_indep]        *)
(*        (S5.2).                                                       *)
(*                                                                      *)
(*   (G2) Statements vs procedures.  EasyCrypt has two judgement forms,  *)
(*        [bdHoareS] (a statement) and [bdHoareF] (a procedure).  Here   *)
(*        [call f] is a command, so the procedure form is the statement  *)
(*        form at [c := call f].  No rule is duplicated.                *)
(*                                                                      *)
(*   (G3) Calls with arguments and results.  EasyCrypt's                 *)
(*        [lv <@ f(args)] is [Block bs Do (call f) Return rs] here:      *)
(*        [minit m bs] opens a fresh local frame and binds the formals   *)
(*        to the actuals evaluated in the caller, [mret m m' rs]         *)
(*        restores the caller's local store and assigns the results      *)
(*        from expressions evaluated in the callee's final memory.       *)
(*        Because the rules below quantify over the callee's *whole*     *)
(*        final memory, EasyCrypt's [forall mod(f)] is not needed.       *)
(*                                                                      *)
(*   (G4) Hoare premises.  Several pHL rules have [hoare[c : P ==> Q]]   *)
(*        premises.  By S3.1 that judgement is exactly                   *)
(*        [phl_ ps P c (~ Q) '= 0], which is the [hoare] notation below; *)
(*        by [pr_range] (pwhile/range.v) it is also exactly              *)
(*        [hl_ ps P c Q] of hl/hl_stmt.v.                               *)
(*                                                                      *)
(*   (G5) Modified variables.  EasyCrypt's [forall mod(c)] is            *)
(*        [hl.eqon (predC (hl.mod c))].  Three limits, see S2.3:         *)
(*        [hl.mod_spec] requires [nocall c]; [hl.mod (call n) = pred0];  *)
(*        and [hl.mod]/[hl.eqon] see the *local* store only, so global   *)
(*        assignments are outside their reach.                          *)
(*                                                                      *)
(* ==================================================================== *)

Section ec_phl.

(* -------------------------------------------------------------------- *)
(* S0.2  The opposite comparison, EasyCrypt's [hoarecmp_opp].            *)
(*   <=^op = >=,  >=^op = <=,  =^op = =.                                 *)
(* Used by the bound-splitting rules of S3.4 and S3.5.                   *)

Definition bd_opp (r : bd) : bd :=
  match r with
  | Le => Ge
  | Ge => Le
  | Eq => Eq
  end.

(* -------------------------------------------------------------------- *)
(* Sanity property of [bd_opp]: it swaps the two sides of the relation.  *)
(* Proof: [by case: r].                                                  *)

Lemma rel_of_bd_opp (r : bd) (x y : R) : bd_opp r x y = r y x.
Proof. Admitted.

Section Rules.
Context ps.

Notation phl := (phl_ ps).

(* [hoare P c Q] is EasyCrypt's [hoare[ c : P ==> Q ]] -- see (G4).      *)
Notation hoare P c Q := (phl_ ps P%A c%S (~ Q)%A '= 0).


(* ==================================================================== *)
(* ===                     1. The core pHL rules                    === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* S1.1  skip.                                                           *)
(*                                                                      *)
(*     forall &m, P => (1 <> b)      forall &m, P => Q                   *)
(*   ---------------------------------------------------                *)
(*            |- phoare[ [] : P ==> Q ] <> b                             *)
(*                                                                      *)
(* By (G1) the first premise of the catalogue is the plain [r 1 d].      *)
(* Proof: [phl_skip] gives [phl P skip P '= 1]; conclude with            *)
(* [phl_conseq_*] on [Q] and the bound.                                  *)

Lemma ec_skip P Q r d :
  (forall m, P m -> Q m) -> r 1 d -> phl P skip Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.2  seq (app) -- the four-bound rule.                               *)
(*                                                                      *)
(* [S] is the catalogue's case predicate [R] (renamed: [R] is the        *)
(* realType here).  [Phi] is the catalogue's auxiliary assertion [phi].  *)
(* The catalogue's [condnm] premise is vacuous by (G1).                  *)
(*                                                                      *)
(* Proof of [ec_seq_eq]: [phl_seq_eq] of phl.v, after weakening the two  *)
(* second-phase judgements with [phl_conseq_eq] using [Phi].             *)

Lemma ec_seq_eq (Phi S P Q : assn) c1 c2 f1 f2 g1 g2 d :
     d = f1 * f2 + g1 * g2
  -> hoare P c1 Phi
  -> phl P c1 S           '= f1
  -> phl (Phi /\ S)%A c2 Q      '= f2
  -> phl P c1 (~ S)%A     '= g1
  -> phl (Phi /\ ~ S)%A c2 Q    '= g2
  -> phl P (c1 ;; c2) Q '= d.
Proof. Admitted.

(* At [<=] no positivity is needed: the two products are bounded by      *)
(* [ler_pM], whose non-negativity side conditions are supplied by        *)
(* [ge0_pr] on the left-hand factors.                                    *)

Lemma ec_seq_le (Phi S P Q : assn) c1 c2 f1 f2 g1 g2 d :
     f1 * f2 + g1 * g2 <= d
  -> hoare P c1 Phi
  -> phl P c1 S           '<= f1
  -> phl (Phi /\ S)%A c2 Q      '<= f2
  -> phl P c1 (~ S)%A     '<= g1
  -> phl (Phi /\ ~ S)%A c2 Q    '<= g2
  -> phl P (c1 ;; c2) Q '<= d.
Proof. Admitted.

(* At [>=] the four non-negativity hypotheses ARE load-bearing: a        *)
(* product of lower bounds bounds the product from below only when the   *)
(* bounds are non-negative.  Without them the statement is false         *)
(* (take [f1 = f2 = -1]).                                                *)

Lemma ec_seq_ge (Phi S P Q : assn) c1 c2 f1 f2 g1 g2 d :
     0 <= f1 -> 0 <= f2 -> 0 <= g1 -> 0 <= g2
  -> d <= f1 * f2 + g1 * g2
  -> hoare P c1 Phi
  -> phl P c1 S           '>= f1
  -> phl (Phi /\ S)%A c2 Q      '>= f2
  -> phl P c1 (~ S)%A     '>= g1
  -> phl (Phi /\ ~ S)%A c2 Q    '>= g2
  -> phl P (c1 ;; c2) Q '>= d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.3  if.                                                             *)
(*                                                                      *)
(*   |- phoare[ s1; tl : P /\ e ==> Q ] <> b                             *)
(*   |- phoare[ s2; tl : P /\ ~e ==> Q ] <> b                            *)
(*   ------------------------------------------------------             *)
(*   |- phoare[ if e then s1 else s2; tl : P ==> Q ] <> b                *)
(*                                                                      *)
(* Both branches keep the *same* bound: the rule is a precondition       *)
(* case-split, sound at a fixed bound because the two preconditions are  *)
(* exclusive and exhaustive.                                             *)
(*                                                                      *)
(* Without a tail this is already phl.v's                                *)
(*   Lemma phl_if P (e : bexpr) c1 c2 Q r d :                            *)
(*        phl (P /\   `[{e}]) c1 Q r d                                   *)
(*     -> phl (P /\ ~ `[{e}]) c2 Q r d                                   *)
(*     -> phl P (If e then c1 else c2) Q r d.                            *)
(* The catalogue's rule carries the tail [tl], so the version with a     *)
(* tail is stated here.  Proof: [if_seq] (psemantic.v:683) turns         *)
(* [(If e then c1 else c2) ;; tl] into                                   *)
(* [If e then (c1 ;; tl) else (c2 ;; tl)], then [phl_if].                *)

Lemma ec_cond P Q (e : bexpr) c1 c2 tl r d :
     phl (P /\   `[{e}])%A (c1 ;; tl) Q r d
  -> phl (P /\ ~ `[{e}])%A (c2 ;; tl) Q r d
  -> phl P ((If e then c1 else c2) ;; tl) Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.4  match -- NOT FORMALIZED.                                        *)
(* [cmd_] (pwhile/pwhile.v:276) has no [match] constructor and the       *)
(* language has no datatypes, so there is no goal of this shape.         *)

(* -------------------------------------------------------------------- *)
(* S1.5  rcondt / rcondf.                                                *)
(*                                                                      *)
(*   |- hoare[ hd : P ==> e_b ]    |- phoare[ hd; s_b; tl : P ==> Q ] <> b *)
(*   ------------------------------------------------------------------- *)
(*     |- phoare[ hd; if e then s1 else s2; tl : P ==> Q ] <> b           *)
(*                                                                      *)
(* The first premise is a Hoare goal, not a pHL one -- see (G4).         *)
(* Proof: [ec_eq] (S5) with [ssem_seqE] and [ssem_ifE]: on the support   *)
(* of [ssem_ ps hd m] the guard is determined, so [eq_in_dlet] rewrites  *)
(* the conditional away.                                                 *)

Lemma ec_rcondt P Q (e : bexpr) hd c1 c2 tl r d :
     hoare P hd `[{e}]
  -> phl P (hd ;; (c1 ;; tl)) Q r d
  -> phl P (hd ;; ((If e then c1 else c2) ;; tl)) Q r d.
Proof. Admitted.

Lemma ec_rcondf P Q (e : bexpr) hd c1 c2 tl r d :
     hoare P hd (~ `[{e}])%A
  -> phl P (hd ;; (c2 ;; tl)) Q r d
  -> phl P (hd ;; ((If e then c1 else c2) ;; tl)) Q r d.
Proof. Admitted.


(* -------------------------------------------------------------------- *)
(* S1.6  rnd, five shapes.                                               *)
(*                                                                      *)
(* Throughout, the statement ends with [x <$- e] and [s] is the prefix.   *)
(* [E : pred T] is the catalogue's *event*, a predicate on the sampled   *)
(* value; [mu d E] is [\P_[`[{e}] m] E].  By (G1) the catalogue's        *)
(* [pre_bound] is [true] and [bound] is [d], so the generalisation over  *)
(* a fresh [bd] variable disappears.                                     *)
(*                                                                      *)
(* !! ORIENTATION OF [mk_event_cond] -- PLEASE CHECK AGAINST EASYCRYPT.  *)
(* RULES-PHL.md S1.6 tabulates it as                                     *)
(*      <=  :  forall v, E v -> v \in supp d -> Q[v/lv]                  *)
(*      >=  :  forall v, Q[v/lv] -> v \in supp d -> E v                  *)
(*      =   :  forall v, v \in supp d -> (E v <-> Q[v/lv])               *)
(* The two one-sided rows are stated below in the OPPOSITE direction,    *)
(* because as tabulated they do not give the rule.  At [<=] one needs    *)
(* [\P_[e] (Q[.]) <= \P_[e] E <= d], hence [Q[v] -> E v]; the tabulated  *)
(* [E v -> Q[v]] yields [\P_[e] E <= \P_[e] (Q[.])], the wrong way.      *)
(* Dually at [>=].  The [=] row agrees with the catalogue and is         *)
(* unchanged, which is evidence that the two one-sided rows of the       *)
(* table are transposed.  The default event [E := fun v => Q[v/lv]]      *)
(* makes both readings coincide, which is why this is invisible unless   *)
(* [E] is supplied explicitly (shapes (c) and (d)).                      *)

(* (a) [rnd], [<=], post independent of the assigned variable: the       *)
(* sampling is simply dropped.                                           *)
(* Proof: [ssem_seqE]/[ssem_rndE], then [pr_dlet]; the inner probability *)
(* is [Q m' * weight (`[{e}] m')] <= [Q m'] by [le1_pr].                 *)

Lemma ec_rnd_le_indep {T : IhbType.type} P Q (x : vars T) (e : dexpr T) s d :
     (forall (m : cmem) (v : T), Q m.[x <- v] = Q m)
  -> phl P s Q '<= d
  -> phl P (s ;; (x <$- e)) Q '<= d.
Proof. Admitted.

(* (b) [rnd], [>=], post independent: a losslessness condition on the    *)
(* sampled distribution is folded into the postcondition.                *)
(*                                                                      *)
(* The catalogue states this shape for [<> in {=, >=}].  Only [>=] is    *)
(* stated here: the [=] instance appears to be unsound as written.       *)
(* Counterexample -- let [s] put mass 1/2 on [m1] and 1/2 on [m2], with  *)
(* [Q m1], [Q m2], [weight (e m1) = 1] and [weight (e m2) = 1/2].  Then  *)
(* the premise holds at [d = 1/2] (only [m1] satisfies [Q /\ ll]) while  *)
(* the conclusion evaluates to [1/2*1 + 1/2*1/2 = 3/4 <> 1/2].  Please   *)
(* check the [=] instance against EasyCrypt before adding it.            *)

Lemma ec_rnd_ge_indep {T : IhbType.type} P Q (x : vars T) (e : dexpr T) s d :
     (forall (m : cmem) (v : T), Q m.[x <- v] = Q m)
  -> phl P s [pred m | Q m && (\P_[`[{e}] m] predT == 1)] '>= d
  -> phl P (s ;; (x <$- e)) Q '>= d.
Proof. Admitted.

(* (c) [rnd E], [<=].  The residual is a *Hoare* goal -- see (G4).       *)

Lemma ec_rnd_le {T : IhbType.type} P Q (x : vars T) (e : dexpr T) (E : pred T) s d :
     hoare P s [pred m | (\P_[`[{e}] m] E <= d)
                         && `[< forall v : T, v \in dinsupp (`[{e}] m)
                                           -> Q m.[x <- v] -> E v >]]
  -> phl P (s ;; (x <$- e)) Q '<= d.
Proof. Admitted.

(* (d) [rnd E], [>=].  The residual judgement is forced to [= 1] by      *)
(* the catalogue ([ecPhlRnd.ml:262]).                                    *)

Lemma ec_rnd_ge {T : IhbType.type} P Q (x : vars T) (e : dexpr T) (E : pred T) s d :
     phl P s [pred m | (d <= \P_[`[{e}] m] E)
                       && `[< forall v : T, v \in dinsupp (`[{e}] m)
                                         -> E v -> Q m.[x <- v] >]] '= 1
  -> phl P (s ;; (x <$- e)) Q '>= d.
Proof. Admitted.

(* (d') [rnd E], [=].  Here the catalogue's [mk_event_cond] is kept as   *)
(* tabulated: on the support, [E] and [Q[./lv]] must agree.              *)

Lemma ec_rnd_eq {T : IhbType.type} P Q (x : vars T) (e : dexpr T) (E : pred T) s d :
     phl P s [pred m | (\P_[`[{e}] m] E == d)
                       && `[< forall v : T, v \in dinsupp (`[{e}] m)
                                         -> (E v = Q m.[x <- v]) >]] '= 1
  -> phl P (s ;; (x <$- e)) Q '= d.
Proof. Admitted.

(* (e) [rnd phi d1 d2 d3 d4 [E]] -- [PMultRndParams], six premises, in   *)
(* the order EasyCrypt emits them ([bd_sgoal], [sgoal1] .. [sgoal5]).    *)
(* [Phi] is the catalogue's [phi].  The [<>]-oriented event condition is *)
(* written [Ev]; instantiate it per the orientation note above.          *)

Lemma ec_rnd_split {T : IhbType.type} P Q (Phi : assn)
                   (x : vars T) (e : dexpr T) (E : pred T) (Ev : assn) s r
                   d d1 d2 d3 d4 :
     r (d1 * d2 + d3 * d4) d
  -> phl P s Phi        r d1
  -> (forall m, Phi m -> r (\P_[`[{e}] m] E) d2 /\ Ev m)
  -> phl P s (~ Phi)%A  r d3
  -> (forall m, ~~ Phi m -> r (\P_[`[{e}] m] E) d4 /\ Ev m)
  -> (0 <= d1 <= 1) && (0 <= d2 <= 1) && (0 <= d3 <= 1) && (0 <= d4 <= 1)
  -> phl P (s ;; (x <$- e)) Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.7  rndsem -- NOT FORMALIZED.                                       *)
(* [Core.t_bdhoare_rndsem_r] replaces a trailing block of samplings by   *)
(* one *semantic* sampling.  [cmd_] has no semantic-sampling             *)
(* constructor, so the rule has no counterpart here.                     *)


(* -------------------------------------------------------------------- *)
(* S1.8  while -- three rules.                                           *)
(*                                                                      *)
(* The variant is [vrnt : cmem -> int], matching EasyCrypt's use of      *)
(* [vrnt <= 0] as the termination threshold.                            *)
(* phl.v has NO loop rule at all, so all three are new here.             *)

(* (a) Variant rule ([while (inv) (vrnt)], admissible at [<=], [=],      *)
(* [>=]).  The body must be certain ([= 1]) and must strictly decrease   *)
(* the variant.                                                         *)
(*                                                                      *)
(* The catalogue packages the rule with a prefix [s] and a [forall       *)
(* mod(body)] postcondition on that prefix.  Here the loop is stated on  *)
(* its own; the prefix is recovered by composing with [ec_seq_*] (S1.2), *)
(* which is what the [forall mod(body)] packaging exists to emulate.     *)
(*                                                                      *)
(* Proof sketch: [ssem_whileE] then [range]/[pr] on [whilen e c n], by   *)
(* strong induction on [vrnt m]; the body being [= 1] makes each         *)
(* unrolling mass-preserving and [homo_whilen] gives the limit.          *)

Lemma ec_while_variant (I : assn) (vrnt : cmem -> int) (e : bexpr) c :
     (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            (I /\ [pred m | vrnt m < z])%A '= 1)
  -> (forall m, I m -> vrnt m <= 0 -> ~~ `[{e}] m)
  -> phl I (While e Do c) (I /\ ~ `[{e}])%A '= 1.
Proof. Admitted.

(* (b) Reverse rule ([while (inv)]), upper bounds only.                  *)
(*                                                                      *)
(* EasyCrypt introduces an *abstract statement* hypothesis [w] standing  *)
(* for the rest of the loop and asks for one unfolding step.  Here that  *)
(* is a genuine quantification over commands.                           *)
(*                                                                      *)
(* [0 <= d] and the second premise are load-bearing.  They are what      *)
(* EasyCrypt's Hoare premise                                            *)
(*   hoare[ s : P ==> I /\ forall mod(body). (I /\ ~e /\ Q => b = 1) ]   *)
(* reduces to once the bound is a constant (G1): the base case of the    *)
(* unrolling is a memory where the guard is false, and there            *)
(* [\P_[dunit m] Q = (Q m)%:R] must be below [d].                        *)
(*                                                                      *)
(* Proof sketch: [ssem_whileE] + [sum_dlim_r_r]; induct on [n],          *)
(* instantiating the third premise at [w := whilen e c n], and close     *)
(* the unrolling with [phl_if] / [phl_skip] / [phl_abort].               *)

Lemma ec_while_rev (I : assn) Q (e : bexpr) c d :
     0 <= d
  -> (forall m, I m -> ~~ `[{e}] m -> Q m -> 1 <= d)
  -> (forall w : cmd, phl I w Q '<= d -> phl (I /\ `[{e}])%A (c ;; w) Q '<= d)
  -> phl I (While e Do c) Q '<= d.
Proof. Admitted.

(* (c) Reverse rule with a rate ([while (inv) (vrnt) k eps]), lower and  *)
(* exact bounds only.  [eps] is the per-iteration lower bound on the     *)
(* probability that the variant decreases and [k] its upper bound;       *)
(* together they make the loop almost surely terminating at a rate.      *)
(* The catalogue requires the loop to be the whole statement, which is   *)
(* automatic below.                                                      *)
(*                                                                      *)
(* DEVIATION: the catalogue's [pre-bound] and [term-invariant] premises  *)
(* are guarded by [forall mod(body)].  They are stated here over *all*   *)
(* memories, which is a strictly stronger premise and therefore a sound  *)
(* (but less applicable) rule.  Stating them with (G5) would drag in a   *)
(* [nocall c] hypothesis; see S2.3.                                      *)
(*                                                                      *)
(* Premises are in the catalogue's order: pre-invariant, pre-bound,      *)
(* term-invariant, body, out-invariant, vrnt.                            *)

Lemma ec_while_rev_geq P Q (I : assn) (vrnt : cmem -> int) (e : bexpr)
                       c d (k : int) (eps : R) :
     (forall m, P m -> I m)
  -> (forall m, P m -> ~~ `[{e}] m -> ~~ Q m -> d = 0)
  -> (forall m, I m -> (vrnt m <= k) && (vrnt m <= 0 ==> ~~ `[{e}] m))
  -> (forall w : cmd, phl P w Q '>= d -> phl (P /\ `[{e}])%A (c ;; w) Q '>= d)
  -> phl (I /\ `[{e}])%A c I '= 1
  -> (forall m, I m -> 0 < eps)
  -> (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            [pred m | vrnt m < z] '>= eps)
  -> phl P (While e Do c) Q '>= d.
Proof. Admitted.

Lemma ec_while_rev_eq P Q (I : assn) (vrnt : cmem -> int) (e : bexpr)
                      c d (k : int) (eps : R) :
     (forall m, P m -> I m)
  -> (forall m, P m -> ~~ `[{e}] m -> d = (if Q m then 1 else 0))
  -> (forall m, I m -> (vrnt m <= k) && (vrnt m <= 0 ==> ~~ `[{e}] m))
  -> (forall w : cmd, phl P w Q '= d -> phl (P /\ `[{e}])%A (c ;; w) Q '= d)
  -> phl (I /\ `[{e}])%A c I '= 1
  -> (forall m, I m -> 0 < eps)
  -> (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            [pred m | vrnt m < z] '>= eps)
  -> phl P (While e Do c) Q '= d.
Proof. Admitted.


(* -------------------------------------------------------------------- *)
(* S1.9  call.                                                           *)
(*                                                                      *)
(* By (G3), EasyCrypt's [lv <@ f(args)] is                               *)
(*   [Block bs Do (call f) Return rs].                                   *)
(* The rule is reached in three steps.                                   *)

(* Step 1 -- the block rule, missing from phl.v ([hl_block] and          *)
(* [ehl_block] exist).  It is an equality, not an inequality, because    *)
(*   ssem (Block bs Do c Return rs) m                                    *)
(*     = \dlet_(m' <- ssem c (minit m bs)) dunit (mret m m' rs)          *)
(* is a [dmargin], and [pr_dmargin] transports the probability exactly:  *)
(*   \P_[ssem (Block bs Do c Return rs) m] Q                             *)
(*     = \P_[ssem c (minit m bs)] [pred m' | Q (mret m m' rs)].          *)
(* Shape taken from [hl_block] (hl/hl.v:173).                            *)

Lemma ec_block P Q (bs rs : seq (@binding _ cmem)) c r d :
     (forall m, P m ->
        phl [pred m0 | m0 == minit m bs] c [pred m' | Q (mret m m' rs)] r d)
  -> phl P (Block bs Do c Return rs) Q r d.
Proof. Admitted.

(* Step 2 -- the callee spec, oriented by the comparison.  The three     *)
(* orientations are exactly the catalogue's [wp] table                   *)
(* ([ecPhlCall.ml:326-336]): [post => Q'] at [<=], [Q' => post] at       *)
(* [>=], and an equivalence at [=].  No [forall res, forall mod(f)] is   *)
(* needed: the premise quantifies over the callee's whole final memory   *)
(* [m'] (G3).                                                            *)

Lemma ec_call_le P Q (Pf Qf : assn) (f : ident) (bs rs : seq (@binding _ cmem)) d :
     (forall m, P m -> Pf (minit m bs))
  -> (forall m m', P m -> Q (mret m m' rs) -> Qf m')
  -> phl Pf (call f) Qf '<= d
  -> phl P (Block bs Do (call f) Return rs) Q '<= d.
Proof. Admitted.

Lemma ec_call_ge P Q (Pf Qf : assn) (f : ident) (bs rs : seq (@binding _ cmem)) d :
     (forall m, P m -> Pf (minit m bs))
  -> (forall m m', P m -> Qf m' -> Q (mret m m' rs))
  -> phl Pf (call f) Qf '>= d
  -> phl P (Block bs Do (call f) Return rs) Q '>= d.
Proof. Admitted.

Lemma ec_call_eq P Q (Pf Qf : assn) (f : ident) (bs rs : seq (@binding _ cmem)) d :
     (forall m, P m -> Pf (minit m bs))
  -> (forall m m', P m -> Q (mret m m' rs) = Qf m')
  -> phl Pf (call f) Qf '= d
  -> phl P (Block bs Do (call f) Return rs) Q '= d.
Proof. Admitted.

(* Step 3 -- with a prefix [s], reproducing the residual-goal table of   *)
(* S1.9.  EasyCrypt reaches it through [t_bdhoare_seq] at the            *)
(* [PSeqSingle] row of the S1.2 surface table, [(b/b', b', 0, 1)].       *)
(*                                                                      *)
(* NOTE the [hoare] premise: it is the [g1 = 0] component of that seq    *)
(* split -- the prefix must establish the [wp] *almost surely*.  The     *)
(* S1.9 residual table does not display it, because in EasyCrypt it is   *)
(* discharged inside the seq application.  It is load-bearing: without   *)
(* it, memories off the [wp] contribute unconstrained mass and the [=]   *)
(* and [>=] rows fail.                                                   *)
(*                                                                      *)
(* The "no explicit bound" rows of the table are the [d' = d]            *)
(* instances, where [d / d'] is [1].                                     *)

Lemma ec_call_seq_le P Q (Pf Qf : assn) (f : ident)
                     (bs rs : seq (@binding _ cmem)) s d :
     hoare P s [pred m | Pf (minit m bs)
                         && `[< forall m', Q (mret m m' rs) -> Qf m' >]]
  -> phl Pf (call f) Qf '<= d
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q '<= d.
Proof. Admitted.

Lemma ec_call_seq_ge P Q (Pf Qf : assn) (f : ident)
                     (bs rs : seq (@binding _ cmem)) s d d' :
     d' != 0
  -> hoare P s [pred m | Pf (minit m bs)
                         && `[< forall m', Qf m' -> Q (mret m m' rs) >]]
  -> phl P s [pred m | Pf (minit m bs)
                       && `[< forall m', Qf m' -> Q (mret m m' rs) >]] '>= (d / d')
  -> phl Pf (call f) Qf '>= d'
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q '>= d.
Proof. Admitted.

Lemma ec_call_seq_eq P Q (Pf Qf : assn) (f : ident)
                     (bs rs : seq (@binding _ cmem)) s d d' :
     d' != 0
  -> hoare P s [pred m | Pf (minit m bs)
                         && `[< forall m', Q (mret m m' rs) = Qf m' >]]
  -> phl P s [pred m | Pf (minit m bs)
                       && `[< forall m', Q (mret m m' rs) = Qf m' >]] '= (d / d')
  -> phl Pf (call f) Qf '= d'
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q '= d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.10 / S1.12  proc, and fun-to-code.                                 *)
(*                                                                      *)
(*   |- phoare[ body(f) : P ==> Q ] <> b                                 *)
(*   ------------------------------------                                *)
(*        |- phoare[ f : P ==> Q ] <> b                                  *)
(*                                                                      *)
(* EasyCrypt substitutes the arguments for the parameters; by (G3) that  *)
(* substitution is the [Block] of S1.9, so the rule proper is just the   *)
(* unfolding of the call.  Both S1.10 and S1.12 collapse to this.        *)
(* Proof: [ssem_call_eq] (psemantic.v:1019).                             *)

Lemma ec_proc P Q (f : ident) r d :
  phl P (ps f) Q r d <-> phl P (call f) Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.11  proc * (abstract procedures) -- NOT FORMALIZED.                *)
(* [t_bdhoareF_abs_ge_r] quantifies over the oracle set [O] of an        *)
(* abstract module [f] and checks [PV.check_depend] / [check_oracle_use] *)
(* against [f]'s top-level module state.  There is no module system and  *)
(* no notion of an abstract procedure with an oracle set here, so the    *)
(* rule cannot be stated.                                                *)

(* -------------------------------------------------------------------- *)
(* S1.13  elim* and exists* -- quantifiers in the precondition.          *)
(*                                                                      *)
(*   |- forall x, phoare[ c : P' ==> Q ] <> b                            *)
(*   -----------------------------------------                           *)
(*   |- phoare[ c : exists x, P' ==> Q ] <> b                            *)

Lemma ec_exists_elim {T : Type} (P : T -> assn) Q c r d :
     (forall t : T, phl (P t) c Q r d)
  -> phl [pred m | `[< exists t : T, P t m >]] c Q r d.
Proof. Admitted.

(* The converse, EasyCrypt's [exists* f]: the value of [f] is named by a *)
(* fresh existential in the precondition.                                *)

Lemma ec_exists_intro {T : eqType} (f : cmem -> T) P Q c r d :
     phl [pred m | `[< exists t : T, (t == f m) && P m >]] c Q r d
  -> phl P c Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.14  ecall -- apply a procedure contract given as a lemma.          *)
(*                                                                      *)
(* Backward direction only, and the contract must be lossless ([= 1]);   *)
(* the goal's own bound must satisfy [1 <> b], which is the [condbd]     *)
(* premise of the underlying seq split.                                  *)
(* Derived, exactly as EasyCrypt derives it: [ec_seq_eq] at the trivial  *)
(* split ([S := predT], [f1 = f2 = 1], [g1 = g2 = 0]) composed with      *)
(* [ec_call_eq] against the contract.                                    *)

Lemma ec_ecall P Q (Pf Qf : assn) (f : ident)
               (bs rs : seq (@binding _ cmem)) s r d :
     r 1 d
  -> phl Pf (call f) Qf '= 1
  -> phl P s [pred m | Pf (minit m bs)
                       && `[< forall m', Qf m' -> Q (mret m m' rs) >]] '= 1
  -> phl P (s ;; (Block bs Do (call f) Return rs)) Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.15  case.  Sound -- unlike a *postcondition* split -- because both *)
(* branches keep the same bound and the preconditions are exclusive.     *)

Lemma ec_case P (Phi : assn) c Q r d :
     phl (P /\ Phi)%A   c Q r d
  -> phl (P /\ ~ Phi)%A c Q r d
  -> phl P c Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S1.16  exfalso -- the [false] precondition axiom.                     *)
(* The core rule has zero premises; the surface tactic also applies when *)
(* the precondition is merely *equivalent* to [false].                   *)
(* Note the catalogue's remark: there is no "phoare[_ ==> true] closes"  *)
(* axiom, because the bound still has to be discharged; [prbounded]      *)
(* (S4.3) plays that role.                                               *)

Lemma ec_exfalso c Q r d : phl pred0 c Q r d.
Proof. Admitted.

Lemma ec_exfalso_conseq P c Q r d :
  (forall m, ~~ P m) -> phl P c Q r d.
Proof. Admitted.


(* ==================================================================== *)
(* ===                     2. The conseq family                     === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* The two tables the conseq rules are built from, transcribed.          *)

(* S2.1, postcondition premise, oriented by the comparison               *)
(* ([bdHoare_conseq_conds], ecPhlConseq.ml:218-231).  At an upper bound  *)
(* one may only *weaken* the postcondition, at a lower bound only        *)
(* *strengthen* it, and at an exact bound it must be equivalent.         *)
(* Stated pointwise so that S2.3 can quantify it over reachable          *)
(* memories only.                                                        *)

Definition ec_postimpl (r : bd) (Q Q' : assn) (m : cmem) : Prop :=
  match r with
  | Le => Q m -> Q' m
  | Ge => Q' m -> Q m
  | Eq => Q m = Q' m
  end.

(* S2.2, the admissible bound-and-comparison changes ([bd_goal_r],       *)
(* ecPhlConseq.ml:95-106).  [bd_goal_r] is a *partial* function of       *)
(* [(<>, <>')]; the rows it does not define are user errors in           *)
(* EasyCrypt, and [False] here.                                          *)
(*                                                                      *)
(*    goal <>  |  new <>'   |  premise                                   *)
(*    ---------+------------+---------------------                       *)
(*      <=     |  <= or =   |  d' <= d                                   *)
(*      >=     |  >= or =   |  d <= d'                                   *)
(*      =      |  =         |  d' = d                                    *)
(*      =      |  >=        |  d = 1 /\ d' = 1                           *)
(*      =      |  <=        |  d = 0 /\ d' = 0                           *)
(*    otherwise|            |  (error)                                   *)

Definition ec_bd_goal (r r' : bd) (d d' : R) : Prop :=
  match r, r' with
  | Le, Le | Le, Eq => d' <= d
  | Ge, Ge | Ge, Eq => d <= d'
  | Eq, Eq         => d' = d
  | Eq, Ge         => d = 1 /\ d' = 1
  | Eq, Le         => d = 0 /\ d' = 0
  | _ , _          => False
  end.

(* -------------------------------------------------------------------- *)
(* S2.1  Consequence (pre/post).                                         *)
(*                                                                      *)
(* phl.v already proves the three instances -- [phl_conseq_le],          *)
(* [phl_conseq_ge] and [phl_conseq_eq] -- and their orientations match   *)
(* the table above exactly ([phl_conseq_eq] changes the precondition     *)
(* only, which is the [=] row read as an equivalence).  Only the         *)
(* comparison-generic packaging is new.                                  *)

Lemma ec_conseq P P' Q Q' c r d :
     (forall m, P m -> P' m)
  -> (forall m, ec_postimpl r Q Q' m)
  -> phl P' c Q' r d
  -> phl P  c Q  r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S2.2  Bound and comparison change.  One lemma for the whole table:    *)
(* the seven admissible rows are the seven cases of [ec_bd_goal] that    *)
(* are not [False].                                                      *)
(*                                                                      *)
(* This is the workhorse EasyCrypt uses internally to normalise a bound  *)
(* before applying the real rule -- in [skip] (S1.1), [proc *] (S1.11),  *)
(* [hoare] (S3.2), [phoare split] (S3.4-S3.5) and [islossless] (S4.5).   *)
(* By (G1) its premise is a plain condition on reals.                    *)
(*                                                                      *)
(* The [Eq, Ge] and [Eq, Le] rows go through [phl_le1] and [phl_ge0].    *)

Lemma ec_conseq_bd P Q c r r' d d' :
     ec_bd_goal r r' d d'
  -> phl P c Q r' d'
  -> phl P c Q r  d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S2.3  Not-modified variants.                                          *)
(*                                                                      *)
(* Same as S2.1, but the postcondition premise need only hold on the     *)
(* memories reachable from [m] by running [c] -- those that agree with   *)
(* [m] off [hl.mod c].  See (G5) for the three limits: [nocall c] is     *)
(* required by [hl.mod_spec]; [hl.mod (call n) = pred0], which is why;   *)
(* and [hl.mod]/[hl.eqon] see the local store only, so EasyCrypt's       *)
(* coverage of global assignments is not reproduced.                     *)
(*                                                                      *)
(* Proof: [hl.mod_spec] gives                                            *)
(*   range [pred m' | `[< hl.eqon (predC (hl.mod c)) m m' >]]            *)
(*         (ssem_ ps c m),                                              *)
(* then [le_in_pr] at [<=]/[>=] and [eq_in_pr] at [=].                   *)

Lemma ec_conseq_notmod P Q Q' c r d :
     nocall c
  -> (forall m, P m -> forall m',
        hl.eqon (predC (hl.mod c)) m m' -> ec_postimpl r Q Q' m')
  -> phl P c Q' r d
  -> phl P c Q  r d.
Proof. Admitted.

(* The derived [conseq_nm]: change pre *and* post in the not-modified    *)
(* style ([gen_conseq_nm], ecPhlConseq.ml:633-645).                      *)

Lemma ec_conseq_nm P P' Q Q' c r d :
     nocall c
  -> (forall m, P m -> P' m)
  -> (forall m, P m -> forall m',
        hl.eqon (predC (hl.mod c)) m m' -> ec_postimpl r Q Q' m')
  -> phl P' c Q' r d
  -> phl P  c Q  r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S2.4  Postcondition conjunction split.                                *)
(*                                                                      *)
(* Splits a conjunct off the postcondition into a *Hoare* side condition *)
(* -- sound because the Hoare part is certain and therefore consumes no  *)
(* probability mass.  Two directions, EasyCrypt's [~add:false] and       *)
(* [~add:true].                                                          *)
(*                                                                      *)
(* Proof: [pr_range] turns the [hoare] premise into                      *)
(* [range Q (ssem_ ps c m)], and then [eq_in_pr] identifies              *)
(* [\P_[.] (Q' /\ Q)] with [\P_[.] Q'].                                  *)

Lemma ec_conseq_conj_rem P Q Q' c r d :
     hoare P c Q
  -> phl P c (Q' /\ Q)%A r d
  -> phl P c Q' r d.
Proof. Admitted.

Lemma ec_conseq_conj_add P Q Q' c r d :
     hoare P c Q
  -> phl P c Q' r d
  -> phl P c (Q' /\ Q)%A r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S2.5  Transitivity via an equivalence.                                *)
(*                                                                      *)
(* Proves a pHL judgement about [c1] from a coupling with [c2] plus a    *)
(* pHL judgement about [c2].  The relational judgement is [prhl_] of     *)
(* prhl/prhl.v; the probability is transported by [prhl.prhl_lepr] at    *)
(* [<=] and [>=] and by [prhl.prhl_eqpr] at [=].                         *)
(*                                                                      *)
(* The catalogue's [cond1] also carries [b1 = b2[&m2]]; that is vacuous  *)
(* by (G1) -- the bound is a constant, and the same [d] is used on both  *)
(* sides.  The catalogue's [cond2] is folded into the coupling's         *)
(* postcondition, which is where [prhl_lepr] needs it.                   *)

Lemma ec_conseq_equiv_le P1 P2 Q1 Q2 (PR : rassn) c1 c2 d :
     (forall m1, P1 m1 -> exists m2, PR (m1, m2) && P2 m2)
  -> prhl.prhl_ ps PR c1 c2 [pred m : rmem | Q1 m.1 ==> Q2 m.2]
  -> phl P2 c2 Q2 '<= d
  -> phl P1 c1 Q1 '<= d.
Proof. Admitted.

Lemma ec_conseq_equiv_ge P1 P2 Q1 Q2 (PR : rassn) c1 c2 d :
     (forall m1, P1 m1 -> exists m2, PR (m1, m2) && P2 m2)
  -> prhl.prhl_ ps PR c1 c2 [pred m : rmem | Q2 m.2 ==> Q1 m.1]
  -> phl P2 c2 Q2 '>= d
  -> phl P1 c1 Q1 '>= d.
Proof. Admitted.

Lemma ec_conseq_equiv_eq P1 P2 Q1 Q2 (PR : rassn) c1 c2 d :
     (forall m1, P1 m1 -> exists m2, PR (m1, m2) && P2 m2)
  -> prhl.prhl_ ps PR c1 c2 [pred m : rmem | Q1 m.1 == Q2 m.2]
  -> phl P2 c2 Q2 '= d
  -> phl P1 c1 Q1 '= d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S2.6  The surface conseq -- the composite the user actually sees:     *)
(* S2.2 to change the bound, then S2.3 in not-modified style.            *)
(* [conseq (: P' ==> Q')] with an unchanged bound instantiates           *)
(* [r' := r], [d' := d], where [ec_bd_goal] is reflexivity and the       *)
(* premise vanishes.                                                     *)

Lemma ec_conseq_full P P' Q Q' c r r' d d' :
     nocall c
  -> (forall m, P m -> P' m)
  -> (forall m, P m -> forall m',
        hl.eqon (predC (hl.mod c)) m m' -> ec_postimpl r Q Q' m')
  -> ec_bd_goal r r' d d'
  -> phl P' c Q' r' d'
  -> phl P  c Q  r  d.
Proof. Admitted.


(* ==================================================================== *)
(* ===                3. Views and bound splitting                  === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* S3.1  hoare -- the [= 0] view, both directions.                       *)
(*                                                                      *)
(*   |- hoare[ c : P ==> ~Q ]            |- phoare[ c : P ==> ~Q ] = 0   *)
(*   ------------------------            ---------------------------    *)
(*   |- phoare[ c : P ==> Q ] = 0        |- hoare[ c : P ==> Q ]         *)
(*                                                                      *)
(* The two logics coincide at bound 0: [phoare[c : P ==> Q] = 0] says    *)
(* that [Q] is almost never established, i.e. [hoare[c : P ==> ~Q]].     *)
(* This is what makes the [hoare] notation of (G4) legitimate; note      *)
(* that [hoare P c (~ Q)] unfolds to [phl P c (~ ~ Q) '= 0], which is    *)
(* [\P_[.] Q = 0] up to [predCK].                                        *)

Lemma ec_view0 P Q c : phl P c Q '= 0 <-> hoare P c (~ Q)%A.
Proof. Admitted.

(* The [range] form of the same fact, i.e. the (G4) claim that the       *)
(* [hoare] notation is [hl_ ps] of hl/hl_stmt.v.  Proof: [pr_range]      *)
(* (pwhile/range.v:69).                                                  *)

Lemma ec_hoare_range P Q c :
  hoare P c Q <-> (forall m, P m -> range Q (ssem_ ps c m)).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S3.2  hoare -- the surface tactic.  By (G1) the catalogue's           *)
(* [forall &m, P => (0 <> b)] premise is the plain [r 0 d].              *)
(* Instantiating: [<= d] gives [0 <= d]; [>= d] gives [d <= 0];          *)
(* [= d] gives [d = 0].                                                  *)

Lemma ec_hoare_bd P Q c r d :
  r 0 d -> hoare P c (~ Q)%A -> phl P c Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S3.3  hoare from pHL at bound 1.                                      *)
(*                                                                      *)
(*   |- phoare[ c : P ==> Q ] = 1                                        *)
(*   ---------------------------                                         *)
(*     |- hoare[ c : P ==> Q ]                                           *)
(*                                                                      *)
(* Proof: [\P_[mu] Q = 1] and [\P_[mu] Q <= \P_[mu] predT <= 1] force    *)
(* [\P_[mu] predT = 1], whence [\P_[mu] (~ Q) = 0] by [pr_predC].        *)

Lemma ec_hoare_of_ll P Q c : phl P c Q '= 1 -> hoare P c Q.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S3.4  phoare split on a conjunctive or disjunctive postcondition.     *)
(*                                                                      *)
(* Inclusion-exclusion: Pr[A /\ B] = Pr[A] + Pr[B] - Pr[A \/ B].  Note   *)
(* the *dual* connective and the *opposite* comparison in the third      *)
(* premise -- this is what the catalogue's transcript of the EasyCrypt   *)
(* output shows:                                                         *)
(*                                                                      *)
(*   for  phoare[ c : true ==> A /\ B ] = 1/4  with                      *)
(*        phoare split (1/2) (1/2) (3/4)  EasyCrypt emits                *)
(*     forall _, 1/2 + 1/2 - 3/4 = 1/4                                   *)
(*     phoare[ c : true ==> A ]      = 1/2                               *)
(*     phoare[ c : true ==> B ]      = 1/2                               *)
(*     phoare[ c : true ==> A \/ B ] = 3/4                               *)
(*                                                                      *)
(* Proof: [pr_and] resp. [pr_or] (counting_distr.v:1729, :1719).         *)
(* Caveat for the proof pass: those are stated with [[predI A & B]] /    *)
(* [[predU A & B]] while [%A] gives [predI A B]; convertible, but        *)
(* [eq_pr] may be needed to line the two up syntactically.               *)

Lemma ec_split_and P (A B : assn) c r d d1 d2 d3 :
     r (d1 + d2 - d3) d
  -> phl P c A r d1
  -> phl P c B r d2
  -> phl P c (A \/ B)%A (bd_opp r) d3
  -> phl P c (A /\ B)%A r d.
Proof. Admitted.

Lemma ec_split_or P (A B : assn) c r d d1 d2 d3 :
     r (d1 + d2 - d3) d
  -> phl P c A r d1
  -> phl P c B r d2
  -> phl P c (A /\ B)%A (bd_opp r) d3
  -> phl P c (A \/ B)%A r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S3.5  phoare split ! on a negation.  Pr[Q] = Pr[true] - Pr[~Q].       *)
(*                                                                      *)
(* [\P_[.] predT] is the sub-distribution *weight*, not [1] -- which is  *)
(* exactly why the catalogue's first premise is                          *)
(* [phoare[ c : P ==> true ] <> b1] and not a constant.                  *)
(*                                                                      *)
(* Catalogue transcript: for [phoare[ c : true ==> Q ] <= 1/2] with      *)
(* [phoare split ! 1 (1/2)] EasyCrypt emits                              *)
(*     forall _, true => 1 - 1/2 <= 1/2                                  *)
(*     phoare[ c : true ==> true ] <= 1                                  *)
(*     phoare[ c : true ==> !Q ]   >= 1/2                                *)
(*                                                                      *)
(* Proof: [pr_predC] (counting_distr.v:1741).                            *)

Lemma ec_split_not P Q c r d d1 d2 :
     r (d1 - d2) d
  -> phl P c predT r d1
  -> phl P c (~ Q)%A (bd_opp r) d2
  -> phl P c Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S3.6  phoare split, case form: split the postcondition on an          *)
(* arbitrary [Phi].  Proof: [prID] (counting_distr.v:1654).              *)

Lemma ec_split_case P Q (Phi : assn) c r d d1 d2 :
     r (d1 + d2) d
  -> phl P c (Phi /\ Q)%A   r d1
  -> phl P c (~ Phi /\ Q)%A r d2
  -> phl P c Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S3.7  phoare equiv -- equiv collapses to pHL when the other side is   *)
(* empty.                                                                *)
(*                                                                      *)
(*   |- phoare[ c : P ==> Q ] = 1                                        *)
(*   -----------------------------------                                 *)
(*   |- equiv[ c ~ [] : P<1> ==> Q<1> ]                                  *)
(*                                                                      *)
(* [skip] plays EasyCrypt's empty statement.  The [= 1] is               *)
(* load-bearing, and is exactly why EasyCrypt demands it: it is what     *)
(* forces [dweight (ssem_ ps c m.1) = 1], without which no coupling      *)
(* against [dunit m.2] exists.                                           *)
(*                                                                      *)
(* Proof: [\P_[mu] Q = 1] gives both [dweight mu = 1] and [range Q mu]   *)
(* (via [pr_predC] then [pr_range]).  Take                               *)
(*   nu := \dlet_(m1 <- mu) dunit (m1, m.2);                             *)
(* [dfst nu = mu] by [dmargin_dlet] + [dmargin_dunit], and               *)
(* [dsnd nu = dunit m.2] by the [-[RHS]mul1r -<weight> -dletC] step of   *)
(* [prhl_rndL] (prhl.v:276-278); the range side by [range_dlet] and      *)
(* [range_dunit].                                                        *)

Lemma ec_phoare_equivL P Q c :
     phl P c Q '= 1
  -> prhl.prhl_ ps [pred m : rmem | P m.1] c skip [pred m : rmem | Q m.1].
Proof. Admitted.

Lemma ec_phoare_equivR P Q c :
     phl P c Q '= 1
  -> prhl.prhl_ ps [pred m : rmem | P m.2] skip c [pred m : rmem | Q m.2].
Proof. Admitted.


(* ==================================================================== *)
(* ===                    4. Probability bridges                    === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* S4.1 / S4.2  byphoare and bypr.                                       *)
(*                                                                      *)
(* In EasyCrypt these connect the pHL judgement to the [Pr[...]]         *)
(* language of the ambient logic.  Here that language *is* the           *)
(* definition of [phl_]: EasyCrypt's [Pr[ c @ &m : Q ]] is               *)
(* [\P_[ssem_ ps c m] Q].  So [bypr] is the unfolding of [phl_],         *)
(* definitionally true, and recorded only for the correspondence.        *)

Lemma ec_bypr P Q c r d :
  phl P c Q r d <-> (forall m, P m -> r (\P_[ssem_ ps c m] Q) d).
Proof. Admitted.

(* [byphoare] additionally relates the probability's event [ev] to the   *)
(* judgement's postcondition [Q].  The comparison is read off the goal   *)
(* shape ([ecPhlDeno.ml:41-56]): [Pr[.] <= b] gives [ev => Q],           *)
(* [b <= Pr[.]] gives [Q => ev], [Pr[.] = b] gives [ev <=> Q] -- which   *)
(* is exactly [ec_postimpl r ev Q].                                      *)

Lemma ec_byphoare P Q (ev : assn) c r d m :
     phl P c Q r d
  -> P m
  -> (forall m', ec_postimpl r ev Q m')
  -> r (\P_[ssem_ ps c m] ev) d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S4.3  prbounded -- closes a pHL goal whose bound is trivially         *)
(* satisfied.  This is the pHL analogue of [t_hoare_true], and the only  *)
(* rule of the catalogue that is *exclusively* pHL.                      *)
(*                                                                      *)
(* The first two rows are already phl.v's [phl_le1] and [phl_ge0]:       *)
(*   Lemma phl_le1 P c Q : phl P c Q '<= 1.                              *)
(*   Lemma phl_ge0 P c Q : phl P c Q '>= 0.                              *)
(* Only the third row and the two [conseq] catch-alls are new.           *)

Lemma ec_prbounded_false P c r : phl P c pred0 r 0.
Proof. Admitted.

Lemma ec_prbounded_le P Q c d : 1 <= d -> phl P c Q '<= d.
Proof. Admitted.

Lemma ec_prbounded_ge P Q c d : d <= 0 -> phl P c Q '>= d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S4.4  fel -- the failure-event lemma -- NOT FORMALIZED.               *)
(* [t_failure_event_r] is driven by a counter, a query bound, per-oracle *)
(* preconditions over the oracle set of an abstract module, and a        *)
(* [PV.indep] check that the failure event, counter and invariant are    *)
(* modified only inside oracles.  None of oracle sets, per-oracle specs  *)
(* or [PV.indep] exists here (see S1.11), so the rule cannot be stated.  *)
(* Its only pHL premise, [not_F_to_F], is an ordinary pHL judgement.     *)

(* -------------------------------------------------------------------- *)
(* S4.5  islossless.                                                     *)
(*                                                                      *)
(* [islossless f] is notation for [phoare[ f : true ==> true ] = 1].     *)
(* The tactic itself is a syntax-directed strategy                       *)
(* ([ll_strategy_of_stmt]); what is formalized here is its *content*,    *)
(* one rule per instruction shape.  The [conseq] steps the tactic wraps  *)
(* around them are S2.1 and S2.2.                                        *)

Lemma ec_ll_skip : phl predT skip predT '= 1.
Proof. Admitted.

Lemma ec_ll_assgn {T : IhbType.type} (x : vars T) (e : expr T) :
  phl predT (x <<- e) predT '= 1.
Proof. Admitted.

Lemma ec_ll_gassgn {T : IhbType.type} (x : vars T) (e : expr T) :
  phl predT (G x <<- e) predT '= 1.
Proof. Admitted.

(* The hypothesis is the losslessness of the sampled distribution; it is *)
(* load-bearing (a sub-distribution of weight < 1 loses mass).           *)

Lemma ec_ll_rnd {T : IhbType.type} (x : vars T) (e : dexpr T) :
     (forall m, \P_[`[{e}] m] predT = 1)
  -> phl predT (x <$- e) predT '= 1.
Proof. Admitted.

Lemma ec_ll_seq c1 c2 :
     phl predT c1 predT '= 1
  -> phl predT c2 predT '= 1
  -> phl predT (c1 ;; c2) predT '= 1.
Proof. Admitted.

Lemma ec_ll_if (e : bexpr) c1 c2 :
     phl `[{e}] c1 predT '= 1
  -> phl (~ `[{e}])%A c2 predT '= 1
  -> phl predT (If e then c1 else c2) predT '= 1.
Proof. Admitted.

Lemma ec_ll_block (bs rs : seq (@binding _ cmem)) c :
     (forall m, phl [pred m0 | m0 == minit m bs] c predT '= 1)
  -> phl predT (Block bs Do c Return rs) predT '= 1.
Proof. Admitted.

Lemma ec_ll_call (f : ident) :
  phl predT (ps f) predT '= 1 -> phl predT (call f) predT '= 1.
Proof. Admitted.

(* The loop case is the S1.8(a) variant rule at [Q := predT].            *)

Lemma ec_ll_while (I : assn) (vrnt : cmem -> int) (e : bexpr) c :
     (forall z : int,
        phl (I /\ `[{e}] /\ [pred m | vrnt m == z])%A c
            (I /\ [pred m | vrnt m < z])%A '= 1)
  -> (forall m, I m -> vrnt m <= 0 -> ~~ `[{e}] m)
  -> phl I (While e Do c) predT '= 1.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S4.6  auto, trivial, exfalso -- NOT RULES.                            *)
(* These are the automation entry points; none introduces a rule of its  *)
(* own, they only try the ones above.  Of the lemmas [t_auto] chains,    *)
(* the two that can close a pHL goal are [t_core_exfalso] (S1.16,        *)
(* [ec_exfalso]) and [t_prbounded] (S4.3).  A [Hint Resolve ... :        *)
(* ec_phl] database is deliberately NOT declared while the lemmas of     *)
(* this file are [Admitted]: it would let [eauto] close goals on         *)
(* nothing.  Add it in the proof pass.                                   *)

(* -------------------------------------------------------------------- *)
(* S4.7  rewrite Pr[...] -- NOT FORMALIZED.                              *)
(* An ambient rewriting tactic over [Pr[...]] terms, not an inference    *)
(* rule.  It appears in the catalogue only because one lemma it can      *)
(* instantiate, [pr_mu1_le_eq_mu1], carries a pHL losslessness           *)
(* hypothesis -- i.e. an instance of S4.5.                               *)

(* -------------------------------------------------------------------- *)
(* S4.8  one-sided call from an equiv goal -- NOT FORMALIZED.            *)
(* [t_equiv_call1] is an *equiv* primitive whose callee obligation is a  *)
(* pHL losslessness spec.  Stating it means proving a [prhl_] rule for   *)
(* [Block ... (call f) ...], and prhl.v has no rule for [block] or       *)
(* [call] to build it on -- that is new prhl development, not a pHL      *)
(* rule.  Its pHL side condition is just S4.5.                           *)

(* ==================================================================== *)
(* ===                      5. Code transforms                      === *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* Every rule of this group obeys one schema: transform the statement,   *)
(* rewrap the *same* judgement -- pre, post, comparison and bound are    *)
(* carried through untouched.  The schema itself is the following        *)
(* congruence, the analogue of [hl_eq] (hl/hl.v:103); each rule below is *)
(* this lemma applied to an [ssem] equation that pwhile already proves.  *)

Lemma ec_eq P Q c c' r d :
     (forall m, P m -> ssem_ ps c m = ssem_ ps c' m)
  -> phl P c Q r d
  -> phl P c' Q r d.
Proof. Admitted.

(* The [Proper] packaging, mirroring [hl_m] (hl/hl.v:111).  The proof    *)
(* pass should re-declare this as a [Global Instance].                   *)

Lemma ec_m :
  Proper (eq ==> eqcmd ps ==> eq ==> eq ==> eq ==> iff) (phl_ ps).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S5.1  wp.                                                             *)
(*                                                                      *)
(*   |- phoare[ s_hd : P ==> wp(s_wp, Q) ] <> b                          *)
(*   ------------------------------------------                          *)
(*     |- phoare[ s_hd; s_wp : P ==> Q ] <> b                            *)
(*                                                                      *)
(* wp is deliberately restricted for pHL: [wp_instr] handles only        *)
(* [Sasgn], [Sif] and [Smatch], and raises [No_wp] on everything else --  *)
(* in particular on [Srnd] and [Scall].  ecPhlWp.mli:10-13 states the    *)
(* reason: "WP only operates over assignments and conditional            *)
(* statements.  Any weakening of this restriction may break the          *)
(* soundness of the bounded hoare logic."                                *)
(*                                                                      *)
(* Stated per instruction, so that no [wp] fixpoint has to be defined.   *)
(* The assignment cases are exact: [ssem (x <<- e) m = dunit m.[x <- e]] *)
(* so [pr_dunit] transports the postcondition verbatim.                  *)

Lemma ec_wp_asgn {T : IhbType.type} P Q (x : vars T) (e : expr T) s r d :
     phl P s [pred m | Q m.[x <- `[{e}] m]] r d
  -> phl P (s ;; (x <<- e)) Q r d.
Proof. Admitted.

Lemma ec_wp_gassgn {T : IhbType.type} P Q (x : vars T) (e : expr T) s r d :
     phl P s [pred m | Q (m.{x <- `[{e}] m}) ] r d
  -> phl P (s ;; (G x <<- e)) Q r d.
Proof. Admitted.

(* The [Sif] case of [wp_instr] is NOT stated: [wp] of a conditional     *)
(* recurses into both branches, so writing it requires either a [wp]     *)
(* fixpoint over the assignment/conditional fragment or a determinism    *)
(* predicate on the branches -- an additional construction either way,   *)
(* which this file's scope rule excludes.  Note that the *operational*   *)
(* content of a leading conditional is already available as [ec_cond]    *)
(* (S1.3), which handles a conditional followed by a tail without any    *)
(* [wp] computation.                                                     *)

(* -------------------------------------------------------------------- *)
(* S5.2  sp -- the dual of wp, pushing the precondition forward.         *)
(*                                                                      *)
(* The catalogue's extra side condition [check_form_indep] ("the bound   *)
(* should not be modified by the statement targeted by sp") has no       *)
(* counterpart here and is vacuous by (G1); it exists in EasyCrypt       *)
(* precisely because the bound is a formula over the same memory.        *)

Lemma ec_sp_asgn {T : IhbType.type} P Q (x : vars T) (e : expr T) c r d :
     phl [pred m | `[< exists m0, P m0 /\ m = m0.[x <- `[{e}] m0] >]] c Q r d
  -> phl P ((x <<- e) ;; c) Q r d.
Proof. Admitted.

Lemma ec_sp_gassgn {T : IhbType.type} P Q (x : vars T) (e : expr T) c r d :
     phl [pred m | `[< exists m0, P m0 /\ m = m0.{x <- `[{e}] m0} >]] c Q r d
  -> phl P ((G x <<- e) ;; c) Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S5.3  inline.                                                         *)
(*                                                                      *)
(* The call-site case is S1.10 ([ec_proc]).  For the positional form,    *)
(* pwhile already has the syntactic transformation, [inliner]            *)
(* (psemantic.v:1079), which replaces every [call f] by [ps f]; what is  *)
(* missing is its semantic correctness, an induction over [cmd_].  No    *)
(* new definition is introduced.                                         *)

Lemma ssem_inliner c m : ssem_ ps (inliner c ps) m = ssem_ ps c m.
Proof. Admitted.

Lemma ec_inline P Q c r d :
  phl P (inliner c ps) Q r d -> phl P c Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S5.4  unroll, splitwhile, simplify if, and the structural rewrites.   *)
(*                                                                      *)
(* All are [ec_eq] applied to an equation pwhile already proves:         *)
(*   [unroll_while]  (psemantic.v:465)                                   *)
(*   [split_while]   (psemantic.v:515)                                   *)
(*   [if_same]       (psemantic.v:678)                                   *)
(*   [seqA], [seq_skip_l], [seq_skip_r]  (psemantic.v:544-553)           *)

Lemma ec_unroll P Q (e : bexpr) c r d :
     phl P (IfT e then (c ;; While e Do c)) Q r d
  -> phl P (While e Do c) Q r d.
Proof. Admitted.

Lemma ec_splitwhile P Q (e1 e2 : bexpr) c r d :
     phl P (While (e1 && e2) Do c ;; While e1 Do c) Q r d
  -> phl P (While e1 Do c) Q r d.
Proof. Admitted.

Lemma ec_if_same P Q (e : bexpr) c r d :
  phl P c Q r d -> phl P (If e then c else c) Q r d.
Proof. Admitted.

Lemma ec_seqA P Q c1 c2 c3 r d :
  phl P (c1 ;; c2 ;; c3) Q r d -> phl P (c1 ;; (c2 ;; c3)) Q r d.
Proof. Admitted.

Lemma ec_skip_l P Q c r d : phl P c Q r d -> phl P (skip ;; c) Q r d.
Proof. Admitted.

Lemma ec_skip_r P Q c r d : phl P c Q r d -> phl P (c ;; skip) Q r d.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* S5.4 (rest)  kill, alias, set, set match, cfold, fission, fusion --   *)
(* NOT FORMALIZED.                                                       *)
(* Each needs a *read*-set analysis: [kill] checks that the removed      *)
(* block writes nothing the postcondition or an enclosing block reads,   *)
(* [alias]/[set]/[cfold] need fresh-variable and substitution machinery, *)
(* [fission]/[fusion] need index reasoning on loops.  [hl.mod] gives     *)
(* *written* variables only; there is no [reads], and [hl.eaccess]       *)
(* handles bare variables only and is used nowhere.                      *)
(* Note that [kill] would also emit a pHL losslessness premise           *)
(* [phoare[ ks : true ==> true ] = 1], i.e. an instance of S4.5.         *)

(* -------------------------------------------------------------------- *)
(* S5.5  swap / interleave -- NOT FORMALIZED.                            *)
(* Needs read/write independence between the swapped fragments, hence    *)
(* the same missing [reads] analysis as above.                           *)

(* -------------------------------------------------------------------- *)
(* S5.6  weakmem, proc case, proc rewrite / proc change, change stmt --  *)
(* NOT FORMALIZED.                                                       *)
(* These act on EasyCrypt's goal representation (memory environments,    *)
(* [kinds] lists, [hl_set_stmt]) rather than on the judgement, and have  *)
(* no counterpart in a semantic formalization.                           *)

(* ==================================================================== *)
(* ===             6. Not applicable to pHL (catalogue S6)          === *)
(* ==================================================================== *)
(*                                                                      *)
(* Catalogue S6 lists the tactics that have no bdHoare arm at all:       *)
(* [upto], [eqobs-in]/[sim], [trans]/[repl], [sym], [rwequiv],           *)
(* [outline], [eager] (equiv or eager only); [rwprgm] (hoare only);      *)
(* [circuit]/[bdep] (circuits, not program logics); [hoare split]        *)
(* (unsound for pHL by design -- its pHL counterpart is S3.4, which      *)
(* pays for the split with inclusion-exclusion); [concave] and           *)
(* [call concave] (ehoare only); [t_hoare_true] / [t_ehoare_zero] (no    *)
(* pHL arm -- S4.3 plays that role); and [rnd f g] ([PTwoRndParams],     *)
(* equiv only).  Nothing to state.                                       *)

End Rules.
End ec_phl.
