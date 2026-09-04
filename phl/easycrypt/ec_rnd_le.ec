(* ==================================================================== *)
(*  rnd at [<=] proves false.                                           *)
(*                                                                      *)
(*  Witness for the [!!! WRONG] flag on [ec_rnd_le] in phl/ec_phl.v.    *)
(*                                                                      *)
(*  Rule:     t_bdhoare_rnd_r, PSingleRndParam/FHle arm,                *)
(*            src/phl/ecPhlRnd.ml:248-256                               *)
(*  Checked:  easycrypt r2026.07-10-ge8c6691, NO SMT prover configured  *)
(*  Command:  easycrypt compile ec_rnd_le.ec                            *)
(* ==================================================================== *)

(*  THE DEFECT.
    On a goal  phoare[ s; x <$ d : P ==> Q ] <= b  the tactic [rnd E]
    emits a SINGLE premise, and at [<=] that premise is a *Hoare* goal
    (f_hoareS, ecPhlRnd.ml:254):

      hoare[ s : P /\ pre_bound ==> (mu d E <= b) /\ mk_event_cond E ]

    A Hoare judgement is partial correctness, so a diverging prefix
    satisfies it whatever the postcondition says -- including a
    postcondition asserting that a probability is at most -1.  Nothing
    else in the rule looks at b, so nothing forces 0 <= b.

    Semantically the rule needs it: on the support one gets F m' <= b,
    hence  E_[mu] F <= P_[mu] predT * b,  and that is <= b only when
    0 <= b, because the weight of a sub-distribution is <= 1, not = 1.

    Contrast the [>=] shape (ecPhlRnd.ml:257-264), which forces its
    residual to FHeq 1%r and is therefore sound: that bound makes the
    prefix lossless, so the weight really is 1.  Contrast also
    [ec_rnd_le_indep] in ec_phl.v, whose premise is a pHL judgement
    rather than a Hoare one and so already implies 0 <= b.             *)

(*  THE INSTANCE.
      P := true   Q := true   E := fun _ => true
      s := while (true) { }   d := dunit 0    b := -1

    The bound is a closed real, so is_bd_indep holds (ecPhlRnd.ml:193)
    and the pre_bound machinery collapses: bound = b, pre_bound = true,
    no extra binder.  The residual is then

      hoare[ while (true) {} : true /\ true ==>
               mu (dunit 0) (fun _ => true) <= (-1)%r
               /\ forall v, v \in dunit 0 => (fun _ => true) v ]

    whose postcondition is plainly false -- mu (dunit 0) predT is 1 --
    and which is nonetheless provable, because the loop never exits.

    (Incidentally this goal displays mk_event_cond in the orientation
    the code builds, v \in supp d => Q[v/x] => E v, with Q[v/x] = true
    simplified away.  RULES-PHL.md S1.6 tabulates the transpose; see the
    orientation note in phl/ec_phl.v S1.6.)                             *)

require import AllCore Distr StdOrder.
import RealOrder.

module M = {
  proc f() : unit = { var x : int; while (true) { } x <$ dunit 0; }
}.

(* ---------------------------------------------------------------- *)
(* The bogus judgement.  Pr[M.f : true] is 0, so this asserts 0 <= -1. *)

lemma bogus : phoare[ M.f : true ==> true ] <= (-1)%r.
proof.
proc.
rnd (fun (_ : int) => true).
(* the single residual, vacuous by divergence *)
while (true); auto.
qed.

(* ---------------------------------------------------------------- *)

lemma boom &m : false.
proof.
have hle : Pr[M.f() @ &m : true] <= (-1)%r by byphoare bogus.
have hge : 0%r <= Pr[M.f() @ &m : true] by rewrite Pr[mu_ge0].
have h0 : 0%r <= - 1%r.
- by move: (ler_trans Pr[M.f() @ &m : true] 0%r (-1)%r hge hle); rewrite fromintN.
have : 0%r < 0%r by apply (ler_lt_trans (- 1%r)) => //; apply ltrN10.
by rewrite ltrr.
qed.
