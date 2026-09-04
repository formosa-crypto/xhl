(* ==================================================================== *)
(*  call at [<=] proves false.                                          *)
(*                                                                      *)
(*  Witness for the [!!! WRONG] flag on [ec_call_seq_le] in             *)
(*  phl/ec_phl.v.                                                       *)
(*                                                                      *)
(*  Rule:     t_bdhoare_call, src/phl/ecPhlCall.ml:304-361              *)
(*            FHle/None row of the residual table, :347-349             *)
(*  Checked:  easycrypt r2026.07-10-ge8c6691, NO SMT prover configured  *)
(*  Command:  easycrypt compile ec_call_seq_le.ec                       *)
(* ==================================================================== *)

(*  THE DEFECT -- missing 0 <= b.
    t_bdhoare_call emits exactly two subgoals (:361):

      f_concl  the callee spec, via bdhoare_call_spec (:291-301);
               at (FHle, None) that is  phoare[ f : fpre ==> fpost ] <= b
      concl    the residual on the prefix (:344-359); at (FHle, None)
               that is a *Hoare* goal, f_hoareS (:349), with
               postcondition  fpre[args] /\ forall result, forall mod(f).
                                (Q[result] => fpost[result])

    Both can be discharged without ever forcing b to be a probability:

      - give the callee an UNSATISFIABLE precondition, and its spec
        holds at any bound whatsoever, including a negative one;
      - that same false fpre makes the residual's postcondition collapse
        (f_anda_simpl at :341), and a diverging prefix satisfies any
        Hoare postcondition.

    Semantically the rule needs 0 <= b for the usual reason: on the
    support the prefix gives F m' <= b, hence
    E_[mu] F <= P_[mu] predT * b, which is <= b only when 0 <= b.

    Contrast the two lower/exact rows: at (FHge, None) the residual
    comparison SWITCHES to FHeq 1%r (:357) and at (FHeq, None) it is
    likewise FHeq 1%r (:353), which forces the prefix to be lossless and
    makes those rows sound.  Only FHle escapes with a Hoare residual.   *)

(*  THE INSTANCE.
      P := true   Q := true   fpre := false   fpost := true
      prefix := while (true) { }             callee := G.g
      b := -1

    The residual's postcondition prints simply as [false], because the
    false fpre absorbs the conjunction.

    Pr[M.f : true] is 0, so the conclusion asserts 0 <= -1.             *)

require import AllCore Distr StdOrder.
import RealOrder.

module G = { proc g() : unit = { } }.
module M = { proc f() : unit = { while (true) { } G.g(); } }.

(* ---------------------------------------------------------------- *)

lemma bogus : phoare[ M.f : true ==> true ] <= (-1)%r.
proof.
proc.
call (_ : false ==> true).
+ (* f_concl : phoare[ G.g : false ==> true ] <= (-1)%r               *)
  (* The callee precondition is unsatisfiable, so the bound is free.  *)
  exfalso; auto.
+ (* concl : hoare[ while (true) {} : true ==> false ]                *)
  (* A Hoare goal (:349) -- vacuous by divergence.                    *)
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
