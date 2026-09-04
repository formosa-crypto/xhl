(* ==================================================================== *)
(*  seq at [<=] proves false.                                           *)
(*                                                                      *)
(*  Witness for the [!!! WRONG] flag on [ec_seq_le] in phl/ec_phl.v.    *)
(*                                                                      *)
(*  Rule:     t_bdhoare_seq_r_low, src/phl/ecPhlSeq.ml:44               *)
(*            surface t_bdhoare_seq_r, :103; dispatcher arm :258-263    *)
(*  Checked:  easycrypt r2026.07-10-ge8c6691, NO SMT prover configured  *)
(*  Command:  easycrypt compile ec_seq_le.ec                            *)
(* ==================================================================== *)

(*  THE DEFECT.
    [t_bdhoare_seq_r_low] takes the tuple (phi, pR, f1, f2, g1, g2) and
    emits (:59-71, pruned at :84-96):

      cond_phi  hoare  [ s1 : P        ==> phi   ]
      condf1    phoare [ s1 : P        ==> pR    ] <= f1
      condf2    phoare [ s2 : phi /\  pR ==> Q   ] <= f2
      condg1    phoare [ s1 : P        ==> !pR   ] <= g1
      condg2    phoare [ s2 : phi /\ !pR ==> Q   ] <= g2
      condbd    forall &m, P => f1 * f2 + g1 * g2 <= b

    The conclusion is  phoare[ s1; s2 : P ==> Q ] <= b.

    Nothing anywhere forces  0 <= f2  or  0 <= g2.  The rule needs them:
    [condbd] bounds a PRODUCT, and a product of upper bounds is an upper
    bound on the product only when the right factors are non-negative.
    So a negative second-phase bound lets [condbd] be satisfied by an
    arithmetic accident while the probability mass it is supposed to
    account for is 0.

    There is no [check_bound] anywhere in EasyCrypt: [bhs_bd] is an
    unrestricted real (src/ecAst.ml:270-280), the smart constructors
    check only that memory tags agree (src/ecCoreFol.ml:317-325), and
    typing checks only ~expct:treal (src/ecTyping.ml:3643-3657).        *)

(*  THE INSTANCE.
    Taking  phi := false  is what disarms the second-phase premises: it
    makes condf2 and condg2 vacuous, so f2 and g2 are unconstrained.
    Taking  s1 := while (true) { }  is what makes cond_phi survive that
    choice: a diverging statement satisfies every Hoare judgement, so
    [hoare[ s1 : true ==> false ]] is provable.

      P := true   Q := true   pR := true   phi := false
      s1 := while (true) { }  s2 := (empty)
      f1 := 1     f2 := -1    g1 := 0      g2 := 0     b := -1

    condbd is then  1 * (-1) + 0 * 0 = -1 <= -1,  which holds.
    Note g2 never even appears: g1 is syntactically 0%r, so :85-86
    prunes condg2 away.  Only five goals are emitted.                    *)

require import AllCore Distr StdOrder.
import RealOrder.

module M = { proc f() : unit = { while (true) { } } }.

(* ---------------------------------------------------------------- *)
(* The bogus judgement.  Pr[M.f : true] is 0, so this asserts 0 <= -1. *)

lemma bogus : phoare[ M.f : true ==> true ] <= (-1)%r.
proof.
proc.
seq 1 : true 1%r (-1)%r 0%r 0%r false.
+ (* cond_phi : hoare[ while (true) {} : true ==> false ]              *)
  (* Vacuous: the loop never exits, so the Hoare post is unreachable.  *)
  while (true); auto.
+ (* condf1 : phoare[ while (true) {} : true ==> true ] <= 1%r         *)
  (* True of any statement -- this is the one honest premise.          *)
  pr_bounded.
+ (* condf2 : phoare[ (empty) : false ==> true ] <= (-1)%r             *)
  (* Vacuous by phi := false.  THIS is where -1 enters unchallenged.   *)
  exfalso; auto.
+ (* condg1 : phoare[ while (true) {} : true ==> !true ] <= 0%r        *)
  (* The post is false, so the probability is 0.                       *)
  hoare; auto.
+ (* condbd : forall &m, true => (-1)%r <= (-1)%r                      *)
  by move=> _ _.
qed.

(* ---------------------------------------------------------------- *)
(* The bridge to false.  No SMT: byphoare turns the judgement into a  *)
(* Pr bound, Pr[mu_ge0] gives the matching lower bound, and the two   *)
(* are contradictory by transitivity.                                 *)
(*                                                                    *)
(* Beware: (-1)%r is from_int (-1), NOT the field negation - 1%r that *)
(* ltrN10 talks about.  fromintN bridges the two.                     *)

lemma boom &m : false.
proof.
have hle : Pr[M.f() @ &m : true] <= (-1)%r by byphoare bogus.
have hge : 0%r <= Pr[M.f() @ &m : true] by rewrite Pr[mu_ge0].
have h0 : 0%r <= - 1%r.
- by move: (ler_trans Pr[M.f() @ &m : true] 0%r (-1)%r hge hle); rewrite fromintN.
have : 0%r < 0%r by apply (ler_lt_trans (- 1%r)) => //; apply ltrN10.
by rewrite ltrr.
qed.
