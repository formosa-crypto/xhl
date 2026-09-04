(* ==================================================================== *)
(*  seq at [>=] proves false -- with an ordinary conclusion bound.       *)
(*                                                                      *)
(*  Witness for the [!!! WRONG] flag on [ec_seq_ge] in phl/ec_phl.v.    *)
(*                                                                      *)
(*  Rule:     t_bdhoare_seq_r_low, src/phl/ecPhlSeq.ml:44               *)
(*            surface t_bdhoare_seq_r, :103; dispatcher arm :258-263    *)
(*  Checked:  easycrypt r2026.07-10-ge8c6691, NO SMT prover configured  *)
(*  Command:  easycrypt compile ec_seq_ge.ec                            *)
(* ==================================================================== *)

(*  THE DEFECT -- the same missing non-negativity as ec_seq_le.ec, but
    this instance is the more alarming of the two, because the bound in
    the JUDGEMENT BEING PROVED is perfectly ordinary.

    At [>=], condbd (ecPhlSeq.ml:70) reads

      forall &m, P => b <= f1 * f2 + g1 * g2

    and a product of LOWER bounds is a lower bound on the product only
    when the factors are non-negative.  Nothing requires that.  Two
    negative factors multiply to a positive number, so f1 = f2 = -1
    manufactures the value 1 out of two bounds that constrain nothing:
    every probability is >= -1, so

      phoare[ c : P ==> S ] >= (-1)%r

    is an ordinary, provable EasyCrypt judgement about ANY statement.

    Note the contrast with ec_seq_le.ec: there the conclusion asked for
    a negative upper bound, which a reader might dismiss as a nonsense
    goal nobody would state.  Here the conclusion is

      phoare[ M.f : true ==> true ] >= 1%r

    i.e. "M.f terminates and establishes true" -- a completely routine
    thing to want.  M.f diverges, so the probability is 0.              *)

(*  THE INSTANCE.
      P := true   Q := true   pR := true   phi := true
      s1 := while (true) { }  s2 := (empty)
      f1 := -1    f2 := -1    g1 := 0      g2 := 0     b := 1

    condbd is  1 <= (-1) * (-1) + 0 * 0,  which EasyCrypt's
    f_real_mul_simpl folds to  1%r <= 1%r.
    As in ec_seq_le.ec, condg2 is pruned away (:85-86) because g1 is
    syntactically 0%r, so five goals are emitted.                       *)

require import AllCore Distr StdOrder.
import RealOrder.

module M = { proc f() : unit = { while (true) { } } }.

(* ---------------------------------------------------------------- *)
(* The bogus judgement.  Pr[M.f : true] is 0, so this asserts 1 <= 0. *)

lemma bogus : phoare[ M.f : true ==> true ] >= 1%r.
proof.
proc.
seq 1 : true (-1)%r (-1)%r 0%r 0%r true.
+ (* cond_phi : hoare[ while (true) {} : true ==> true ]               *)
  while (true); auto.
+ (* condf1 : phoare[ while (true) {} : true ==> true ] >= (-1)%r      *)
  (* Vacuous: pr_bounded reduces it to (-1)%r <= 0%r.                  *)
  pr_bounded; move=> _ _; rewrite fromintN; by apply/ltrW/ltrN10.
+ (* condf2 : phoare[ (empty) : true ==> true ] >= (-1)%r              *)
  (* Vacuous for the same reason -- and this is the second -1 whose    *)
  (* product with the first fabricates the bound 1.                    *)
  pr_bounded; move=> _ _; rewrite fromintN; by apply/ltrW/ltrN10.
+ (* condg1 : phoare[ while (true) {} : true ==> !true ] >= 0%r        *)
  (* Closed outright by pr_bounded (ecPhlPr.ml:118).                   *)
  pr_bounded.
+ (* condbd : forall &m, true => 1%r <= 1%r                            *)
  by move=> _ _.
qed.

(* ---------------------------------------------------------------- *)
(* The matching upper bound.  The [hoare] view (ecPhlBdHoare.ml:16)   *)
(* turns [<= 0%r] into the Hoare goal [true ==> !true], which the     *)
(* diverging loop satisfies vacuously.                                *)

lemma diverges : phoare[ M.f : true ==> true ] <= 0%r.
proof. proc; hoare; while (true); auto. qed.

(* ---------------------------------------------------------------- *)

lemma boom &m : false.
proof.
have hge : 1%r <= Pr[M.f() @ &m : true] by byphoare bogus.
have hle : Pr[M.f() @ &m : true] <= 0%r by byphoare diverges.
have : 1%r < 1%r.
- by apply (ler_lt_trans 0%r);
    [apply (ler_trans Pr[M.f() @ &m : true]) | apply ltr01].
by rewrite ltrr.
qed.
