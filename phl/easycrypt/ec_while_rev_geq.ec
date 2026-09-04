(* ==================================================================== *)
(*  while (inv) (vrnt) k eps -- the rate rule at [>=] -- proves false.  *)
(*                                                                      *)
(*  Witness for the [!!! WRONG] flag on [ec_while_rev_geq] in           *)
(*  phl/ec_phl.v.                                                       *)
(*                                                                      *)
(*  Rule:     t_bdhoare_while_rev_geq_r, src/phl/ecPhlWhile.ml:205-306  *)
(*            FHge/FHeq only (:210-211 rejects FHle)                    *)
(*  Checked:  easycrypt r2026.07-10-ge8c6691, NO SMT prover configured  *)
(*  Command:  easycrypt compile ec_while_rev_geq.ec                     *)
(* ==================================================================== *)

(*  THE DEFECT -- missing b <= 1.
    The rule emits six subgoals (:300-306).  The only one that says
    anything at all about the bound is pre_bound_concl (:240-250),
    which at FHge is

      forall &m, P => !guard => (!Q => bound = 0%r)

    -- it constrains b only on the !Q branch.  When Q DOES hold at an
    exit state the rule still claims  b <= Pr[...] <= 1,  yet nothing
    anywhere forces b <= 1.  A lower bound above 1 is therefore
    derivable for a statement whose probability is exactly 1.

    Note the loop must be the whole statement here: check_single_stmt
    at :230 (definition :92-94) rejects any prefix.                     *)

(*  THE INSTANCE -- guard identically false, so the loop is a no-op and
    every premise mentioning the guard is vacuous.

      P := Q := inv := true    guard := false
      vrnt := 0    k := 0    eps := 1    b := 2

    The six goals come out as:
      pre_inv     forall &m, true => true
      pre_bound   forall &m, true => !false => !true => 2%r = 0%r
                  -- vacuous: !true is false, so b is never pinned
      inv_term    forall &m, true => 0 <= 0 /\ (0 <= 0 => !false)
      body        phoare[ w : true ==> true ] >= 2%r =>
                  phoare[ w : true /\ false ==> true ] >= 2%r
      inv_out     phoare[ <skip> : true /\ false ==> true ] = 1%r
      vrnt        (forall &m, true => 0%r < 1%r)
                  /\ forall z, phoare[ <skip> : true /\ false /\ 0 = z
                                        ==> 0 < z ] >= 1%r

    Pr[M.f : true] = 1, so the conclusion asserts 2 <= 1.               *)

require import AllCore Distr StdOrder.
import RealOrder.

module M = { proc f() : unit = { while (false) { } } }.

(* ---------------------------------------------------------------- *)

lemma terminates : phoare[ M.f : true ==> true ] = 1%r.
proof. proc; rcondf 1; auto. qed.

(* ---------------------------------------------------------------- *)

lemma bogus : phoare[ M.f : true ==> true ] >= 2%r.
proof.
proc.
while (true) 0 0 1%r.
+ (* pre_inv_concl (:237)                                            *)
  by move=> _ _.
+ (* pre_bound_concl (:240-250) -- the ONLY bound premise, and it is  *)
  (* disarmed: its !Q antecedent is !true.                            *)
  by move=> _ _.
+ (* inv_term_concl (:253-258)                                       *)
  by move=> _ _.
+ (* body_concl (:289-298), w abstract; precondition inv /\ guard.    *)
  by move=> _; exfalso; auto.
+ (* inv_concl (:280-282); precondition inv /\ guard.                 *)
  by exfalso; auto.
+ (* vrnt_concl (:261-277), a conjunction.                            *)
  split; [by move=> _ _; apply ltr01 | by move=> z; exfalso; auto].
qed.

(* ---------------------------------------------------------------- *)

lemma boom &m : false.
proof.
have h1 : Pr[M.f() @ &m : true] = 1%r by byphoare terminates.
have h2 : 2%r <= Pr[M.f() @ &m : true] by byphoare bogus.
have h3 : 2%r <= 1%r by rewrite -h1.
have : 1%r < 1%r.
- by apply (ltr_le_trans 2%r) => //; rewrite lt_fromint.
by rewrite ltrr.
qed.
