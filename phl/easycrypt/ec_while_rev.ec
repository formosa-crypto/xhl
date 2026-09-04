(* ==================================================================== *)
(*  while (inv) -- the reverse rule at [<=] -- proves false.            *)
(*                                                                      *)
(*  Witness for the [!!! WRONG] flag on [ec_while_rev] in phl/ec_phl.v. *)
(*                                                                      *)
(*  Rule:     t_bdhoare_while_rev_r, src/phl/ecPhlWhile.ml:157-200      *)
(*            FHle only (:161-162 rejects any other comparison)         *)
(*  Checked:  easycrypt r2026.07-10-ge8c6691, NO SMT prover configured  *)
(*  Command:  easycrypt compile ec_while_rev.ec                         *)
(* ==================================================================== *)

(*  THE DEFECT -- missing 0 <= b.
    t_bdhoare_while_rev_r emits two subgoals (:200):

      body_concl (:178-186)
        phoare[ w : inv ==> Q ] <= b  =>
        phoare[ body; w : inv /\ guard ==> Q ] <= b
      rem_concl (:189-198)   -- a *Hoare* goal, f_hoareS at :197
        hoare[ rem_s : P ==> inv /\ forall mod(body).
                                ((inv /\ !guard /\ Q) => bound = 1%r) ]

    The only place the bound is constrained at all is that inner
    [f_eq bound f_r1] at :193 -- and note it is an EQUALITY, b = 1%r,
    not 1%r <= b.  It sits behind an antecedent that mentions Q.

    So two independent choices disarm the whole rule:
      - pick Q unsatisfiable, and the bound condition never fires;
      - pick a guard that is false, and body_concl is vacuous.
    Nothing anywhere then forces b to be a possible probability.

    (An earlier draft of ec_while_rev in ec_phl.v carried 0 <= b and
    1 <= b as premises and was provable.  Neither hypothesis exists in
    t_bdhoare_while_rev_r; removing them to match the implementation is
    what exposed this.)                                                 *)

(*  THE INSTANCE.
      P := true   Q := false   inv := true
      rem_s := x <- 0          loop := while (false) { }     b := -1

    body_concl becomes  phoare[ w : true /\ false ==> false ] <= (-1)%r,
    whose precondition is false.
    rem_concl becomes
      hoare[ x <- 0 : true ==> true /\ (true /\ !false /\ false
                                        => (-1)%r = 1%r) ]
    whose implication has a false antecedent, so the bound equation is
    never reached.

    Pr[M.f : false] is 0, so the conclusion asserts 0 <= -1.            *)

require import AllCore Distr StdOrder.
import RealOrder.

module M = { proc f() : unit = { var x : int; x <- 0; while (false) { } } }.

(* ---------------------------------------------------------------- *)

lemma bogus : phoare[ M.f : true ==> false ] <= (-1)%r.
proof.
proc.
while (true).
+ (* body_concl, with w the abstract rest-of-loop statement.          *)
  (* The loop body is empty, so body; w is just w, and the            *)
  (* precondition inv /\ guard is true /\ false.                      *)
  move=> _; exfalso; auto.
+ (* rem_concl : the bound equation (-1)%r = 1%r is guarded by Q,     *)
  (* and Q is false, so it never has to be proved.                    *)
  auto.
qed.

(* ---------------------------------------------------------------- *)

lemma boom &m : false.
proof.
have hle : Pr[M.f() @ &m : false] <= (-1)%r by byphoare bogus.
have hge : 0%r <= Pr[M.f() @ &m : false] by rewrite Pr[mu_ge0].
have h0 : 0%r <= - 1%r.
- by move: (ler_trans Pr[M.f() @ &m : false] 0%r (-1)%r hge hle); rewrite fromintN.
have : 0%r < 0%r by apply (ler_lt_trans (- 1%r)) => //; apply ltrN10.
by rewrite ltrr.
qed.
