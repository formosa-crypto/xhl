(* ==================================================================== *)
(*  while (inv) (vrnt) proves false -- at an ORDINARY bound.            *)
(*                                                                      *)
(*  Witness for the [!!! WRONG] flag on [ec_while_variant] in           *)
(*  phl/ec_phl.v.  This is the most serious of the ten findings.        *)
(*                                                                      *)
(*  Rule:     t_bdhoare_while_r, src/phl/ecPhlWhile.ml:127-153          *)
(*            dispatched by process_while, :567-572, for ANY comparison *)
(*  Checked:  easycrypt r2026.07-10-ge8c6691, NO SMT prover configured  *)
(*  Command:  easycrypt compile ec_while_variant.ec                     *)
(* ==================================================================== *)

(*  THE DEFECT -- not a bound problem.  Every other witness in this
    directory turns on a bound that no [check_bound] rejects.  This one
    does not: the bound here is 0%r and the judgement being proved,

      phoare[ M.f : true ==> true ] <= 0%r

    is an ordinary thing to write.  The rule itself is unsound.

    On a goal  phoare[ s; while e do c : P ==> Q ] <> b,
    t_bdhoare_while_r emits exactly TWO subgoals (:153):

      b_concl (:134-141)  forall z, phoare[ c : inv /\ e /\ vrnt = z
                                             ==> inv /\ vrnt < z ] = 1%r
      concl   (:142-151)  phoare[ s : P ==> inv /\ forall mod(c).
                                    (term_condition /\ (!e => inv => Q)) ] <> b

    NEITHER IS  P => inv.  So the invariant is never connected to the
    precondition, and nothing in the rule says anything about the states
    in which inv FAILS after s.  Semantically

      Pr[s; while : Q] = E_[s] (fun m' => Pr[while @ m' : Q])

    and the premises pin Pr[while @ m' : Q] = 1 only for inv-states m',
    leaving it arbitrary in [0,1] everywhere else.  Hence

      Pr[s; while : Q] >= Pr[s : inv]

    and ONLY the >= direction transfers.  At <= and at = the rule is
    unsound.  process_while (:567-572) nevertheless dispatches here for
    every comparison; only the two *reverse* rules check bhs_cmp
    (:161-162 rejects non-FHle, :210-211 rejects FHle).                 *)

(*  THE INSTANCE -- take the invariant IDENTICALLY FALSE.
      P := true   Q := true   inv := false   vrnt := 0
      s := x <- 0             loop := while (x < 0) { }      b := 0

    Both premises then collapse:
      b_concl  has precondition  false /\ ... , so exfalso closes it;
      concl    has postcondition  f_and_simpl false _  =  false,
               so it reads  phoare[ x <- 0 : true ==> false ] <= 0%r,
               i.e. 0 <= 0.

    Meanwhile the guard x < 0 is false at entry, so M.f terminates and
    Pr[M.f : true] = 1.  The conclusion asserts 1 <= 0.

    The same instance with [= 0%r] in place of [<= 0%r] refutes the
    FHeq case; only [>= 0%r] would be sound (and vacuous).              *)

require import AllCore Distr StdOrder.
import RealOrder.

module M = { proc f() : unit = { var x : int; x <- 0; while (x < 0) { } } }.

(* ---------------------------------------------------------------- *)
(* M.f plainly terminates: the guard is false on entry.               *)

lemma terminates : phoare[ M.f : true ==> true ] = 1%r.
proof. proc; rcondf 2; auto. qed.

(* ---------------------------------------------------------------- *)
(* The bogus judgement, at the same ordinary bound 0%r.               *)

lemma bogus : phoare[ M.f : true ==> true ] <= 0%r.
proof.
proc.
while (false) 0.
+ (* b_concl : phoare[ {} : false /\ x < 0 /\ 0 = z ==> false ] = 1%r *)
  (* Vacuous: the precondition carries the false invariant.           *)
  exfalso; auto.
+ (* concl : phoare[ x <- 0 : true ==> false ] <= 0%r                 *)
  (* The postcondition is inv /\ ..., and inv is false, so f_and_simpl *)
  (* (:150) collapses it to false.  Pr of false is 0.                 *)
  (* NOTE what is absent: no goal ever asks that true => false.       *)
  hoare; auto.
qed.

(* ---------------------------------------------------------------- *)

lemma boom &m : false.
proof.
have h1 : Pr[M.f() @ &m : true] = 1%r by byphoare terminates.
have h0 : Pr[M.f() @ &m : true] <= 0%r by byphoare bogus.
have : 1%r < 1%r.
- by apply (ler_lt_trans 0%r); [rewrite -h1 | apply ltr01].
by rewrite ltrr.
qed.
