(* -------------------------------------------------------------------- *)
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra   Require Import all_algebra.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Monoid.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Section PartitionBigSeq.
Context {R : Type} {idx : R} {op : com_law idx} (T U : eqType).
Context (p : T -> U) (r : seq.seq T) (F : T -> U -> R).

Lemma partition_big_seq : uniq r ->
  \big[op/idx]_(x <- r) F x (p x) =
    \big[op/idx]_(y <- undup [seq p x | x <- r])
      \big[op/idx]_(x <- [seq x <- r | p x == y]) F x y.
Proof.
move=> uq_r; set s := undup _; pose g y := [seq x <- r | p x == y].
suff h: perm_eq r (flatten [seq g y | y <- s]).
  rewrite (perm_big _ h) big_flatten big_map; apply/eq_bigr.
  move=> y _; rewrite !big_seq; apply/eq_bigr=> x.
  by rewrite mem_filter => /andP[/eqP <-].
apply/uniq_perm => //.
  have: uniq s by apply/undup_uniq. elim: s => //.
  move=> y s ih /andP[yNs /ih uq_s] /=; rewrite cat_uniq.
  rewrite uq_s filter_uniq ?andbT //=; apply/hasPn=> /= x.
  case/flatten_mapP=> y' /= y's; rewrite mem_filter.
  case/andP=> /eqP /esym y'E _; apply/contraL: y's.
  by rewrite {}y'E mem_filter=> /andP[/eqP -> _].
move=> x; apply/idP/idP.
  move=> xr; apply/flattenP=> /=; exists (g (p x)).
    by apply/map_f; rewrite mem_undup; apply/map_f.
  by rewrite mem_filter eqxx.
by case/flatten_mapP=> y _; rewrite mem_filter=> /andP[].
Qed.
End PartitionBigSeq.

(* -------------------------------------------------------------------- *)
Section PartitionBigSeqMul.
Context {R : ringType} (T U : eqType).
Context (p : T -> U) (r : seq.seq T) (F : T -> R) (G : U -> R).

Lemma partition_big_seq_mulr_suml : uniq r ->
  \sum_(x <- r) F x * G (p x) =
    \sum_(y <- undup [seq p x | x <- r])
      (\sum_(x <- [seq x <- r | p x == y]) F x) * G y.
Proof.
move=> uq_r; rewrite (partition_big_seq p (fun x y => F x * G y)) //=.
by apply/eq_bigr=> y _; rewrite mulr_suml.
Qed.

Lemma partition_big_seq_mulr_sumr : uniq r ->
  \sum_(x <- r) G (p x) * F x =
    \sum_(y <- undup [seq p x | x <- r])
      G y * (\sum_(x <- [seq x <- r | p x == y]) F x).
Proof.
move=> uq_r; rewrite (partition_big_seq p (fun x y => G y * F x)) //=.
by apply/eq_bigr=> y _; rewrite mulr_sumr.
Qed.
End PartitionBigSeqMul.
