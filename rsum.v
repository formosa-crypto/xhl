(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import cardinality fsbigop.
From mathcomp.finmap    Require Import finmap.
From mathcomp.reals     Require Import reals.
From mathcomp.classical Require Import filter.
From mathcomp.analysis  Require Import esum counting_distr ereal.
From mathcomp.analysis  Require Import sequences normedtype topology.
                        Require Import misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

Section RSum.
Context {R : realType} {T : choiceType}.

Implicit Types (f g : T -> R).

Definition rsum f : R := fine (\esum_(x in [set: T]) (f x)%:E).

Lemma eq_rsum f g : f =1 g -> rsum f = rsum g.
Proof.
by move=> eq; rewrite /rsum; congr fine; apply: eq_esum => x _; rewrite eq.
Qed.

Lemma rsum0 : rsum (fun _ : T => 0) = 0.
Proof.
rewrite /rsum (eq_esum _ _ (fun _ => 0%E)); first by [].
by rewrite esum0.
Qed.

Lemma ge0_rsum f : (forall x, 0 <= f x) -> 0 <= rsum f.
Proof.
move=> f0; rewrite /rsum fine_ge0 //.
by apply: esum_ge0 => x _; rewrite lee_fin.
Qed.

Lemma rsumE f : esummable [set: T] (EFin \o f) ->
  (rsum f)%:E = \esum_(x in [set: T]) (f x)%:E.
Proof.
move=> sf; rewrite /rsum fineK //.
by apply: (esummable_esum_fin_num sf).
Qed.

Lemma esum_seq_le f z : (forall x, 0 <= f x) ->
  (forall J : seq T, uniq J -> \sum_(j <- J) f j <= z) ->
  (\esum_(x in [set: T]) (f x)%:E <= z%:E)%E.
Proof.
move=> f0 h; rewrite ge0_esum; first by move=> x _; rewrite lee_fin.
apply: ge_ereal_sup => _ [B [finB _] <-].
rewrite fsbig_finite; first exact: finB.
by rewrite sumEFin lee_fin; apply/h/fset_uniq.
Qed.

Lemma esummable_ge0_le f z : (forall x, 0 <= f x) ->
  (\esum_(x in [set: T]) (f x)%:E <= z%:E)%E ->
  esummable [set: T] (EFin \o f).
Proof.
move=> f0 h; rewrite esummableE.
rewrite (eq_esum _ _ (fun x => (f x)%:E)).
+ by move=> x _ /=; rewrite (ger0_norm (f0 x)).
rewrite ge0_fin_numE; first by apply: esum_ge0 => x _; rewrite lee_fin.
by apply: (le_lt_trans h); rewrite ltry.
Qed.

Lemma rsum_le f z : (forall x, 0 <= f x) ->
  (forall J : seq T, uniq J -> \sum_(j <- J) f j <= z) -> rsum f <= z.
Proof.
move=> f0 h; have key := esum_seq_le f0 h.
by rewrite -lee_fin rsumE // (esummable_ge0_le f0 key).
Qed.

Lemma gerfinseq_rsum f (r : seq T) : uniq r ->
  (forall x, 0 <= f x) -> esummable [set: T] (EFin \o f) ->
  \sum_(j <- r) f j <= rsum f.
Proof.
move=> uqr f0 sf; rewrite -lee_fin rsumE // -sumEFin.
apply: esum_ge; first by move=> x _; rewrite lee_fin.
have pr : perm_eq (fset_set ([set` r])%classic) r.
+ apply: uniq_perm; [exact: fset_uniq | exact: uqr |].
  move=> i; rewrite in_fset_set; first exact: finite_seq.
  by rewrite mem_setE.
exists ([set` r])%classic; first by split; [exact: finite_seq | by []].
rewrite fsbig_finite; first exact: finite_seq.
by rewrite (perm_big r pr).
Qed.

Lemma rsumZ f c : (forall x, 0 <= f x) ->
  rsum (fun x => c * f x) = c * rsum f.
Proof.
move=> f0; rewrite /rsum.
rewrite (eq_esum _ _ (fun x => (c%:E * (f x)%:E)%E)); first by move=> x _.
rewrite esumZ; first by move=> x _; rewrite lee_fin.
by rewrite fineMl.
Qed.

Lemma rsumB f g : (forall x, 0 <= g x <= f x) ->
  esummable [set: T] (EFin \o f) ->
  rsum (fun x => f x - g x) = rsum f - rsum g.
Proof.
move=> gf sf.
have sg : esummable [set: T] (EFin \o g).
+ apply: (le_esummable (g := EFin \o f)) => // x _.
  by rewrite /= !lee_fin; exact: gf x.
have ff := esummable_esum_fin_num sf.
have fg := esummable_esum_fin_num sg.
have E : \esum_(x in [set: T]) ((f x - g x)%:E)
       = ((\esum_(x in [set: T]) (f x)%:E)
          - (\esum_(x in [set: T]) (g x)%:E))%E.
+ rewrite -(esummable_esumB sf sg); apply: eq_esum => x _; exact: EFinB.
by rewrite /rsum E fineB.
Qed.

Lemma le_rsum f g : (forall x, 0 <= f x <= g x) ->
  esummable [set: T] (EFin \o g) -> rsum f <= rsum g.
Proof.
move=> fg sg; have sf : esummable [set: T] (EFin \o f).
  apply: (le_esummable (g := EFin \o g)) => // x _.
  by rewrite /= !lee_fin; have /andP[-> ->] := fg x.
rewrite -lee_fin !rsumE //; apply: le_esum => x _.
by rewrite lee_fin; have /andP[_ ->] := fg x.
Qed.

End RSum.

Lemma rsum_fin {R : realType} {I : finType} (f : I -> R) :
  (forall i, 0 <= f i) -> rsum f = \sum_i f i.
Proof.
move=> f0; rewrite /rsum (esum_fset finite_finset).
- by move=> i _; rewrite lee_fin.
by rewrite sum_eq_set sumEFin.
Qed.

Lemma rsum_finseq {R : realType} {T : choiceType} (f : T -> R) (r : seq T) :
  uniq r -> (forall x, 0 <= f x) -> (forall x, f x != 0 -> x \in r) ->
  rsum f = \sum_(x <- r) f x.
Proof.
move=> uqr f0 supp.
have fin : finite_set ([set` r])%classic by exact: finite_seq.
have pr : perm_eq (fset_set ([set` r])%classic) r.
+ apply: uniq_perm; [exact: fset_uniq | exact: uqr |].
  by move=> i; rewrite in_fset_set // mem_setE.
rewrite /rsum (esumID ([set` r])%classic [set: T]);
  first by move=> ? _; rewrite lee_fin.
rewrite !setTI.
have -> : \esum_(x in ~` ([set` r])%classic) ((f x)%:E) = 0%E.
+ apply: esum1 => x xNr.
  have -> : f x = 0; last by [].
  apply/eqP/negPn/negP => nz; apply: xNr.
  exact: supp nz.
rewrite adde0 esum_fset // ; first by move=> i _; rewrite lee_fin.
by rewrite fsbig_finite // (perm_big r pr) sumEFin.
Qed.

Lemma le1_rsum {R : realType} {T : choiceType} (mu : {distr T / R}) :
  rsum mu <= 1.
Proof.
by rewrite -lee_fin (rsumE (summable_mu mu)); exact: le1_mu.
Qed.

Lemma prE_rsum {R : realType} {T : choiceType}
    (mu : {distr T / R}) (E : pred T) :
  \P_[mu] E = rsum (fun x => (E x)%:R * mu x).
Proof. by []. Qed.

Lemma dfstE_rsum {R : realType} {T U : choiceType}
    (mu : {distr (T * U)%type / R}) x :
  dfst mu x = rsum (fun y => mu (x, y)).
Proof. by rewrite dfstE. Qed.

Lemma dsndE_rsum {R : realType} {T U : choiceType}
    (mu : {distr (T * U)%type / R}) y :
  dsnd mu y = rsum (fun x => mu (x, y)).
Proof. by rewrite dsndE. Qed.

Lemma dfstE_fin {R : realType} {T U : finType}
    (mu : {distr (T * U)%type / R}) x :
  dfst mu x = \sum_y mu (x, y).
Proof.
have -> : dfst mu x = rsum (fun y => mu (x, y)) by rewrite dfstE.
by rewrite rsum_fin // => ?; exact: ge0_mu.
Qed.

Lemma dsndE_fin {R : realType} {T U : finType}
    (mu : {distr (T * U)%type / R}) y :
  dsnd mu y = \sum_x mu (x, y).
Proof.
have -> : dsnd mu y = rsum (fun x => mu (x, y)) by rewrite dsndE.
by rewrite rsum_fin // => ?; exact: ge0_mu.
Qed.

Lemma rsum_image {R : realType} {T U : choiceType} (g : U -> T) (f : T -> R) :
  injective g -> (forall x, (forall u, g u <> x) -> f x = 0) ->
  (forall x, 0 <= f x) -> rsum f = rsum (f \o g).
Proof.
move=> ginj f0 fge0; rewrite /rsum; congr fine.
rewrite (esumID (g @` [set: U]) [set: T]); first by move=> ? _; rewrite lee_fin.
rewrite !setTI.
have -> : \esum_(x in ~` (g @` [set: U])) ((f x)%:E) = 0%E.
+ apply: esum1 => x xNim.
  have -> : f x = 0 by apply: f0 => u gu; apply: xNim; exists u.
  by [].
rewrite adde0.
by rewrite (esum_image [set: U] g (fun x => (f x)%:E)) // => x y _ _; exact: ginj.
Qed.

Lemma rsum_pair {R : realType} {T U : choiceType} (f : T * U -> R) :
  (forall x, 0 <= f x) ->
  (forall x, esummable [set: U] (EFin \o (fun y => f (x, y)))) ->
  rsum f = rsum (fun x => rsum (fun y => f (x, y))).
Proof.
move=> f0 sfx; rewrite /rsum; congr fine.
have dom : ([set: T] `*`` (fun _ : T => [set: U]))%classic
         = @setT (T * U)%type.
+ by rewrite predeqE => -[x y]; split.
transitivity (\esum_(x in [set: T]) \esum_(y in [set: U]) (f (x, y))%:E);
  last by apply: eq_esum => x _; rewrite -(rsumE (sfx x)).
rewrite (esum_esum (f := fun x y => (f (x, y))%:E));
  first by move=> ?? _ _; rewrite lee_fin.
by rewrite dom; apply: eq_esum => -[x y] _.
Qed.

Lemma rsum_pair_swap {R : realType} {T U : choiceType} (f : T * U -> R) :
  (forall x, 0 <= f x) ->
  (forall y, esummable [set: T] (EFin \o (fun x => f (x, y)))) ->
  rsum f = rsum (fun y => rsum (fun x => f (x, y))).
Proof.
move=> f0 sfy; rewrite /rsum; congr fine.
have dom : ([set: T] `*`` (fun _ : T => [set: U]))%classic
         = @setT (T * U)%type.
+ by rewrite predeqE => -[x y]; split.
transitivity (\esum_(y in [set: U]) \esum_(x in [set: T]) (f (x, y))%:E);
  last by apply: eq_esum => y _; rewrite -(rsumE (sfy y)).
rewrite -(@exchange_esum R T U [set: T] [set: U]
            (fun x y => (f (x, y))%:E)); first by move=> ??; rewrite lee_fin.
rewrite (esum_esum (f := fun x y => (f (x, y))%:E));
  first by move=> ?? _ _; rewrite lee_fin.
by rewrite dom; apply: eq_esum => -[x y] _.
Qed.

Lemma rsum_option {R : realType} {T : choiceType} (f : option T -> R) :
  esummable [set: option T] (EFin \o f) ->
  rsum f = rsum (f \o some) + f None.
Proof.
move=> sf; have sfs := esummable_option sf.
rewrite /rsum (esum_option sf) fineD //.
by apply: (esummable_esum_fin_num sfs).
Qed.
