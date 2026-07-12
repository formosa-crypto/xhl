(* -------------------------------------------------------------------- *)
(* ------- *)           Require Import Setoid Morphisms.
From mathcomp           Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr.
From xhl.pwhile Require Import notations inhabited pwhile psemantic passn range.
From xhl.hl Require Import hl.

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
Local Notation dmem  := (Distr cmem).
Local Notation dassn := (pred  dmem).

Implicit Types P Q S : dassn.
Implicit Types c : cmd.
Implicit Types mu : dmem.

(* -------------------------------------------------------------------- *)
Local Notation iwhilen k b c := (iterc k (IfT b then c)).

(* -------------------------------------------------------------------- *)
Inductive sellora : dassn -> dassn -> cmd -> Prop :=
| ESkip P : sellora P P skip

| EAbort P : sellora P (□ pred0) abort

| ESeq S P Q c1 c2 :
    sellora P S c1 -> sellora S Q c2 -> sellora P Q (c1 ;; c2)

| EConseq P' Q' P Q c :
       (forall mu, mu \in P  -> mu \in P')
    -> (forall mu, mu \in Q' -> mu \in Q )
    -> sellora P' Q' c
    -> sellora P  Q  c

| ESem c1 P Q c2 :
       (forall mu, mu \in P -> dssem c1 mu = dssem c2 mu)
    -> sellora P Q c1 -> sellora P Q c2

| ESemCond P Q (e : expr bool) c1 c2 :
       (forall mu, mu \in P -> forall m, m \in dinsupp mu -> `[{ e }] m)
    -> sellora P Q c1 -> sellora P Q (If e then c1 else c2)

| ESemCondF P Q (e : expr bool) c1 c2 :
       (forall mu, mu \in P -> forall m, m \in dinsupp mu -> `[{ ~~ e }] m)
    -> sellora P Q c2 -> sellora P Q (If e then c1 else c2)

| EDframe P c :
    separated (mod c) P -> lossless predT c -> sellora P P c

| EAnd P Q1 Q2 c :
    sellora P Q1 c -> sellora P Q2 c -> sellora P (Q1 /\ Q2)%A c

| EOr P1 P2 c Q :
    sellora P1 Q c -> sellora P2 Q c -> sellora (P1 \/ P2)%A Q c

| EAssign {t : IhbType.type} P (x : vars t) (e : expr t) :
    sellora (P.[fun mu => dssem (x <<- e) mu])%A P (x <<- e)
  
| ESample {t : IhbType.type} P (x : vars t) (d : dexpr t) :
    sellora (P.[fun mu => dssem (x <$- d) mu])%A P (x <$- d)

| ECond P P' Q Q' e c1 c2 :
    let SP := (P /\ □ [pred m | `[{    e }] m])%A in
    let SQ := (Q /\ □ [pred m | `[{ ~~ e }] m])%A in
  
       sellora SP P' c1
    -> sellora SQ Q' c2
    -> sellora (SP ⊕ SQ) (P' ⊕ Q') (If e then c1 else c2)

| EWhileDClosed P b c :
       dclosed P -> sellora P P (IfT b then c)
    -> sellora P (P /\ □ `[{~~ b}])%A (While b Do c)

| EWhileTClosed (P Q : nat -> dassn) Qinf b c :
       (forall n, sellora (P n) (P n.+1) (IfT b then c))
    -> (forall n, sellora (P n) (Q n) (IfT b then abort))
    -> tclosed Q Qinf
    -> sellora (P 0%N) (Qinf /\ □ `[{~~ b}])%A (While b Do c)

| EWhileUClosed (P Q : nat -> dassn) Qinf b c :
       (forall n, sellora (P n) (P n.+1) (IfT b then c))
    -> (forall n, sellora (P n) (Q n) (IfT b then abort))
    -> uclosed Q Qinf
    -> sellora (P 0%N) (Qinf /\ □ `[{~~ b}])%A (While b Do c)

| EWhileCertainCT P b c :
    (forall mu, mu \in P -> exists k,
       \P_[dssem (iwhilen k b c) mu] [eta `[{ b }]] = 0)
  -> sellora P P (IfT b then c)
  -> sellora P (P /\ □ `[{ ~~ b}])%A (While b Do c)

| EWhileCertain (P : nat -> dassn) k e c :
     (forall n, sellora (P n) (P n.+1) (IfT e then c))
  -> (forall mu, P 0%N mu -> dssem (While e Do c) =
                             dssem (iterc k (IfT e then c)))
  -> sellora (P 0%N) (P k /\ □ `[{~~ e}])%A (While e Do c)

| ESplit P P' Q Q' c :
    sellora P Q c -> sellora P' Q' c -> sellora (P) (Q) c.
