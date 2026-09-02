From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp           Require finmap.
From xhl                Require Import misc rsum.
From xhl.pwhile         Require Import notations inhabited pwhile psemantic passn range.
From xhl.prhl           Require Import prhl.
From xhl.ehl            Require Import ehl_stmt.
From xhl.hl             Require hl.
From xhl.erhl           Require Import erhl_stmt.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope sem_scope.

Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Local Notation cmd := (@cmd_ ident cmem ident).

Implicit Types (f g h : rcond) (c d : cmd) (cl : rphi) (ps : psi).

(* ==================================================================== *)
(* Swapping a procedure context, needed by [H_Swap].                     *)
(* ==================================================================== *)
Definition rphi_swap (cl : rphi) : rphi :=
  fun o1 o2 => (rswap (get_pre (cl o2 o1)), rswap2 (get_post (cl o2 o1))).

(* ==================================================================== *)
Section Logic.

Inductive derivable : psi -> rphi -> rcond -> cmd -> cmd -> rcond -> Prop :=

(* ---------------------------------------------------------------- *)
(* Two-sided rules (Figure 3, top).                                  *)
(* ---------------------------------------------------------------- *)

(* [abort] denotes [dnull], whose star-extension is [dunit None]; the  *)
(* star-coupling is then forced and the post-expectation contributes   *)
(* nothing, so the right-hand program may be arbitrary.                *)
| H_Abort : forall f g c cl ps,
    (forall m, (0 <= f m)%E) ->
    derivable ps cl f abort c g

(* [Skip]; pwhile's [skip] is the paper's empty program [eps]. *)
| H_Skip : forall f cl ps,
    derivable ps cl f skip skip f

(* [Asgn] *)
| H_Asgn : forall {T1 T2 : IhbType.type}
    (x : vars T1) (e1 : expr T1) (y : vars T2) (e2 : expr T2) f cl ps,
    derivable ps cl
      (fun m : rmem => f (m.[~1 x <- `[{e1}] m.1]).[~2 y <- `[{e2}] m.2])
      (x <<- e1) (y <<- e2) f

| H_GAsgn : forall {T1 T2 : IhbType.type}
    (x : vars T1) (e1 : expr T1) (y : vars T2) (e2 : expr T2) f cl ps,
    derivable ps cl
      (fun m : rmem => f (m.{x#'1 <- `[{e1}] m.1}).{y#'2 <- `[{e2}] m.2})
      (G x <<- e1) (G y <<- e2) f

(* [Sample]: the pre-expectation is computed from a coupling [nu] of    *)
(* the two sampling instructions, supplied by the user.                 *)
| H_Sample : forall {T1 T2 : IhbType.type}
    (x : vars T1) (d1 : dexpr T1) (y : vars T2) (d2 : dexpr T2)
    (nu : rmem -> Distr (T1 * T2)%type) f cl ps,
    (forall m : rmem, iscoupling (`[{d1}] m.1) (`[{d2}] m.2) (nu m)) ->
    let g := fun m : rmem =>
      espe (\dlet_(v <- nu m) dunit (m.[~1 x <- v.1]).[~2 y <- v.2]) f in
    derivable ps cl g (x <$- d1) (y <$- d2) f

| H_Block : forall f g bs1 c rs1 bs2 d rs2 cl ps,
    (forall m, (0 <= g m)%E) ->
    (forall m : rmem,
       derivable ps cl
         (bound (fun _ => f m) (minit m.1 bs1, minit m.2 bs2)) c d
         (fun m'' : rmem => g (mret m.1 m''.1 rs1, mret m.2 m''.2 rs2))) ->
    derivable ps cl f (Block bs1 Do c Return rs1) (Block bs2 Do d Return rs2) g

(* [If]: the classical part of the pre-expectation forces both programs *)
(* to take the same branch.                                             *)
| H_If : forall f g (e1 e2 : bexpr) c1 c2 d1 d2 cl ps,
    derivable ps cl (rlift `[{    e1#'1 &&    e2#'2 }] f) c1 d1 g ->
    derivable ps cl (rlift `[{ ~~ e1#'1 && ~~ e2#'2 }] f) c2 d2 g ->
    derivable ps cl (rlift `[{ e1#'1 =b e2#'2 }] f)
      (If e1 then c1 else c2) (If e2 then d1 else d2) g

(* [While]: [f] is the quantitative invariant, and the classical part    *)
(* keeps the two loops in lockstep.                                      *)
| H_While : forall f (e1 e2 : bexpr) c d cl ps,
    (forall m, (0 <= f m)%E) ->
    derivable ps cl (rlift `[{ e1#'1 && e2#'2 }] f) c d
                    (rlift `[{ e1#'1 =b e2#'2 }] f) ->
    derivable ps cl (rlift `[{ e1#'1 =b e2#'2 }] f)
      (While e1 Do c) (While e2 Do d)
      (rlift `[{ ~~ e1#'1 && ~~ e2#'2 }] f)

| H_Seq : forall f g h c1 c2 d1 d2 cl ps,
    (forall m, (0 <= g m)%E) ->
    derivable ps cl h c2 d2 g ->
    derivable ps cl f c1 d1 h ->
    derivable ps cl f (c1 ;; c2) (d1 ;; d2) g

(* ---------------------------------------------------------------- *)
(* One-sided rules (Figure 3, middle).  Only the left-hand versions   *)
(* are primitive; the right-hand ones are derived through [H_Swap].   *)
(* ---------------------------------------------------------------- *)

| H_AsgnL : forall {T : IhbType.type} (x : vars T) (e : expr T) f cl ps,
    derivable ps cl (fun m : rmem => f m.[~1 x <- `[{e}] m.1])
      (x <<- e) skip f

| H_GAsgnL : forall {T : IhbType.type} (x : vars T) (e : expr T) f cl ps,
    derivable ps cl (fun m : rmem => f m.{x#'1 <- `[{e}] m.1})
      (G x <<- e) skip f

| H_SampleL : forall {T : IhbType.type} (x : vars T) (d : dexpr T) f cl ps,
    let g := fun m : rmem =>
      espe (\dlet_(v <- `[{d}] m.1) dunit m.[~1 x <- v]) f in
    derivable ps cl g (x <$- d) skip f

| H_BlockL : forall f g bs c rs d cl ps,
    (forall m, (0 <= g m)%E) ->
    (forall m : rmem,
       derivable ps cl (bound (fun _ => f m) (minit m.1 bs, m.2)) c d
         (fun m'' : rmem => g (mret m.1 m''.1 rs, m''.2))) ->
    derivable ps cl f (Block bs Do c Return rs) d g

| H_IfL : forall f g (e : bexpr) c1 c2 d cl ps,
    derivable ps cl (rlift `[{    e#'1 }] f) c1 d g ->
    derivable ps cl (rlift `[{ ~~ e#'1 }] f) c2 d g ->
    derivable ps cl f (If e then c1 else c2) d g

| H_WhileL : forall f (e : bexpr) c cl ps,
    (forall m, (0 <= f m)%E) ->
    derivable ps cl (rlift `[{ e#'1 }] f) c skip f ->
    derivable ps cl f (While e Do c) skip (rlift `[{ ~~ e#'1 }] f)

(* ---------------------------------------------------------------- *)
(* Logical rules (Figure 3, bottom).                                  *)
(* ---------------------------------------------------------------- *)

| H_Swap : forall f g c d cl ps,
    derivable ps (rphi_swap cl) (rswap f) d c (rswap g) ->
    derivable ps cl f c d g

(* [Conseq], in the [psharp] (infimum) formulation of the paper. *)
| H_Consequence : forall f f' g g' c d cl ps,
    derivable ps cl f' c d g' ->
    (forall (m : rmem) (mu1 mu2 : Distr cmem),
       (psharp g' mu1 mu2 <= f' m)%E -> (psharp g mu1 mu2 <= f m)%E) ->
    derivable ps cl f c d g

(* [Nmod-L]: the paper's logical variable [v] is the *initial* value of  *)
(* [x<1>], so quantifying over [v] and guarding the pre-expectation      *)
(* with [x<1> = v] replaces it.                                         *)
| H_NmodL : forall {T : IhbType.type} (x : vars T) f g c d cl ps,
    nocall c ->
    (Tagged vars x) \notin hl.mod c ->
    (forall v : T,
       derivable ps cl (rlift (fun m : rmem => `[< (m.1.[x])%M = v >]) f) c d
         (fun m' : rmem => g m'.[~1 x <- v])) ->
    derivable ps cl f c d g

(* [Strassen] (both directions of the paper's double line).  The set     *)
(* [M] of memories is universally quantified at the Coq level.           *)
| H_Strassen : forall (Rl : rel cmem) f c d cl ps,
    lossless predT c -> lossless predT d ->
    (forall M : pred cmem,
       derivable ps cl (fun m : rmem => (1 + f m)%E) c d
         (fun m' : rmem => ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E)) ->
    derivable ps cl f c d (fun m' : rmem => ((~~ Rl m'.1 m'.2)%:R)%:E)

| H_StrassenInv : forall (Rl : rel cmem) f c d cl ps (M : pred cmem),
    lossless predT c -> lossless predT d ->
    derivable ps cl f c d (fun m' : rmem => ((~~ Rl m'.1 m'.2)%:R)%:E) ->
    derivable ps cl (fun m : rmem => (1 + f m)%E) c d
      (fun m' : rmem => ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E)

| H_krhl : forall f g c d cl ps,
    derivable2 ps cl f c d (fun _ => g) -> derivable ps cl f c d g

(* ================================================================== *)
(* The generic judgment: the post-expectation reads the initial pair   *)
(* of memories.  Only the bridge, the procedure rules and the rule of  *)
(* consequence live here.                                              *)
(* ================================================================== *)
with derivable2 : psi -> rphi -> rcond -> cmd -> cmd -> rcond2 -> Prop :=

| H_rhl : forall f (g : rcond2) c d cl ps,
    (forall s0 : rmem, derivable ps cl (bound f s0) c d (g s0)) ->
    derivable2 ps cl f c d g

(* [Call] and [Call-L] at once: [None] denotes the identity procedure,   *)
(* i.e. [skip].                                                         *)
| H_call : forall cl (o1 o2 : option ident) ps,
    derivable2 ps cl
      (get_pre (cl o1 o2)) (ocmd o1) (ocmd o2) (get_post (cl o1 o2))

(* [ProcInd] *)
| H_rec : forall f (g : rcond2) c d (cl cl' : rphi) ps',
    (forall o1 o2 ps,
       derivable2 ps cl (get_pre (cl o1 o2))
         (obody ps' o1) (obody ps' o2) (get_post (cl o1 o2))) ->
    (forall ps, derivable2 ps cl f c d g) ->
    derivable2 ps' cl' f c d g

(* [Conseq] on generic judgments. *)
| H_adapt : forall (f1 f2 : rcond) (g1 g2 : rcond2) c d cl ps,
    derivable2 ps cl f2 c d g2 ->
    (forall (m : rmem) (mu1 mu2 : Distr cmem),
       (psharp (g2 m) mu1 mu2 <= f2 m)%E ->
       (psharp (g1 m) mu1 mu2 <= f1 m)%E) ->
    derivable2 ps cl f1 c d g1.

Scheme derivable_min := Minimality for derivable Sort Prop
  with derivable2_min := Minimality for derivable2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

End Logic.

(* ==================================================================== *)
Section Sound.

Section Rules.
Context (ps : psi).

Notation erhl  := (erhl_ ps).
Notation kerhl := (kerhl_ ps).

(* Extraction of the star-coupling witnessing a valid judgment,          *)
(* mirroring [prhl.prhlw].                                              *)
Lemma erhlw f c d g (m : rmem) :
  erhl f c d g ->
  { nu | scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
       & (espe nu (rstar g) <= f m)%E }.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Lemma erhl_abort f g c : (forall m, (0 <= f m)%E) -> erhl f abort c g.
Proof. Admitted.

Lemma erhl_skip f g : (forall m, (g m <= f m)%E) -> erhl f skip skip g.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Lemma erhl_assign {T1 T2 : IhbType.type}
    (x : vars T1) (e1 : expr T1) (y : vars T2) (e2 : expr T2) f :
  erhl (fun m : rmem => f (m.[~1 x <- `[{e1}] m.1]).[~2 y <- `[{e2}] m.2])
       (x <<- e1) (y <<- e2) f.
Proof. Admitted.

Lemma erhl_gassign {T1 T2 : IhbType.type}
    (x : vars T1) (e1 : expr T1) (y : vars T2) (e2 : expr T2) f :
  erhl (fun m : rmem => f (m.{x#'1 <- `[{e1}] m.1}).{y#'2 <- `[{e2}] m.2})
       (G x <<- e1) (G y <<- e2) f.
Proof. Admitted.

Lemma erhl_sample {T1 T2 : IhbType.type}
    (x : vars T1) (d1 : dexpr T1) (y : vars T2) (d2 : dexpr T2)
    (nu : rmem -> Distr (T1 * T2)%type) f :
  (forall m : rmem, iscoupling (`[{d1}] m.1) (`[{d2}] m.2) (nu m)) ->
  erhl (fun m : rmem =>
          espe (\dlet_(v <- nu m) dunit (m.[~1 x <- v.1]).[~2 y <- v.2]) f)
       (x <$- d1) (y <$- d2) f.
Proof. Admitted.

Lemma erhl_block f g bs1 c rs1 bs2 d rs2 :
  (forall m, (0 <= g m)%E) ->
  (forall m : rmem,
     erhl (bound (fun _ => f m) (minit m.1 bs1, minit m.2 bs2)) c d
          (fun m'' : rmem => g (mret m.1 m''.1 rs1, mret m.2 m''.2 rs2))) ->
  erhl f (Block bs1 Do c Return rs1) (Block bs2 Do d Return rs2) g.
Proof. Admitted.

Lemma erhl_if f g (e1 e2 : bexpr) c1 c2 d1 d2 :
  erhl (rlift `[{    e1#'1 &&    e2#'2 }] f) c1 d1 g ->
  erhl (rlift `[{ ~~ e1#'1 && ~~ e2#'2 }] f) c2 d2 g ->
  erhl (rlift `[{ e1#'1 =b e2#'2 }] f)
       (If e1 then c1 else c2) (If e2 then d1 else d2) g.
Proof. Admitted.

Lemma erhl_while f (e1 e2 : bexpr) c d :
  (forall m, (0 <= f m)%E) ->
  erhl (rlift `[{ e1#'1 && e2#'2 }] f) c d (rlift `[{ e1#'1 =b e2#'2 }] f) ->
  erhl (rlift `[{ e1#'1 =b e2#'2 }] f)
       (While e1 Do c) (While e2 Do d)
       (rlift `[{ ~~ e1#'1 && ~~ e2#'2 }] f).
Proof. Admitted.

Lemma erhl_seq f g h c1 c2 d1 d2 :
  (forall m, (0 <= g m)%E) ->
  erhl f c1 d1 h -> erhl h c2 d2 g -> erhl f (c1 ;; c2) (d1 ;; d2) g.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* One-sided rules                                                       *)
(* -------------------------------------------------------------------- *)

Lemma erhl_assignL {T : IhbType.type} (x : vars T) (e : expr T) f :
  erhl (fun m : rmem => f m.[~1 x <- `[{e}] m.1]) (x <<- e) skip f.
Proof. Admitted.

Lemma erhl_gassignL {T : IhbType.type} (x : vars T) (e : expr T) f :
  erhl (fun m : rmem => f m.{x#'1 <- `[{e}] m.1}) (G x <<- e) skip f.
Proof. Admitted.

Lemma erhl_sampleL {T : IhbType.type} (x : vars T) (d : dexpr T) f :
  erhl (fun m : rmem => espe (\dlet_(v <- `[{d}] m.1) dunit m.[~1 x <- v]) f)
       (x <$- d) skip f.
Proof. Admitted.

Lemma erhl_blockL f g bs c rs d :
  (forall m, (0 <= g m)%E) ->
  (forall m : rmem,
     erhl (bound (fun _ => f m) (minit m.1 bs, m.2)) c d
          (fun m'' : rmem => g (mret m.1 m''.1 rs, m''.2))) ->
  erhl f (Block bs Do c Return rs) d g.
Proof. Admitted.

Lemma erhl_ifL f g (e : bexpr) c1 c2 d :
  erhl (rlift `[{    e#'1 }] f) c1 d g ->
  erhl (rlift `[{ ~~ e#'1 }] f) c2 d g ->
  erhl f (If e then c1 else c2) d g.
Proof. Admitted.

Lemma erhl_whileL f (e : bexpr) c :
  (forall m, (0 <= f m)%E) ->
  erhl (rlift `[{ e#'1 }] f) c skip f ->
  erhl f (While e Do c) skip (rlift `[{ ~~ e#'1 }] f).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* Logical rules                                                         *)
(* -------------------------------------------------------------------- *)

Lemma erhl_swap f g c d :
  erhl (rswap f) d c (rswap g) -> erhl f c d g.
Proof. Admitted.

Lemma erhl_conseq f f' g g' c d :
  erhl f' c d g' ->
  (forall (m : rmem) (mu1 mu2 : Distr cmem),
     (psharp g' mu1 mu2 <= f' m)%E -> (psharp g mu1 mu2 <= f m)%E) ->
  erhl f c d g.
Proof. Admitted.

Lemma kerhl_conseq f1 f2 (g1 g2 : rcond2) c d :
  kerhl f2 c d g2 ->
  (forall (m : rmem) (mu1 mu2 : Distr cmem),
     (psharp (g2 m) mu1 mu2 <= f2 m)%E -> (psharp (g1 m) mu1 mu2 <= f1 m)%E) ->
  kerhl f1 c d g1.
Proof. Admitted.

Lemma erhl_nmodL {T : IhbType.type} (x : vars T) f g c d :
  nocall c ->
  (Tagged vars x) \notin hl.mod c ->
  (forall v : T,
     erhl (rlift (fun m : rmem => `[< (m.1.[x])%M = v >]) f) c d
          (fun m' : rmem => g m'.[~1 x <- v])) ->
  erhl f c d g.
Proof. Admitted.

Lemma erhl_strassen (Rl : rel cmem) f c d :
  lossless predT c -> lossless predT d ->
  (forall M : pred cmem,
     erhl (fun m : rmem => (1 + f m)%E) c d
          (fun m' : rmem => ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E)) ->
  erhl f c d (fun m' : rmem => ((~~ Rl m'.1 m'.2)%:R)%:E).
Proof. Admitted.

Lemma erhl_strassenInv (Rl : rel cmem) f c d (M : pred cmem) :
  lossless predT c -> lossless predT d ->
  erhl f c d (fun m' : rmem => ((~~ Rl m'.1 m'.2)%:R)%:E) ->
  erhl (fun m : rmem => (1 + f m)%E) c d
       (fun m' : rmem => ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* Procedures                                                            *)
(* -------------------------------------------------------------------- *)

(** Judgment on a command, under a procedure context **)
Definition rhoare_triple_ctx (cl : rphi) (ps' : psi)
    (f : rcond) (g : rcond2) (c d : cmd) :=
  (forall o1 o2, kerhl_ ps' (get_pre (cl o1 o2))
                   (ocmd o1) (ocmd o2) (get_post (cl o1 o2))) ->
  kerhl_ ps' f c d g.

(** Judgment on the procedures themselves, under a procedure context **)
Definition rhoare_triple_proc_ctx (cl : rphi) (ps_init : psi) :=
  forall o1 o2 ps',
    rhoare_triple_ctx cl ps'
      (get_pre (cl o1 o2)) (get_post (cl o1 o2))
      (obody ps_init o1) (obody ps_init o2).

Lemma recursive_proc (ps' : psi) (cl' : rphi) :
  rhoare_triple_proc_ctx cl' ps' ->
  (forall o1 o2, kerhl_ ps' (get_pre (cl' o1 o2))
                   (ocmd o1) (ocmd o2) (get_post (cl' o1 o2))).
Proof. Admitted.

Theorem recursion_rhoare_triple :
  forall f (g : rcond2) c d (cl : rphi) (ps' : psi),
    rhoare_triple_proc_ctx cl ps' ->
    rhoare_triple_ctx cl ps' f g c d ->
    kerhl_ ps' f c d g.
Proof. Admitted.

End Rules.

(* -------------------------------------------------------------------- *)
Definition valid_cl (cl : rphi) (ps : psi) :=
  forall o1 o2, kerhl_ ps (get_pre (cl o1 o2))
                  (ocmd o1) (ocmd o2) (get_post (cl o1 o2)).

(* Theorem 4.3 / 6.1(1).  Proof deferred: it goes by [derivable_mut] off *)
(* the rule lemmas above.                                                *)
Theorem soundness :
  (forall ps cl f c d g, derivable  ps cl f c d g ->
     valid_cl cl ps -> erhl_  ps f c d g) /\
  (forall ps cl f c d (g : rcond2), derivable2 ps cl f c d g ->
     valid_cl cl ps -> kerhl_ ps f c d g).
Proof. Admitted.

Corollary rhoare_sound0 f c d g ps :
  derivable ps rcl_empty f c d g -> erhl_ ps f c d g.
Proof. Admitted.

Corollary krhoare_sound0 f c d (g : rcond2) ps :
  derivable2 ps rcl_empty f c d g -> kerhl_ ps f c d g.
Proof. Admitted.

End Sound.

#[export] Hint Resolve erhl_skip erhl_abort erhl_assign erhl_assignL
  erhl_gassign erhl_gassignL erhl_sample erhl_sampleL : erhl.

(* ==================================================================== *)
(* Derived right-sided rules, and the embedding of pRHL (Lemma 5.2).     *)
(* ==================================================================== *)
Section Derived.
Context (ps : psi).

Notation erhl := (erhl_ ps).

Lemma erhl_assignR {T : IhbType.type} (x : vars T) (e : expr T) f :
  erhl (fun m : rmem => f m.[~2 x <- `[{e}] m.2]) skip (x <<- e) f.
Proof. Admitted.

Lemma erhl_gassignR {T : IhbType.type} (x : vars T) (e : expr T) f :
  erhl (fun m : rmem => f m.{x#'2 <- `[{e}] m.2}) skip (G x <<- e) f.
Proof. Admitted.

Lemma erhl_sampleR {T : IhbType.type} (x : vars T) (d : dexpr T) f :
  erhl (fun m : rmem => espe (\dlet_(v <- `[{d}] m.2) dunit m.[~2 x <- v]) f)
       skip (x <$- d) f.
Proof. Admitted.

Lemma erhl_ifR f g (e : bexpr) d1 d2 c :
  erhl (rlift `[{    e#'2 }] f) c d1 g ->
  erhl (rlift `[{ ~~ e#'2 }] f) c d2 g ->
  erhl f c (If e then d1 else d2) g.
Proof. Admitted.

Lemma erhl_whileR f (e : bexpr) d :
  (forall m, (0 <= f m)%E) ->
  erhl (rlift `[{ e#'2 }] f) skip d f ->
  erhl f skip (While e Do d) (rlift `[{ ~~ e#'2 }] f).
Proof. Admitted.

Lemma erhl_nmodR {T : IhbType.type} (x : vars T) f g c d :
  nocall d ->
  (Tagged vars x) \notin hl.mod d ->
  (forall v : T,
     erhl (rlift (fun m : rmem => `[< (m.2.[x])%M = v >]) f) c d
          (fun m' : rmem => g m'.[~2 x <- v])) ->
  erhl f c d g.
Proof. Admitted.

(* Lemma 5.2: the semantic embedding of pRHL into eRHL, by               *)
(* contraposition.  Entry point for the applications of Section 5.       *)
Lemma prhl_erhl (P Q : rassn) c d :
  prhl_ ps P c d Q ->
  erhl (fun m : rmem => ((~~ P m)%:R)%:E) c d
       (fun m' : rmem => ((~~ Q m')%:R)%:E).
Proof. Admitted.

End Derived.
