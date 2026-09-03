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
From xhl.ehl            Require ehl.
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
    (forall m, (0 <= f m)%E) ->
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
    (forall m, (0 <= f m)%E) ->
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

(* The positivity side condition is needed to transport the expectation     *)
(* through [dswap] (via [eexp_dmargin]), as in [ehl.v]'s [H_Seq]/[H_While]. *)
| H_Swap : forall f g c d cl ps,
    (forall m, (0 <= g m)%E) ->
    derivable ps (rphi_swap cl) (rswap f) d c (rswap g) ->
    derivable ps cl f c d g

(* [Conseq], in the [psharp] (infimum) formulation of the paper. *)
| H_Consequence : forall f f' g g' c d cl ps,
    (forall m, (0 <= g m)%E) ->
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

(* The converse direction needs NO almost-sure-termination hypothesis, in     *)
(* contrast with [H_Strassen] above.  It reuses the star-coupling it is       *)
(* handed and only has to bound [\P_[nu] [predU T1 & T2]] by 1, which is      *)
(* [le1_pr] -- true of any distribution.  Forcing [lossless] here would make  *)
(* the rule needlessly weak, the more so as the repo has no lemma deriving    *)
(* [lossless] for any concrete command.                                      *)
| H_StrassenInv : forall (Rl : rel cmem) f c d cl ps (M : pred cmem),
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

(* [ProcInd].  The [rcl_post_pos] side condition plays the role of         *)
(* [ehl.v]'s [cl_cond2_independent]: it is what lets the internalised      *)
(* context [cl] be recognised as valid.                                    *)
| H_rec : forall f (g : rcond2) c d (cl cl' : rphi) ps',
    rcl_pre_pos cl -> rcl_post_pos cl -> rcl_skip_valid cl ->
    (forall o1 o2 ps,
       derivable2 ps cl (get_pre (cl o1 o2))
         (obody ps' o1) (obody ps' o2) (get_post (cl o1 o2))) ->
    (forall ps, derivable2 ps cl f c d g) ->
    derivable2 ps' cl' f c d g

(* [Conseq] on generic judgments. *)
| H_adapt : forall (f1 f2 : rcond) (g1 g2 : rcond2) c d cl ps,
    (forall m0 m, (0 <= g1 m0 m)%E) ->
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
Proof.
move=> h.
have: exists nu, scoupling (ssem_ ps c m.1) (ssem_ ps d m.2) nu
               /\ (espe nu (rstar g) <= f m)%E.
+ by case: (h m) => nu h1 h2; exists nu; split.
by case/cid => nu [h1 h2]; exists nu.
Qed.

(* -------------------------------------------------------------------- *)
(* [abort] denotes [dnull], whose star-extension is [dunit None].  The    *)
(* star-coupling is therefore forced to sit entirely on {None} x _, where *)
(* [rstar g] vanishes -- so the right-hand program is arbitrary.          *)
Lemma erhl_abort f g c : (forall m, (0 <= f m)%E) -> erhl f abort c g.
Proof.
move=> hf m.
exists (dmargin (fun o => (@None cmem, o)) (dstar (ssem_ ps c m.2))).
+ split; rewrite dmargin_comp /comp.
  * have -> : (fun o : option cmem => (@None cmem, o).1) = (fun=> @None cmem).
    - by [].
    rewrite ssem_abortE dstar_dnull.
    by apply/distr_eqP => o; rewrite dmarginE dletC dweight_dstar mul1r.
  have -> : (fun o : option cmem => (@None cmem, o).2) = id by [].
  by rewrite dmarginE dlet_dunit_id.
by rewrite espe_rstar_left0; exact: hf.
Qed.

Lemma erhl_skip f g : (forall m, (g m <= f m)%E) -> erhl f skip skip g.
Proof.
move=> h [m1 m2]; exists (dunit (Some m1, Some m2)).
+ by rewrite !ssemE; apply: scoupling_dunit.
by rewrite eexp_dunit /rstar; exact: h.
Qed.

(* -------------------------------------------------------------------- *)
Lemma erhl_assign {T1 T2 : IhbType.type}
    (x : vars T1) (e1 : expr T1) (y : vars T2) (e2 : expr T2) f :
  erhl (fun m : rmem => f (m.[~1 x <- `[{e1}] m.1]).[~2 y <- `[{e2}] m.2])
       (x <<- e1) (y <<- e2) f.
Proof.
move=> m.
set m' := ((m.[~1 x <- `[{e1}] m.1]).[~2 y <- `[{e2}] m.2] : rmem).
have h1 : ssem_ ps (x <<- e1) m.1 = dunit (m' # '1)%M.
+ by rewrite ssemE /m' !mselect_mset.
have h2 : ssem_ ps (y <<- e2) m.2 = dunit (m' # '2)%M.
+ by rewrite ssemE /m' !mselect_mset.
exists (dunit (Some m'.1, Some m'.2)).
+ by rewrite h1 h2; apply: scoupling_dunit.
by rewrite eexp_dunit /rstar -surjective_pairing.
Qed.

Lemma erhl_gassign {T1 T2 : IhbType.type}
    (x : vars T1) (e1 : expr T1) (y : vars T2) (e2 : expr T2) f :
  erhl (fun m : rmem => f (m.{x#'1 <- `[{e1}] m.1}).{y#'2 <- `[{e2}] m.2})
       (G x <<- e1) (G y <<- e2) f.
Proof.
move=> m.
set m' := ((m.{x#'1 <- `[{e1}] m.1}).{y#'2 <- `[{e2}] m.2} : rmem).
have h1 : ssem_ ps (G x <<- e1) m.1 = dunit (m' # '1)%M.
+ by rewrite ssem_gassnE /m' !mselect_msetg.
have h2 : ssem_ ps (G y <<- e2) m.2 = dunit (m' # '2)%M.
+ by rewrite ssem_gassnE /m' !mselect_msetg.
exists (dunit (Some m'.1, Some m'.2)).
+ by rewrite h1 h2; apply: scoupling_dunit.
by rewrite eexp_dunit /rstar -surjective_pairing.
Qed.

Lemma erhl_sample {T1 T2 : IhbType.type}
    (x : vars T1) (d1 : dexpr T1) (y : vars T2) (d2 : dexpr T2)
    (nu : rmem -> Distr (T1 * T2)%type) f :
  (forall m, (0 <= f m)%E) ->
  (forall m : rmem, iscoupling (`[{d1}] m.1) (`[{d2}] m.2) (nu m)) ->
  erhl (fun m : rmem =>
          espe (\dlet_(v <- nu m) dunit (m.[~1 x <- v.1]).[~2 y <- v.2]) f)
       (x <$- d1) (y <$- d2) f.
Proof.
move=> hf hc m.
pose upd (v : (T1 * T2)%type) := ((m.[~1 x <- v.1]).[~2 y <- v.2] : rmem).
pose h (o : option (T1 * T2)%type) : (option cmem * option cmem)%type :=
  if o is Some v then (Some (upd v).1, Some (upd v).2) else (None, None).
have hup1 : forall v, (upd v).1 = (m.1.[x <- v.1])%M.
+ by move=> v; rewrite /upd -/(mselect '1 _) !mselect_mset.
have hup2 : forall v, (upd v).2 = (m.2.[y <- v.2])%M.
+ by move=> v; rewrite /upd -/(mselect '2 _) !mselect_mset.
exists (dmargin h (dstar (nu m))).
+ split; rewrite dmargin_comp.
  * have -> : dmargin (fst \o h) (dstar (nu m))
            = dmargin (omap (fun v : (T1 * T2)%type => (m.1.[x <- v.1])%M))
                      (dstar (nu m)).
    - by apply: eq_dmargin; case=> [v|] //=; rewrite hup1.
    rewrite dstar_dmargin; congr dstar.
    have -> : dmargin (fun v : (T1 * T2)%type => (m.1.[x <- v.1])%M) (nu m)
            = dmargin (fun v1 => (m.1.[x <- v1])%M) (dmargin fst (nu m)).
    - by rewrite dmargin_comp.
    by case: (hc m) => -> _; rewrite ssemE dmarginE.
  have -> : dmargin (snd \o h) (dstar (nu m))
          = dmargin (omap (fun v : (T1 * T2)%type => (m.2.[y <- v.2])%M))
                    (dstar (nu m)).
  * by apply: eq_dmargin; case=> [v|] //=; rewrite hup2.
  rewrite dstar_dmargin; congr dstar.
  have -> : dmargin (fun v : (T1 * T2)%type => (m.2.[y <- v.2])%M) (nu m)
          = dmargin (fun v2 => (m.2.[y <- v2])%M) (dmargin snd (nu m)).
  * by rewrite dmargin_comp.
  by case: (hc m) => _ ->; rewrite ssemE dmarginE.
have -> : espe (dmargin h (dstar (nu m))) (rstar f)
        = espe (dstar (nu m)) (rstar f \o h).
+ by apply: eexp_dmargin => p; exact: ge0_rstar.
have -> : espe (dstar (nu m)) (rstar f \o h)
        = espe (nu m) ((rstar f \o h) \o some).
+ by apply: espe_dstar => // o; exact: ge0_rstar.
have -> : (\dlet_(v <- nu m) dunit (upd v)) = dmargin upd (nu m) by rewrite dmarginE.
rewrite (eexp_dmargin _ _ _ hf).
by apply: le_espe => v; rewrite /comp /rstar /= -surjective_pairing.
Qed.

Lemma erhl_block f g bs1 c rs1 bs2 d rs2 :
  (forall m, (0 <= g m)%E) ->
  (forall m : rmem,
     erhl (bound (fun _ => f m) (minit m.1 bs1, minit m.2 bs2)) c d
          (fun m'' : rmem => g (mret m.1 m''.1 rs1, mret m.2 m''.2 rs2))) ->
  erhl f (Block bs1 Do c Return rs1) (Block bs2 Do d Return rs2) g.
Proof.
move=> hg H m.
case: (H m ((minit m.1 bs1, minit m.2 bs2) : rmem)) => nu hnu hle.
rewrite /bound eqxx in hle.
exists (dmargin (fun p : option cmem * option cmem =>
          (omap (fun m1' => mret m.1 m1' rs1) p.1,
           omap (fun m2' => mret m.2 m2' rs2) p.2)) nu).
+ have := scoupling_dmargin _ _ _ (fun m1' => mret m.1 m1' rs1)
                                  (fun m2' => mret m.2 m2' rs2) hnu.
  by rewrite !ssem_blockE !dmarginE.
by rewrite (espe_dmargin_rstar _ _ _ _ hg); exact: hle.
Qed.

Lemma erhl_if f g (e1 e2 : bexpr) c1 c2 d1 d2 :
  erhl (rlift `[{    e1#'1 &&    e2#'2 }] f) c1 d1 g ->
  erhl (rlift `[{ ~~ e1#'1 && ~~ e2#'2 }] f) c2 d2 g ->
  erhl (rlift `[{ e1#'1 =b e2#'2 }] f)
       (If e1 then c1 else c2) (If e2 then d1 else d2) g.
Proof.
move=> h1 h2 m; rewrite !ssemE.
case he1 : (`[{e1}] m.1); case he2 : (`[{e2}] m.2) => /=.
+ case: (h1 m) => nu hnu hle; exists nu => //.
  by move: hle; rewrite /ehl_stmt.lift !esemE he1 he2.
+ have [nu hnu] := exists_scoupling (ssem_ ps c1 m.1) (ssem_ ps d2 m.2).
  by exists nu => //; rewrite /ehl_stmt.lift !esemE he1 he2 /=; exact: leey.
+ have [nu hnu] := exists_scoupling (ssem_ ps c2 m.1) (ssem_ ps d1 m.2).
  by exists nu => //; rewrite /ehl_stmt.lift !esemE he1 he2 /=; exact: leey.
case: (h2 m) => nu hnu hle; exists nu => //.
by move: hle; rewrite /ehl_stmt.lift !esemE he1 he2.
Qed.

Lemma erhl_seq f g h c1 c2 d1 d2 :
  (forall m, (0 <= g m)%E) ->
  erhl f c1 d1 h -> erhl h c2 d2 g -> erhl f (c1 ;; c2) (d1 ;; d2) g.
Proof.
move=> hg H1 H2 m.
have hge : forall p, (0 <= rstar g p)%E by move=> p; exact: ge0_rstar.
case: (erhlw _ _ _ _ m H1) => nu hnu hle.
pose k (p : option cmem * option cmem) : Distr (option cmem * option cmem)%type :=
  match p with
  | (Some a, Some b) => s2val (erhlw _ _ _ _ (a, b) H2)
  | (Some a, None)   => dmargin (fun o => (o, @None cmem)) (dstar (ssem_ ps c2 a))
  | (None, Some b)   => dmargin (fun o => (@None cmem, o)) (dstar (ssem_ ps d2 b))
  | (None, None)     => dunit (@None cmem, @None cmem)
  end.
have hk1 : forall p, dfst (k p) = ostar (fun a => ssem_ ps c2 a) p.1.
+ case=> [[a|] [b|]] /=.
  * by have [h1' h2'] := s2valP (erhlw _ _ _ _ (a, b) H2); exact: h1'.
  * rewrite dmargin_comp /comp.
    have -> : (fun o : option cmem => (o, @None cmem).1) = id by [].
    by rewrite dmarginE dlet_dunit_id.
  * rewrite dmargin_comp /comp.
    have -> : (fun o : option cmem => (@None cmem, o).1) = (fun=> @None cmem) by [].
    by apply/distr_eqP => o; rewrite dmarginE dletC dweight_dstar mul1r.
  by rewrite dmargin_dunit.
have hk2 : forall p, dsnd (k p) = ostar (fun b => ssem_ ps d2 b) p.2.
+ case=> [[a|] [b|]] /=.
  * by have [h1' h2'] := s2valP (erhlw _ _ _ _ (a, b) H2); exact: h2'.
  * rewrite dmargin_comp /comp.
    have -> : (fun o : option cmem => (o, @None cmem).2) = (fun=> @None cmem) by [].
    by apply/distr_eqP => o; rewrite dmarginE dletC dweight_dstar mul1r.
  * rewrite dmargin_comp /comp.
    have -> : (fun o : option cmem => (@None cmem, o).2) = id by [].
    by rewrite dmarginE dlet_dunit_id.
  by rewrite dmargin_dunit.
exists (\dlet_(p <- nu) k p).
+ rewrite !ssemE; apply: scoupling_dlet; [exact: hnu | exact: hk1 | exact: hk2].
have -> : espe (\dlet_(p <- nu) k p) (rstar g)
        = espe nu (fun p => espe (k p) (rstar g)).
+ by apply: eexp_dlet; exact: hge.
apply: (le_trans _ hle).
apply: le_espe; case=> [[a|] [b|]] /=; rewrite /rstar /=.
+ exact: (s2valP' (erhlw _ _ _ _ (a, b) H2)).
+ by rewrite espe_rstar_right0.
+ by rewrite espe_rstar_left0.
by rewrite eexp_dunit /rstar.
Qed.

(* [While].  Exactly the shape of [ehl.v]'s [ehl_while]: [erhl_ierhl_pt]   *)
(* turns the judgment into an inequality, so the whole rule is an          *)
(* induction on the [whilen] unrolling using [erhl_abort] / [erhl_if] /    *)
(* [erhl_seq] / [erhl_skip], with a single limit step ([psharp_dlim]).     *)
(* No coupling has to be built by hand -- contrast [prhl_while], which     *)
(* constructs a monotone family explicitly.                                *)
Lemma erhl_while f (e1 e2 : bexpr) c d :
  (forall m, (0 <= f m)%E) ->
  erhl (rlift `[{ e1#'1 && e2#'2 }] f) c d (rlift `[{ e1#'1 =b e2#'2 }] f) ->
  erhl (rlift `[{ e1#'1 =b e2#'2 }] f)
       (While e1 Do c) (While e2 Do d)
       (rlift `[{ ~~ e1#'1 && ~~ e2#'2 }] f).
Proof.
move=> hf hbody.
have hlift : forall (b : rmem -> bool) m, (0 <= rlift b f m)%E.
+ by move=> b m; rewrite /ehl_stmt.lift; case: (b m); [exact: hf | exact: leey].
have key : forall n,
  erhl (rlift `[{ e1#'1 =b e2#'2 }] f)
       (whilen e1 c n) (whilen e2 d n)
       (rlift `[{ ~~ e1#'1 && ~~ e2#'2 }] f).
+ elim=> [|n IH] /=.
  * by apply: erhl_abort => m; exact: hlift.
  apply: erhl_if.
  - by apply: erhl_seq; [move=> m; exact: hlift | exact: hbody | exact: IH].
  by apply: erhl_skip => m; exact: lexx.
move=> m; apply/(erhl_ierhl_pt _ _ _ _ (hlift _)).
rewrite !ssem_whileE; apply: psharp_dlim.
+ by move=> n p le; exact: homo_whilen.
+ by move=> n p le; exact: homo_whilen.
+ by move=> m'; exact: hlift.
by move=> n; apply: erhl_ierhl_ptL; exact: (key n m).
Qed.

(* -------------------------------------------------------------------- *)
(* One-sided rules                                                       *)
(* -------------------------------------------------------------------- *)

(* The star-coupling of [[c]]m1 with [dunit m2] is UNIQUE: [dsnd] must be   *)
(* [dunit (Some m2)], so all the mass sits in _ x {Some m2}.  One-sided     *)
(* eRHL judgments are therefore exactly unary eHL judgments, and the        *)
(* corresponding rules come straight from [ehl.v].                          *)
Lemma erhl_oneL (f g : rcond) c :
  (forall m, (0 <= g m)%E) ->
  (forall m2, ehl_ ps (fun m1 => f (m1, m2)) c (fun m1' => g (m1', m2))) ->
  erhl f c skip g.
Proof.
move=> hg h m.
exists (dmargin (fun o => (o, Some m.2)) (dstar (ssem_ ps c m.1))).
+ split; rewrite dmargin_comp /comp.
  * have -> : (fun o : option cmem => (o, Some m.2).1) = id by [].
    by rewrite dmarginE dlet_dunit_id.
  have -> : (fun o : option cmem => (o, Some m.2).2) = (fun=> Some m.2) by [].
  rewrite ssemE dstar_dunit.
  by apply/distr_eqP => o; rewrite dmarginE dletC dweight_dstar mul1r.
have -> : espe (dmargin (fun o => (o, Some m.2)) (dstar (ssem_ ps c m.1)))
               (rstar g)
        = espe (dstar (ssem_ ps c m.1))
               (rstar g \o (fun o => (o, Some m.2))).
+ by apply: eexp_dmargin => p; exact: ge0_rstar.
have -> : espe (dstar (ssem_ ps c m.1)) (rstar g \o (fun o => (o, Some m.2)))
        = espe (ssem_ ps c m.1)
               ((rstar g \o (fun o => (o, Some m.2))) \o some).
+ by apply: espe_dstar => // o; exact: ge0_rstar.
by have := h m.2 m.1; rewrite -surjective_pairing.
Qed.

(* Converse of [erhl_oneL]: uses that the coupling is concentrated on the   *)
(* slice _ x {Some m2} ([scoupling_supp2]).                                 *)
Lemma erhl_oneLW (f g : rcond) c :
  (forall m, (0 <= g m)%E) ->
  erhl f c skip g ->
  forall m2, ehl_ ps (fun m1 => f (m1, m2)) c (fun m1' => g (m1', m2)).
Proof.
move=> hg h m2 m1; case: (h (m1, m2)) => nu hnu hle.
rewrite /= ssemE in hnu.
have hs := scoupling_supp2 _ _ _ hnu.
have hH : forall o : option cmem,
  (0 <= (if o is Some a then g (a, m2) else 0%E))%E.
+ by case=> [a|] //=; exact: hg.
apply: (le_trans _ hle).
have -> : espe nu (rstar g)
        = espe nu ((fun o => if o is Some a then g (a, m2) else 0%E) \o fst).
+ apply: eexp_eq_in; case=> [[a|] b] hp; rewrite /rstar /comp //=.
  by have hb : b = Some m2 := hs (Some a, b) hp; rewrite hb.
rewrite -(eexp_dmargin nu fst _ hH).
by case: hnu => h1 _; rewrite h1 (espe_dstar _ _ hH).
Qed.

Lemma erhl_assignL {T : IhbType.type} (x : vars T) (e : expr T) f :
  erhl (fun m : rmem => f m.[~1 x <- `[{e}] m.1]) (x <<- e) skip f.
Proof.
move=> m; set m' := (m.[~1 x <- `[{e}] m.1] : rmem).
have h1 : ssem_ ps (x <<- e) m.1 = dunit (m' # '1)%M.
+ by rewrite ssemE /m' mselect_mset.
have h2 : ssem_ ps skip m.2 = dunit (m' # '2)%M.
+ by rewrite ssemE /m' mselect_mset.
exists (dunit (Some m'.1, Some m'.2)).
+ by rewrite h1 h2; apply: scoupling_dunit.
by rewrite eexp_dunit /rstar -surjective_pairing.
Qed.

Lemma erhl_gassignL {T : IhbType.type} (x : vars T) (e : expr T) f :
  erhl (fun m : rmem => f m.{x#'1 <- `[{e}] m.1}) (G x <<- e) skip f.
Proof.
move=> m; set m' := (m.{x#'1 <- `[{e}] m.1} : rmem).
have h1 : ssem_ ps (G x <<- e) m.1 = dunit (m' # '1)%M.
+ by rewrite ssem_gassnE /m' mselect_msetg.
have h2 : ssem_ ps skip m.2 = dunit (m' # '2)%M.
+ by rewrite ssemE /m' mselect_msetg.
exists (dunit (Some m'.1, Some m'.2)).
+ by rewrite h1 h2; apply: scoupling_dunit.
by rewrite eexp_dunit /rstar -surjective_pairing.
Qed.

Lemma erhl_sampleL {T : IhbType.type} (x : vars T) (d : dexpr T) f :
  (forall m, (0 <= f m)%E) ->
  erhl (fun m : rmem => espe (\dlet_(v <- `[{d}] m.1) dunit m.[~1 x <- v]) f)
       (x <$- d) skip f.
Proof.
move=> hf; apply: erhl_oneL => // m2 m1; rewrite ssemE.
have -> : (\dlet_(v <- `[{d}] m1) dunit (((m1, m2) : rmem).[~1 x <- v]))
        = dmargin (fun v => (((m1.[x <- v])%M, m2) : rmem)) (`[{d}] m1).
+ by rewrite dmarginE; apply: eq_in_dlet => // v _; rewrite rmset1E.
have -> : (\dlet_(v <- `[{d}] m1) dunit (m1.[x <- v])%M)
        = dmargin (fun v => (m1.[x <- v])%M) (`[{d}] m1) by rewrite dmarginE.
rewrite (eexp_dmargin _ _ _ hf).
rewrite (eexp_dmargin _ _ _ (fun m1' => hf (m1', m2))).
exact: lexx.
Qed.

Lemma erhl_blockL f g bs c rs d :
  (forall m, (0 <= g m)%E) ->
  (forall m : rmem,
     erhl (bound (fun _ => f m) (minit m.1 bs, m.2)) c d
          (fun m'' : rmem => g (mret m.1 m''.1 rs, m''.2))) ->
  erhl f (Block bs Do c Return rs) d g.
Proof.
move=> hg H m.
case: (H m ((minit m.1 bs, m.2) : rmem)) => nu hnu hle.
rewrite /bound eqxx in hle.
exists (dmargin (fun p : option cmem * option cmem =>
          (omap (fun m1' => mret m.1 m1' rs) p.1, omap id p.2)) nu).
+ have := scoupling_dmargin _ _ _ (fun m1' => mret m.1 m1' rs) id hnu.
  rewrite ssem_blockE dmarginE.
  by have -> : dmargin id (ssem_ ps d m.2) = ssem_ ps d m.2
    by rewrite dmarginE dlet_dunit_id.
by rewrite (espe_dmargin_rstar _ _ _ _ hg); exact: hle.
Qed.

Lemma erhl_ifL f g (e : bexpr) c1 c2 d :
  erhl (rlift `[{    e#'1 }] f) c1 d g ->
  erhl (rlift `[{ ~~ e#'1 }] f) c2 d g ->
  erhl f (If e then c1 else c2) d g.
Proof.
move=> h1 h2 m; rewrite ssemE.
case he : (`[{e}] m.1) => /=.
+ case: (h1 m) => nu hnu hle; exists nu => //.
  by move: hle; rewrite /ehl_stmt.lift !esemE he.
case: (h2 m) => nu hnu hle; exists nu => //.
by move: hle; rewrite /ehl_stmt.lift !esemE he.
Qed.

Lemma erhl_whileL f (e : bexpr) c :
  (forall m, (0 <= f m)%E) ->
  erhl (rlift `[{ e#'1 }] f) c skip f ->
  erhl f (While e Do c) skip (rlift `[{ ~~ e#'1 }] f).
Proof.
move=> hf h; apply: erhl_oneL => [m|m2].
+ by rewrite /ehl_stmt.lift; case: ifP => // _; exact: leey.
have -> : (fun m1' : cmem => rlift `[{ ~~ e#'1 }] f (m1', m2))
        = ehl_stmt.lift (fun m1' => ~~ `[{e}] m1') (fun m1 => f (m1, m2)).
+ by apply/funext => m1'; rewrite /ehl_stmt.lift !esemE.
apply: ehl.ehl_while; first by move=> m1; exact: hf.
have hb := erhl_oneLW _ _ _ hf h m2.
by move=> m1; have := hb m1; rewrite /ehl_stmt.lift !esemE.
Qed.

(* -------------------------------------------------------------------- *)
(* Logical rules                                                         *)
(* -------------------------------------------------------------------- *)

Lemma erhl_swap f g c d :
  (forall m, (0 <= g m)%E) ->
  erhl (rswap f) d c (rswap g) -> erhl f c d g.
Proof.
move=> hg h m; case: (h (m.2, m.1)) => nu hnu hle.
exists (dswap nu); first by apply: scoupling_swap; exact: hnu.
by rewrite (espe_dswap _ _ hg); move: hle; rewrite /rswap /= -surjective_pairing.
Qed.

Lemma kerhl_swap (f : rcond) (g : rcond2) c d :
  (forall m0 m, (0 <= g m0 m)%E) ->
  kerhl f d c g -> kerhl (rswap f) c d (rswap2 g).
Proof.
move=> hg h m; case: (h (m.2, m.1)) => nu hnu hle.
exists (dswap nu); first by apply: scoupling_swap; exact: hnu.
rewrite (espe_dswap _ _ (fun m' => hg (m.2, m.1) (m'.2, m'.1))).
have -> : espe nu (rstar (rswap (rswap2 g m))) = espe nu (rstar (g (m.2, m.1))).
+ by apply: eexp_eq; case=> [[a|] [b|]]; rewrite /rstar /rswap /rswap2.
by rewrite /rswap; exact: hle.
Qed.

(* Right-sided mirrors, obtained from the left ones through [erhl_swap]. *)
Lemma erhl_swapW (f g : rcond) c d :
  (forall m, (0 <= g m)%E) -> erhl f c d g -> erhl (rswap f) d c (rswap g).
Proof.
move=> hg h.
have hff : rswap (rswap f) = f by apply/funext; exact: rswapK.
have hgg : rswap (rswap g) = g by apply/funext; exact: rswapK.
by apply: erhl_swap => [m|]; [rewrite /rswap; exact: hg | rewrite hff hgg].
Qed.

Lemma erhl_oneR (f g : rcond) c :
  (forall m, (0 <= g m)%E) ->
  (forall m1, ehl_ ps (fun m2 => f (m1, m2)) c (fun m2' => g (m1, m2'))) ->
  erhl f skip c g.
Proof.
move=> hg h; apply: erhl_swap => //.
apply: erhl_oneL => [m|m2]; first by rewrite /rswap; exact: hg.
by have := h m2; rewrite /rswap.
Qed.

Lemma erhl_oneRW (f g : rcond) c :
  (forall m, (0 <= g m)%E) ->
  erhl f skip c g ->
  forall m1, ehl_ ps (fun m2 => f (m1, m2)) c (fun m2' => g (m1, m2')).
Proof.
move=> hg h m1.
have hg' : forall m, (0 <= rswap g m)%E by move=> m; rewrite /rswap; exact: hg.
by have := erhl_oneLW _ _ _ hg' (erhl_swapW _ _ _ _ hg h) m1; rewrite /rswap.
Qed.

Lemma erhl_conseq f f' g g' c d :
  (forall m, (0 <= g m)%E) ->
  erhl f' c d g' ->
  (forall (m : rmem) (mu1 mu2 : Distr cmem),
     (psharp g' mu1 mu2 <= f' m)%E -> (psharp g mu1 mu2 <= f m)%E) ->
  erhl f c d g.
Proof.
move=> hg h hc m; apply/(erhl_ierhl_pt _ _ _ _ hg).
by apply: hc; apply: erhl_ierhl_ptL; exact: h.
Qed.

Lemma kerhl_conseq f1 f2 (g1 g2 : rcond2) c d :
  (forall m0 m, (0 <= g1 m0 m)%E) ->
  kerhl f2 c d g2 ->
  (forall (m : rmem) (mu1 mu2 : Distr cmem),
     (psharp (g2 m) mu1 mu2 <= f2 m)%E -> (psharp (g1 m) mu1 mu2 <= f1 m)%E) ->
  kerhl f1 c d g1.
Proof.
move=> hg h hc m; apply/(erhl_ierhl_pt _ _ _ _ (hg m)).
by apply: hc; apply: erhl_ierhl_ptL; exact: h.
Qed.

(* [Nmod-L].  The logical variable [v] of the paper is the *initial* value  *)
(* of [x<1>]; since [x] is not modified by [c], [hl.mod_spec] says every    *)
(* reachable memory still carries that value, and [mset_get] then makes the *)
(* substitution in the post-expectation vacuous.                            *)
Lemma erhl_nmodL {T : IhbType.type} (x : vars T) f g c d :
  nocall c ->
  (Tagged vars x) \notin hl.mod c ->
  (forall v : T,
     erhl (rlift (fun m : rmem => `[< (m.1.[x])%M = v >]) f) c d
          (fun m' : rmem => g m'.[~1 x <- v])) ->
  erhl f c d g.
Proof.
move=> hnc hmod H m.
case: (H ((m.1).[x])%M m) => nu hnu hle.
have hguard : `[< ((m.1).[x])%M = ((m.1).[x])%M >] by apply/asboolP.
rewrite /ehl_stmt.lift hguard in hle.
exists nu => //.
have -> : espe nu (rstar g)
        = espe nu (rstar (fun m' : rmem => g m'.[~1 x <- ((m.1).[x])%M]));
  last exact: hle.
apply: eexp_eq_in; case=> [[a|] [b|]] hp; rewrite /rstar //.
have ha : a \in dinsupp (ssem_ ps c m.1).
+ apply/dinsuppP => hz.
  have hle2 := le_dfst nu (Some a, Some b).
  case: hnu => h1 _; rewrite h1 dstarE /= hz in hle2.
  have hnz : nu (Some a, Some b) = 0 by apply/eqP; rewrite eq_le hle2 ge0_mu.
  by move: hp; rewrite in_dinsupp hnz eqxx.
have hax : ((a).[x])%M = ((m.1).[x])%M.
+ have hr : range [pred m' | `[< hl.eqon (predC (hl.mod c)) m.1 m' >]]
                  (ssem_ ps c m.1).
  * by apply: (hl.mod_spec hnc); rewrite !inE.
  have := hr a ha; rewrite inE => /asboolP heq.
  have hmem : (Tagged vars x) \in predC (hl.mod c) by rewrite !inE.
  by rewrite (heq _ hmem).
by rewrite -hax rmset_get1.
Qed.

Lemma erhl_strassen (Rl : rel cmem) f c d :
  lossless predT c -> lossless predT d ->
  (forall M : pred cmem,
     erhl (fun m : rmem => (1 + f m)%E) c d
          (fun m' : rmem => ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E)) ->
  erhl f c d (fun m' : rmem => ((~~ Rl m'.1 m'.2)%:R)%:E).
Proof.
move=> hc hd h m.
have w1 : dweight (ssem_ ps c m.1) = 1 by apply: hc; rewrite inE.
have w2 : dweight (ssem_ ps d m.2) = 1 by apply: hd; rewrite inE.
pose T (P : rmem -> bool) : pred (option cmem * option cmem)%type :=
  [pred p | if p is (Some a, Some b) then P (a, b) else false].
(* The hypothesis, read as a statement about the two marginals.  This is    *)
(* exactly the computation of [erhl_strassenInv] run backwards; the extra   *)
(* ingredient is [scoupling_full_supp], which is where losslessness enters: *)
(* it lets [T _] be replaced by a predicate depending on one component      *)
(* only, so that [pr_dmargin] and [pr_dstar] can push it to the marginal.   *)
have hraw : forall M : pred cmem,
    ((\P_[ssem_ ps c m.1] M)%:E
       + (1 - \P_[ssem_ ps d m.2] (rimage Rl M))%:E <= 1 + f m)%E.
+ move=> M; case: (h M m) => nu hnu hle.
  have hT : forall P : rmem -> bool,
      espe nu (rstar (fun m' : rmem => ((P m')%:R)%:E)) = (\P_[nu] (T P))%:E.
  - move=> P; rewrite -(espe_indic nu (T P)).
    by apply: eexp_eq; case=> [[a|] [b|]]; rewrite /rstar.
  have hsplit :
    espe nu (rstar (fun m' : rmem =>
               ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E))
    = (espe nu (rstar (fun m' : rmem => ((M m'.1)%:R)%:E))
     + espe nu (rstar (fun m' : rmem => ((~~ rimage Rl M m'.2)%:R)%:E)))%E.
  - rewrite -espe_rstarD.
    * by move=> ?; rewrite lee_fin ler0n.
    * by move=> ?; rewrite lee_fin ler0n.
    by apply: eexp_eq => p; rewrite /rstar; case: p => -[a|] [b|].
  have e1 : \P_[nu] (T (fun m' => M m'.1)) = \P_[ssem_ ps c m.1] M.
  - have -> : \P_[nu] (T (fun m' => M m'.1))
            = \P_[nu] [pred x | fst x \in
                        [pred o | if o is Some a then M a else false]].
    * apply: eq_in_pr => p hp; move: (scoupling_full_supp _ _ _ w1 w2 hnu p hp).
      by case: p hp => [[a|] [b|]] //= _ _; rewrite !inE.
    by rewrite -(pr_dmargin _ fst) (proj1 hnu) pr_dstar.
  have e2 : \P_[nu] (T (fun m' => ~~ rimage Rl M m'.2))
          = 1 - \P_[ssem_ ps d m.2] (rimage Rl M).
  - have -> : \P_[nu] (T (fun m' => ~~ rimage Rl M m'.2))
            = \P_[nu] [pred x | snd x \in
                        [pred o | if o is Some b
                                  then ~~ rimage Rl M b else false]].
    * apply: eq_in_pr => p hp; move: (scoupling_full_supp _ _ _ w1 w2 hnu p hp).
      by case: p hp => [[a|] [b|]] //= _ _; rewrite !inE.
    rewrite -(pr_dmargin _ snd) (proj2 hnu).
    have -> : [pred o | if o is Some b then ~~ rimage Rl M b else false]
            = [pred o : option cmem | if o is Some b
                                      then (predC (rimage Rl M)) b else false]
      by [].
    by rewrite pr_dstar pr_predC w2.
  by move: hle; rewrite hsplit !hT e1 e2.
(* [0 <= f m]: instantiate at [M := pred0], where [rimage] is empty. *)
have hz0 : \P_[ssem_ ps d m.2] (rimage Rl pred0) = 0.
+ have -> : \P_[ssem_ ps d m.2] (rimage Rl pred0)
          = \P_[ssem_ ps d m.2] pred0.
  - by apply: eq_pr => x; rewrite !inE /=; apply/negbTE/asboolPn => -[y].
  exact: pr_pred0.
have hf0 : (0 <= f m)%E.
+ have h0 := hraw pred0.
  rewrite pr_pred0 hz0 subr0 in h0.
  by move: h0; rewrite add0e -{1}(adde0 1%:E) leeD2lE.
have arith : forall a b e : pwhile.R, a + (1 - b) <= 1 + e -> a <= b + e.
+ move=> a b e H; rewrite addrC -lerBlDr.
  by move: H; rewrite addrA [a + 1]addrC -addrA lerD2l.
(* An infinite pre-expectation makes the goal vacuous. *)
case: (eqVneq (f m) (+oo)%E) => [hoo|hnoo].
+ have [nu hnu] := exists_scoupling (ssem_ ps c m.1) (ssem_ ps d m.2).
  by exists nu => //; rewrite hoo leey.
have hfn : f m \is a fin_num by rewrite ge0_fin_numE // ltey.
have [delta hdE] : exists delta : pwhile.R, f m = delta%:E.
+ by exists (fine (f m)); rewrite fineK.
have hd0 : 0 <= delta by rewrite -lee_fin -hdE.
have hM : forall M : pred cmem,
    \P_[ssem_ ps c m.1] M <= \P_[ssem_ ps d m.2] (rimage Rl M) + delta.
+ move=> M; apply: arith.
  by have := hraw M; rewrite hdE -!EFinD lee_fin.
have [nu hnu hle] :=
  strassen_deficiency (ssem_ ps c m.1) (ssem_ ps d m.2) Rl delta w1 w2 hd0 hM.
by exists nu => //; rewrite hdE.
Qed.

(* No [lossless] hypothesis: see the comment on [H_StrassenInv]. *)
Lemma erhl_strassenInv (Rl : rel cmem) f c d (M : pred cmem) :
  erhl f c d (fun m' : rmem => ((~~ Rl m'.1 m'.2)%:R)%:E) ->
  erhl (fun m : rmem => (1 + f m)%E) c d
       (fun m' : rmem => ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E).
Proof.
move=> h m; case: (h m) => nu hnu hle; exists nu => //.
(* Everything happens inside [nu]; no marginal, hence no AST, is needed. *)
pose T (P : rmem -> bool) : pred (option cmem * option cmem)%type :=
  [pred p | if p is (Some a, Some b) then P (a, b) else false].
have hT : forall P : rmem -> bool,
  espe nu (rstar (fun m' : rmem => ((P m')%:R)%:E)) = (\P_[nu] (T P))%:E.
+ move=> P; rewrite -(espe_indic nu (T P)).
  by apply: eexp_eq; case=> [[a|] [b|]]; rewrite /rstar.
have hsplit :
  espe nu (rstar (fun m' : rmem =>
             ((M m'.1)%:R + (~~ rimage Rl M m'.2)%:R)%:E))
  = (espe nu (rstar (fun m' : rmem => ((M m'.1)%:R)%:E))
   + espe nu (rstar (fun m' : rmem => ((~~ rimage Rl M m'.2)%:R)%:E)))%E.
+ rewrite -espe_rstarD.
  * by move=> ?; rewrite lee_fin ler0n.
  * by move=> ?; rewrite lee_fin ler0n.
  by apply: eexp_eq => p; rewrite /rstar; case: p => -[a|] [b|].
(* P[T1] + P[T2] = P[T1 n T2] + P[T1 u T2] <= P[Tbad] + 1, and P[Tbad] is *)
(* exactly the hypothesis.  No marginal is taken, hence no AST is needed. *)
have hbad : \P_[nu] [predI T (fun m' => M m'.1)
                       & T (fun m' => ~~ rimage Rl M m'.2)]
         <= \P_[nu] (T (fun m' => ~~ Rl m'.1 m'.2)).
+ apply: subset_pr; case=> [[a|] [b|]] //=; rewrite !inE /= => /andP[hM hIm].
  apply/negP => hR; move/negP: hIm; apply.
  by apply/asboolP; exists a; rewrite hM hR.
have hsum : \P_[nu] (T (fun m' => M m'.1))
          + \P_[nu] (T (fun m' => ~~ rimage Rl M m'.2))
          = \P_[nu] [predI T (fun m' => M m'.1)
                        & T (fun m' => ~~ rimage Rl M m'.2)]
          + \P_[nu] [predU T (fun m' => M m'.1)
                        & T (fun m' => ~~ rimage Rl M m'.2)].
+ by rewrite pr_and subrK.
have hreal : \P_[nu] (T (fun m' => M m'.1))
           + \P_[nu] (T (fun m' => ~~ rimage Rl M m'.2))
          <= 1 + \P_[nu] (T (fun m' => ~~ Rl m'.1 m'.2)).
+ by rewrite hsum addrC; apply: lerD; [exact: le1_pr | exact: hbad].
have hbadE : ((\P_[nu] (T (fun m' : rmem => ~~ Rl m'.1 m'.2)))%:E <= f m)%E.
+ by rewrite -hT; exact: hle.
rewrite hsplit !hT -EFinD.
apply: (@le_trans _ _ ((1 + \P_[nu] (T (fun m' : rmem => ~~ Rl m'.1 m'.2)))%:E)).
+ by rewrite lee_fin.
by rewrite EFinD; apply: leeD2l.
Qed.

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
  rcl_pre_pos cl' -> rcl_post_pos cl' -> rcl_skip_valid cl' ->
  rhoare_triple_proc_ctx cl' ps' ->
  (forall o1 o2, kerhl_ ps' (get_pre (cl' o1 o2))
                   (ocmd o1) (ocmd o2) (get_post (cl' o1 o2))).
Proof.
move=> hpre hpost hNN hproc.
(* Level-by-level: at inlining depth [n] the semantics is exact, so the  *)
(* whole recursion is a plain induction on [n] -- no limit is involved.  *)
have key : forall n o1 o2,
  kerhl_ (k_inliner_ps1 n ps') (get_pre (cl' o1 o2))
         (ocmd o1) (ocmd o2) (get_post (cl' o1 o2)).
+ elim=> [|n IH] q1 q2 s.
  * case: q1 => [p1|]; case: q2 => [p2|].
    - exists (dunit (@None cmem, @None cmem)).
      + by split; rewrite dmargin_dunit ssem_false_ps dstar_dnull.
      by rewrite eexp_dunit /rstar; exact: hpre.
    - exists (dunit (@None cmem, Some s.2)).
      + split; rewrite dmargin_dunit /=.
        * by rewrite ssem_false_ps dstar_dnull.
        by rewrite ssemE dstar_dunit.
      by rewrite eexp_dunit /rstar; exact: hpre.
    - exists (dunit (Some s.1, @None cmem)).
      + split; rewrite dmargin_dunit /=.
        * by rewrite ssemE dstar_dunit.
        by rewrite ssem_false_ps dstar_dnull.
      by rewrite eexp_dunit /rstar; exact: hpre.
    exists (dunit (Some s.1, Some s.2)).
    + by rewrite !ssemE; apply: scoupling_dunit.
    by rewrite eexp_dunit /rstar -surjective_pairing; exact: hNN.
  have hstep : forall q,
    ssem_ (k_inliner_ps1 n.+1 ps') (ocmd q)
      =1 ssem_ (k_inliner_ps1 n ps') (obody ps' q).
  * by case=> [p|] s0; rewrite -add1n (inline2_split n 1).
  rewrite (hstep q1 s.1) (hstep q2 s.2).
  by apply: (hproc q1 q2 (k_inliner_ps1 n ps') IH).
move=> o1 o2 s; apply/(erhl_ierhl_pt _ _ _ _ (hpost o1 o2 s)).
rewrite !ssem_dlim_ubnf; apply: psharp_dlim.
+ by move=> ????; apply: mono_ssem_aux; exact: homo_ubnf.
+ by move=> ????; apply: mono_ssem_aux; exact: homo_ubnf.
+ by move=> m'; exact: hpost.
move=> n; apply: erhl_ierhl_ptL.
by rewrite !ssem_aux_ssem_; exact: (key n o1 o2 s).
Qed.

Theorem recursion_rhoare_triple :
  forall f (g : rcond2) c d (cl : rphi) (ps' : psi),
    rcl_pre_pos cl -> rcl_post_pos cl -> rcl_skip_valid cl ->
    rhoare_triple_proc_ctx cl ps' ->
    rhoare_triple_ctx cl ps' f g c d ->
    kerhl_ ps' f c d g.
Proof.
move=> f g c d cl ps' hpre hpost hNN hproc hctx.
by apply: hctx; exact: (recursive_proc ps' cl hpre hpost hNN hproc).
Qed.

End Rules.

(* -------------------------------------------------------------------- *)
(* Well-formedness ([rcl_post_pos]) is part of validity: the [H_Swap] case  *)
(* of soundness transports the context through [rphi_swap], which goes      *)
(* through [espe_dswap] and so needs the contract posts to be non-negative. *)
Definition valid_cl (cl : rphi) (ps : psi) :=
  rcl_post_pos cl /\
  forall o1 o2, kerhl_ ps (get_pre (cl o1 o2))
                  (ocmd o1) (ocmd o2) (get_post (cl o1 o2)).

Lemma valid_cl_empty ps : valid_cl rcl_empty ps.
Proof.
split; first exact: rpost_pos_rcl_empty.
move=> o1 o2 m.
have [nu hnu] :=
  exists_scoupling (ssem_ ps (ocmd o1) m.1) (ssem_ ps (ocmd o2) m.2).
by exists nu => //; exact: leey.
Qed.

Lemma valid_cl_swap cl ps : valid_cl cl ps -> valid_cl (rphi_swap cl) ps.
Proof.
case=> hpos hv; split=> [o1 o2 m0 m|o1 o2].
+ by rewrite /rphi_swap /= /rswap2; exact: hpos.
by rewrite /rphi_swap /=; apply: kerhl_swap => [m0 m|]; [exact: hpos | exact: hv].
Qed.

(* Theorem 4.3 / 6.1(1).  Proof deferred: it goes by [derivable_mut] off *)
(* the rule lemmas above.                                                *)
Theorem soundness :
  (forall ps cl f c d g, derivable  ps cl f c d g ->
     valid_cl cl ps -> erhl_  ps f c d g) /\
  (forall ps cl f c d (g : rcond2), derivable2 ps cl f c d g ->
     valid_cl cl ps -> kerhl_ ps f c d g).
Proof.
apply: derivable_mut.
- (* H_Abort *) by move=> f g c cl ps hf _; apply: erhl_abort.
- (* H_Skip *) by move=> f cl ps _; apply: erhl_skip => m; exact: lexx.
- (* H_Asgn *) by move=> *; exact: erhl_assign.
- (* H_GAsgn *) by move=> *; exact: erhl_gassign.
- (* H_Sample *) by move=> *; apply: erhl_sample.
- (* H_Block *)
  by move=> f g bs1 c rs1 bs2 d rs2 cl ps hg _ IH hv;
     apply: erhl_block => // m; exact: IH.
- (* H_If *)
  by move=> f g e1 e2 c1 c2 d1 d2 cl ps _ IH1 _ IH2 hv;
     apply: erhl_if; [exact: IH1 | exact: IH2].
- (* H_While *)
  by move=> f e1 e2 c d cl ps hf _ IH hv; apply: erhl_while => //; exact: IH.
- (* H_Seq *)
  by move=> f g h c1 c2 d1 d2 cl ps hg _ IHa _ IHb hv;
     apply: erhl_seq => //; [exact: IHb | exact: IHa].
- (* H_AsgnL *) by move=> *; exact: erhl_assignL.
- (* H_GAsgnL *) by move=> *; exact: erhl_gassignL.
- (* H_SampleL *) by move=> *; apply: erhl_sampleL.
- (* H_BlockL *)
  by move=> f g bs c rs d cl ps hg _ IH hv;
     apply: erhl_blockL => // m; exact: IH.
- (* H_IfL *)
  by move=> f g e c1 c2 d cl ps _ IH1 _ IH2 hv;
     apply: erhl_ifL; [exact: IH1 | exact: IH2].
- (* H_WhileL *)
  by move=> f e c cl ps hf _ IH hv; apply: erhl_whileL => //; exact: IH.
- (* H_Swap *)
  by move=> f g c d cl ps hg _ IH hv; apply: erhl_swap => //;
     apply: IH; exact: valid_cl_swap.
- (* H_Consequence *)
  by move=> f f' g g' c d cl ps hg _ IH hc hv;
     apply: erhl_conseq; [exact: hg | exact: IH | exact: hc].
- (* H_NmodL *)
  by move=> T x f g c d cl ps hnc hmod _ IH hv;
     exact: (erhl_nmodL _ x _ _ _ _ hnc hmod (fun v => IH v hv)).
- (* H_Strassen *)
  by move=> Rl f c d cl ps hlc hld _ IH hv;
     apply: erhl_strassen => // M; exact: IH.
- (* H_StrassenInv *)
  by move=> Rl f c d cl ps M _ IH hv; apply: erhl_strassenInv; exact: IH.
- (* H_krhl *) by move=> f g c d cl ps _ IH hv; apply/erhl_kerhl; exact: IH.
- (* H_rhl *)
  by move=> f g c d cl ps _ IH hv; apply/kerhl_erhl => s0; exact: IH.
- (* H_call *) by move=> cl o1 o2 ps [_ hv]; exact: hv.
- (* H_rec *)
  move=> f g c d cl cl' ps' hcpre hcpos hcNN _ IH_body _ IH_c hv.
  have hproc : rhoare_triple_proc_ctx cl ps'.
  + rewrite /rhoare_triple_proc_ctx /rhoare_triple_ctx => o1 o2 ps'' hctx.
    by apply: IH_body; split; [exact: hcpos | exact: hctx].
  have hmain : rhoare_triple_ctx cl ps' f g c d.
  + rewrite /rhoare_triple_ctx => hctx.
    by apply: IH_c; split; [exact: hcpos | exact: hctx].
  exact (@recursion_rhoare_triple f g c d cl ps'
            hcpre hcpos hcNN hproc hmain).
- (* H_adapt *)
  by move=> f1 f2 g1 g2 c d cl ps hg _ IH hc hv;
     apply: kerhl_conseq; [exact: hg | exact: IH | exact: hc].
Qed.

Corollary rhoare_sound0 f c d g ps :
  derivable ps rcl_empty f c d g -> erhl_ ps f c d g.
Proof.
by move=> hd; apply: (proj1 soundness _ rcl_empty) => //; exact: valid_cl_empty.
Qed.

Corollary krhoare_sound0 f c d (g : rcond2) ps :
  derivable2 ps rcl_empty f c d g -> kerhl_ ps f c d g.
Proof.
by move=> hd; apply: (proj2 soundness _ rcl_empty) => //; exact: valid_cl_empty.
Qed.

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
Proof.
move=> m; set m' := (m.[~2 x <- `[{e}] m.2] : rmem).
have h1 : ssem_ ps skip m.1 = dunit (m' # '1)%M.
+ by rewrite ssemE /m' mselect_mset.
have h2 : ssem_ ps (x <<- e) m.2 = dunit (m' # '2)%M.
+ by rewrite ssemE /m' mselect_mset.
exists (dunit (Some m'.1, Some m'.2)).
+ by rewrite h1 h2; apply: scoupling_dunit.
by rewrite eexp_dunit /rstar -surjective_pairing.
Qed.

Lemma erhl_gassignR {T : IhbType.type} (x : vars T) (e : expr T) f :
  erhl (fun m : rmem => f m.{x#'2 <- `[{e}] m.2}) skip (G x <<- e) f.
Proof.
move=> m; set m' := (m.{x#'2 <- `[{e}] m.2} : rmem).
have h1 : ssem_ ps skip m.1 = dunit (m' # '1)%M.
+ by rewrite ssemE /m' mselect_msetg.
have h2 : ssem_ ps (G x <<- e) m.2 = dunit (m' # '2)%M.
+ by rewrite ssem_gassnE /m' mselect_msetg.
exists (dunit (Some m'.1, Some m'.2)).
+ by rewrite h1 h2; apply: scoupling_dunit.
by rewrite eexp_dunit /rstar -surjective_pairing.
Qed.

Lemma erhl_sampleR {T : IhbType.type} (x : vars T) (d : dexpr T) f :
  (forall m, (0 <= f m)%E) ->
  erhl (fun m : rmem => espe (\dlet_(v <- `[{d}] m.2) dunit m.[~2 x <- v]) f)
       skip (x <$- d) f.
Proof.
move=> hf; apply: (erhl_oneR ps) => // m1 m2; rewrite ssemE.
have -> : (\dlet_(v <- `[{d}] m2) dunit (((m1, m2) : rmem).[~2 x <- v]))
        = dmargin (fun v => ((m1, (m2.[x <- v])%M) : rmem)) (`[{d}] m2).
+ by rewrite dmarginE; apply: eq_in_dlet => // v _; rewrite rmset2E.
have -> : (\dlet_(v <- `[{d}] m2) dunit (m2.[x <- v])%M)
        = dmargin (fun v => (m2.[x <- v])%M) (`[{d}] m2) by rewrite dmarginE.
rewrite (eexp_dmargin _ _ _ hf).
rewrite (eexp_dmargin _ _ _ (fun m2' => hf (m1, m2'))).
exact: lexx.
Qed.

Lemma erhl_ifR f g (e : bexpr) d1 d2 c :
  erhl (rlift `[{    e#'2 }] f) c d1 g ->
  erhl (rlift `[{ ~~ e#'2 }] f) c d2 g ->
  erhl f c (If e then d1 else d2) g.
Proof.
move=> h1 h2 m; rewrite ssemE.
case he : (`[{e}] m.2) => /=.
+ case: (h1 m) => nu hnu hle; exists nu => //.
  by move: hle; rewrite /ehl_stmt.lift !esemE he.
case: (h2 m) => nu hnu hle; exists nu => //.
by move: hle; rewrite /ehl_stmt.lift !esemE he.
Qed.

Lemma erhl_whileR f (e : bexpr) d :
  (forall m, (0 <= f m)%E) ->
  erhl (rlift `[{ e#'2 }] f) skip d f ->
  erhl f skip (While e Do d) (rlift `[{ ~~ e#'2 }] f).
Proof.
move=> hf h; apply: (erhl_oneR ps) => [m|m1].
+ by rewrite /ehl_stmt.lift; case: ifP => // _; exact: leey.
have -> : (fun m2' : cmem => rlift `[{ ~~ e#'2 }] f (m1, m2'))
        = ehl_stmt.lift (fun m2' => ~~ `[{e}] m2') (fun m2 => f (m1, m2)).
+ by apply/funext => m2'; rewrite /ehl_stmt.lift !esemE.
apply: ehl.ehl_while; first by move=> m2; exact: hf.
have hb := erhl_oneRW ps _ _ _ hf h m1.
by move=> m2; have := hb m2; rewrite /ehl_stmt.lift !esemE.
Qed.

Lemma erhl_nmodR {T : IhbType.type} (x : vars T) f g c d :
  nocall d ->
  (Tagged vars x) \notin hl.mod d ->
  (forall v : T,
     erhl (rlift (fun m : rmem => `[< (m.2.[x])%M = v >]) f) c d
          (fun m' : rmem => g m'.[~2 x <- v])) ->
  erhl f c d g.
Proof.
move=> hnc hmod H m.
case: (H ((m.2).[x])%M m) => nu hnu hle.
have hguard : `[< ((m.2).[x])%M = ((m.2).[x])%M >] by apply/asboolP.
rewrite /ehl_stmt.lift hguard in hle.
exists nu => //.
have -> : espe nu (rstar g)
        = espe nu (rstar (fun m' : rmem => g m'.[~2 x <- ((m.2).[x])%M]));
  last exact: hle.
apply: eexp_eq_in; case=> [[a|] [b|]] hp; rewrite /rstar //.
have hb : b \in dinsupp (ssem_ ps d m.2).
+ apply/dinsuppP => hz.
  have hle2 := le_dsnd nu (Some a, Some b).
  case: hnu => _ h2; rewrite h2 dstarE /= hz in hle2.
  have hnz : nu (Some a, Some b) = 0 by apply/eqP; rewrite eq_le hle2 ge0_mu.
  by move: hp; rewrite in_dinsupp hnz eqxx.
have hbx : ((b).[x])%M = ((m.2).[x])%M.
+ have hr : range [pred m' | `[< hl.eqon (predC (hl.mod d)) m.2 m' >]]
                  (ssem_ ps d m.2).
  * by apply: (hl.mod_spec hnc); rewrite !inE.
  have := hr b hb; rewrite inE => /asboolP heq.
  have hmem : (Tagged vars x) \in predC (hl.mod d) by rewrite !inE.
  by rewrite (heq _ hmem).
by rewrite -hbx rmset_get2.
Qed.

(* Lemma 5.2: the semantic embedding of pRHL into eRHL, by               *)
(* contraposition.  Entry point for the applications of Section 5.       *)
Lemma prhl_erhl (P Q : rassn) c d :
  prhl_ ps P c d Q ->
  erhl (fun m : rmem => ((~~ P m)%:R)%:E) c d
       (fun m' : rmem => ((~~ Q m')%:R)%:E).
Proof.
move=> h m; case/boolP: (P m) => hP; last first.
(* Unrelated inputs: the pre-expectation is 1, and any coupling will do. *)
+ have [nu hnu] := exists_scoupling (ssem_ ps c m.1) (ssem_ ps d m.2).
  exists nu => //=.
  apply: (@le_trans _ _ (espe nu (fun=> 1%E))).
  * apply: le_espe; case=> [[a|] [b|]]; rewrite /rstar /= lee_fin;
      try by rewrite ler01.
    by case: (~~ Q (a, b)).
  by rewrite eexp_cst (dweight_scoupling _ _ _ hnu) mule1.
(* Related inputs: the pRHL coupling has its support inside Q, so the      *)
(* indicator of ~Q integrates to 0.                                        *)
case: (prhlw h hP) => nu0 hnu0 hrg.
exists (slift nu0); first exact: scoupling_slift.
have -> : espe (slift nu0) (rstar (fun m' : rmem => ((~~ Q m')%:R)%:E))
        = espe nu0 (fun m' : rmem => ((~~ Q m')%:R)%:E).
+ by apply: espe_slift => m'; rewrite lee_fin ler0n.
rewrite (espe_indic nu0 [pred m' | ~~ Q m']).
have -> : \P_[nu0] [pred m' : rmem | ~~ Q m'] = 0.
+ by apply: eq0_pr => m' /hrg hQ; rewrite !inE negbK.
by [].
Qed.

End Derived.
