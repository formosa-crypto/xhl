(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From mathcomp           Require Import boot order algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import esum ereal counting_distr.
From mathcomp           Require finmap.
From xhl.pwhile         Require Import notations inhabited pwhile psemantic range.
From xhl.ehl            Require Import ehl_stmt.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope sem_scope.

Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

(* -------------------------------------------------------------------- *)

Section ehl.
Context {X Y : eqType} {mem : memType X}.

Notation cond := (@cond _ mem).
Notation cond2 := (@cond2 _ mem).

Notation phi := (@Phi.type X Y mem).
Notation psi := (@psi _ Y mem).

Implicit Types  (f g h : cond).

Section Logic.

Definition cond2_independent (P:  mem -> \bar pwhile.R -> mem -> \bar pwhile.R) :=
(forall r r' x x', P x r x' = P x r' x')%E.

Definition cl_cond2_independent (cl:phi) :=
  forall (f: Y), cond2_independent (get_post (cl f)).

Inductive derivable : psi -> phi -> cond -> cmd -> cond -> Prop :=
| H_Abort : forall f g cl ps,
    (forall m, (0 <= f m)%E) ->
    derivable ps cl f abort g
| H_Skip : forall f cl ps,
    derivable ps cl f skip f
| H_Asgn : forall {T : IhbType.type} x (e : expr_ X mem T) f cl ps,
    derivable ps cl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f
| H_GAsgn : forall {T : IhbType.type} x (e : expr_ X mem T) f cl ps,
    derivable ps cl (fun m => f (m.{x <- `[{e}] m})) (G x <<- e) f
| H_Random : forall {T : IhbType.type} x (d:expr_ X mem (Distr T))  f cl ps,
    let g m :=
      espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f
    in
    derivable ps cl g (x <$- d) f
| H_Block : forall f g bs c rs cl ps,
    (forall m, (0 <= g m)%E) ->
    (forall m, derivable ps cl (bound (fun _ => f m) (minit m bs)) c
                               (fun m'' => g (mret m m'' rs))) ->
    derivable ps cl f (block bs c rs) g
| H_If : forall f g (e:expr_ X mem bool) c1 c2 cl ps,
    derivable ps cl (lift (esem e) f) c1 g ->
    derivable ps cl (lift (fun m => negb (esem e m)) f) c2 g ->
    derivable ps cl f (If e then c1 else c2) g
| H_While : forall f (e:expr_ X mem bool) c cl ps ,
    (forall m, 0 <= f m)%E ->
    derivable ps cl (lift (esem e) f) c f ->
    derivable ps cl f (While e Do c) (lift (fun m => negb (esem e m)) f)
| H_Seq : forall f c d g h cl ps,
    (forall m, (0 <= g m)%E) ->
    derivable ps cl h d g -> derivable ps cl f c h -> derivable ps cl f (c;;d) g
| H_Consequence : forall f' g' f g (c : cmd) cl ps,
    derivable ps cl f' c g' ->
    (forall m mu,  espe mu g' <= f' m -> espe mu g <= f m)%E ->
    derivable ps cl f c g
| H_khl : forall P Q c cl ps,
    derivable2 ps cl P c (fun _ _ => Q) -> derivable ps cl P c Q
with derivable2 : psi -> phi -> cond -> cmd -> cond2 -> Prop :=
| H_hl: forall P Q c cl ps,
    (* (forall m mu m', (0 <= Q m mu m')%E) -> *)
    (* cond2_mono Q -> *)
    (forall s0, derivable ps cl (bound P s0) c (fun s => Q s0 ((ssem_ ps c s0 s)%:E) s)) ->
    derivable2 ps cl P c Q
| H_call : forall cl (f:Y) ps,
    derivable2 ps cl (get_pre (cl f)) (call f) (get_post (cl f))
| H_rec : forall P Q c (cl cl':phi) ps',
    cl_cond2_independent cl ->
    (forall p' ps, derivable2 ps cl (get_pre (cl p')) (ps' p') (get_post (cl p'))) ->
    (forall ps, derivable2 ps cl P c Q) ->
    derivable2 ps' cl' P c Q
| H_adapt : forall (P1 P2 : cond) (Q1 Q2 : cond2) c cl ps,
    derivable2 ps cl P2 c Q2 ->
    (forall m mu,  espe mu (fun m' => Q2 m ((mu m')%:E) m') <= P2 m ->
              espe mu (fun m' => Q1 m ((mu m')%:E) m') <= P1 m)%E ->
    derivable2 ps cl P1 c Q1.

Scheme derivable_min := Minimality for derivable Sort Prop
    with derivable2_min := Minimality for derivable2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

End Logic.

Section Sound.

Section Rules.
Context (ps: psi).

Notation ehl   := (ehl_ ps).
Notation kehl   := (kehl_ ps).

(* -------------------------------------------------------------------- *)

Lemma ehl_skip f g :
  (forall m, (g m <= f m)%E) ->
  ehl f skip g.
Proof. by move => h m; rewrite ssemE eexp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_abort f g :
  (forall m, (0 <= f m)%E) ->
  ehl f abort g.
Proof.
move => h m.
rewrite ssem_abortE /espe.
rewrite (eq_esum _ _ (fun _ => 0)).
- by move => x; rewrite dnullE mule0.
- by rewrite esum0.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_seq_m (m:mem) f g h c1 c2:
  (forall m : mem, 0 <= g m)%E ->
  (espe (ssem_ ps c1 m) h <= f m)%E ->
  (forall m : mem, espe (ssem_ ps c2 m) g <= h m)%E ->
  (espe(\dlet_(m' <- ssem_ ps c1 m) ssem_ ps c2 m') g <= f m)%E.
Proof.
move => Hg h1 h2.
rewrite eexp_dlet //.
apply: (@le_trans _ _ (espe (ssem_ ps c1 m) h)); last exact: h1.
rewrite /espe; apply: le_esum => x ?; apply: lee_wpmul2r.
+ by apply: lee_tofin; apply: ge0_mu.
+ exact: h2.
Qed.

Lemma ehl_seq f g h c1 c2:
  (forall m, (0 <= g m)%E) ->
  ehl f c1 h -> ehl h c2 g -> ehl f (c1 ;; c2) g.
Proof.
move => Hg h1 h2 m.
rewrite ssemE.
by apply: (ehl_seq_m m _ _ h).
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_assign {T : IhbType.type} f x (e : expr_ X mem T) :
  ehl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f.
Proof. by  move => m; rewrite ssemE eexp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_gassign {T : IhbType.type} f x (e : expr_ X mem T) :
  ehl (fun m => f (m.{x <- `[{e}] m})) (G x <<- e) f.
Proof. by move => m; rewrite ssem_gassnE eexp_dunit. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_block f g bs c rs :
  (forall m, (0 <= g m)%E) ->
  (forall m, ehl (bound (fun _ => f m) (minit m bs)) c
                 (fun m'' => g (mret m m'' rs))) ->
  ehl f (block bs c rs) g.
Proof.
move=> Hg H m; rewrite ssem_blockE espe_dlet_ret //.
by have := H m (minit m bs); rewrite /bound eqxx.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_random {T : IhbType.type} f x (d:expr_ X mem (Distr T)) :
  let g m :=
    espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) f
  in
  ehl g (x <$- d) f.
Proof. by move => g m; rewrite ssemE. Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_if f (e:expr_ X mem bool) c1 c2 g :
  ehl (lift (esem e) f) c1 g ->
  ehl (lift (fun m => negb (esem e m)) f) c2 g ->
  ehl f (If e then c1 else c2) g.
Proof.
move => Hc1 Hc2 m.
rewrite ssemE.
case h: (`[{e}] m).
- move : (Hc1 m).
  by rewrite /lift h /=.
  move : (Hc2 m).
  by  rewrite /lift h /=.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_while (e:expr_ X mem bool) c f :
  (forall m, 0 <= f m)%E ->
  ehl (lift (esem e) f) c f ->
  ehl f (While e Do c) (lift (fun m => negb (esem e m)) f).
Proof.
move => Hf.
have Hpos : forall m : mem, (0%R <= (if ~~ `[{e}] m then f m else +oo))%E.
+ move => m;  case (`[{e}] m) => //=. exact: le0y.
rewrite /lift => Hi m.
rewrite ssemE /espe.
apply: (esum_dlim_r (dhomo_dnd (homo_whilen e c m)) Hpos) => n.
move : m.
elim : n => /=.
+ by apply ehl_abort.
+  move => n Hi'.
   apply ehl_if => //=.
   + by apply: (ehl_seq _ _ f).
   + by apply ehl_skip.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_conseq c f g f' g':
  ehl f' c g' ->
  (forall m d,  espe d g' <= f' m -> espe d g <= f m)%E ->
  ehl f c g.
Proof. move => h' hc m. by apply hc. Qed.

(* -------------------------------------------------------------------- *)

Lemma kehl_conseq c f f' (g g' : cond2):
  kehl f' c g' ->
  (forall m d,  espe d (fun m' => g' m ((d m')%:E) m') <= f' m ->
           espe d (fun m' => g m ((d m')%:E) m') <= f m)%E ->
  kehl f c g.
Proof. by move => h' hc m; apply hc. Qed.

(* -------------------------------------------------------------------- *)

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx (cl : phi) (ps: psi) (P: cond) (Q: cond2) (c: cmd) :=
  (forall p, kehl_ ps (get_pre (cl p)) (call p) (get_post (cl p))) ->
  kehl_ ps P c Q.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx (cl : phi) (ps_init: psi):=
  forall p ps, hoare_triple_ctx cl ps
            (get_pre (cl p))
            (get_post (cl p))
            (ps_init p).

Lemma recursive_proc (ps': psi) (cl' : phi) :
  cl_cond2_independent cl' ->
  hoare_triple_proc_ctx cl' ps' ->
  (forall p, kehl_ ps' (get_pre (cl' p)) (call p)  (get_post (cl' p))).
Proof.
  rewrite /cl_cond2_independent /cond2_independent.
  move => hcl h p s.
  rewrite /espe {2}ssem_dlim_ubnf.
  apply esum_dlim_r.
  + move => ????.
    apply mono_ssem_aux.
    by apply homo_ubnf.
  + move => m. exact: post_pos.
  move => n; rewrite ssem_aux_ssem_.
  under eq_esum do rewrite (hcl p _ 0%E).
  move : s p.
  elim : n => [| n Hn].
  + move => ??. rewrite ssem_false_ps.
    under eq_esum do  rewrite dnullE mule0.
    rewrite esum1 //.
    exact: pre_pos.
  move => s p.
  rewrite (inline2_split n 1) //=.
  rewrite /hoare_triple_proc_ctx in h.
  rewrite /hoare_triple_ctx in h.
  under eq_esum => i do rewrite (hcl p _ (EFin (ssem_ (k_inliner_ps1 n ps') (ps' p) s i))).
  apply: h => // p0 s0.
  rewrite /espe.
  under eq_esum do rewrite (hcl p0 _ 0%E).
  by apply: Hn.
Qed.

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple :
  forall P Q c (cl: phi) (ps: psi),
    cl_cond2_independent cl ->
    hoare_triple_proc_ctx cl ps  ->
    hoare_triple_ctx cl ps P Q c ->
    kehl_ ps P c Q .
Proof.
  move => ?????? H H0.
  apply H0.
  by apply: recursive_proc.
Qed.

(* -------------------------------------------------------------------- *)
End Rules.

Definition valid_cl (cl:phi) (ps:psi) :=
  forall (f:Y), kehl_ ps (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma soundness :
  (forall (ps:psi) (cl:phi) P (c:cmd) Q, derivable ps cl P c Q ->
      valid_cl cl ps -> ehl_ ps P c Q) /\
  (forall ps cl P c Q, derivable2 ps cl P c Q ->
     valid_cl cl ps -> kehl_ ps P c Q).
Proof.
apply: derivable_mut.
- (* H_Abort *) by move=> *; exact: ehl_abort.
- (* H_Skip *)  by move=> *; exact: ehl_skip.
- (* H_Asgn *) by move=> *; exact: ehl_assign.
- (* H_GAsgn *) by move=> *; exact: ehl_gassign.
- (* H_Random *) by move=> *; exact: ehl_random.
- (* H_Block *)
  move=> f g bs c rs cl ps Hg _ IH Hv.
  by apply: ehl_block; [exact: Hg | move=> m; exact: IH].
- (* H_If *)
  move=> Pr Po e c1 c2 cl ? ? IH1 ? IH2 Hv.
  by apply: ehl_if; [exact: IH1 | exact: IH2].
- (* H_While *)
  by move=> I e c cl ? Hpos ? IH Hv; apply: ehl_while; [exact: Hpos | exact: IH].
- (* H_Seq *)
  move=> P c Q d R cl ps Hpos ? IHd ? IHc Hv.
  by apply: ehl_seq; [exact: Hpos | exact: (IHc Hv) | exact: (IHd Hv)].
- (* H_Consequence *)
  move=> P2 Q2 P1 Q1 c cl ps ? HP HQ IH Hv.
  by apply: ehl_conseq; [ exact: HP | exact: HQ].
- (* H_khl *) by move=> P Q c cl ? ? IH Hv; apply/ehl_kehl; exact: IH.
- (* H_hl *)
  move=> P Q c cl ps ? IH Hv.
  rewrite kehl_ehl => s0.
  exact: (IH s0 Hv).
- (* H_call *) by move=> cl f ? Hv; exact: Hv.
- (* H_rec *)
  move=> P Q c cl cl' ps' Hlc _ IH_body _ IH_c Hv.
  apply: (recursion_hoare_triple _ _ _ cl) => //.
  rewrite /hoare_triple_ctx.
   by move => h; apply: IH_c.
- (* H_adapt *)
  move=> P1 P2 Q1 Q2 c cl ps ? IH H Hv m.
   exact: (H m (ssem_ ps c m) (IH Hv m)).
Qed.

Corollary hoare_sound0 P c Q ps : derivable ps cl_empty P c Q -> ehl_ ps P c Q.
Proof.
  move => Hd.
  apply: (proj1 soundness _ cl_empty) => //.
  rewrite /valid_cl /kehl_ => //= => *.
  rewrite /empty_precondition.
  exact: leey.
Qed.

Corollary khoare_sound0 P c Q ps : derivable2 ps cl_empty P c Q -> kehl_ ps P c Q.
Proof.
  move => Hd.
  apply: (proj2 soundness _ cl_empty) => //.
  rewrite /valid_cl /kehl_ => //= => *.
  rewrite /empty_precondition.
  exact: leey.
Qed.

End Sound.

Section Complete.


Definition cl_mgt ps : Y -> clause:=
fun (f:Y) => ((fun _ => 0)%E,
                (fun (s0: mem) r s =>
                   if (r <= ((ssem_ ps (ps f) s0) s)%:E)%E then 0%E else +oo%E)
          ).

(* The logic in section Logic cannot be proven complete. *)
(*    This is because the to proof completes, the contract "cl_mgt" *)
(*    is requires. This contract implies that postcondition for procedure *)
(*    dependents on the resulting distribution of the execution of the program. *)
(*    However, to proof soundness, the postcondition must be independent from *)
(*    from this argument. *)

(*    If the H_rec case in the logic is like in Ellora, then the logic is complete. *)

(*    The ehl2.v file present a logic which is complete. Not, that *)
(*    the logic in ehl2.v allows to use H_rec more then one time *)
(*    which is not possible in the logic present in section logic. *)
(*  *)

End Complete.

Section prhl.

From xhl.prhl Require Import prhl.

Notation cmd := (@cmd ident ident cmem).

Lemma espe_coupling (ν : Distr (cmem * cmem)) (g g':(@ehl_stmt.cond _ cmem)) :
  (forall m, 0 <= g m)%E ->
  (forall m, 0 <= g' m)%E ->
  (forall p, p \in dinsupp ν -> (g p.2 <= g' p.1)%E) ->
  (espe (dsnd ν) g <= espe (dfst ν) g')%E.
Proof.
move => Hg Hg' Hpw.
rewrite eexp_dlet //.
rewrite {1}/espe.
rewrite (eq_esum _ _ (fun p => g p.2 * EFin (ν p))%E).
+ by move => ??; rewrite eexp_dunit.
rewrite [espe (dfst ν) g'] eexp_dlet //.
rewrite {1}/espe.
rewrite (eq_esum _
           (fun x => espe (dunit (T:=cmem) x.1) g' * EFin (ν x))%E
           (fun p => g' p.1 * EFin (ν p))%E).
+ by move => ??; rewrite eexp_dunit.
rewrite /espe; apply: le_esum => p _.
case/boolP: (p \in dinsupp ν) => [hp | /dinsuppPn hp].
+ apply: lee_wpmul2r; first by apply: lee_tofin; apply: ge0_mu.
  exact: Hpw _ hp.
+ by rewrite hp !mule0.
Qed.

Lemma ehl_prhl (c d:cmd) (f g f' g':(@ehl_stmt.cond _ cmem))  P Q (ps: ident -> cmd):
  (forall m : cmem, 0 <= g m)%E ->
  (forall m : cmem, 0 <= g' m)%E ->
  ehl_ ps f' d g' ->
  @prhl_ ps P d c Q ->
  (forall m, exists m', f' m' <= f m /\ P (m',m))%E ->
  (forall m' m, Q (m',m) -> g m <= g' m')%E ->
  ehl_ ps f c g.
Proof.
move => Hg Hg' He Hr H1 H2 m.
have [m' Hm'] := H1 m.
have [Hle HP] := Hm'.
have [ν [Hfst Hsnd] Hrange] := prhlw Hr HP.
rewrite -Hsnd.
have Hpw : forall p, p \in dinsupp ν -> (g p.2 <= g' p.1)%E.
{ by move => [m1 m2] /Hrange /H2. }
apply: (@le_trans _ _ (espe (dfst ν) g')).
- exact: (espe_coupling ν g g' Hg Hg' Hpw).
  rewrite Hfst.
  apply: (@le_trans _ _ (f' m')); first exact: (He m').
  exact: Hle.
Qed.

End prhl.

End ehl.
