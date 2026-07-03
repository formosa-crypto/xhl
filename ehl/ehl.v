(* -------------------------------------------------------------------- *)
(* (* ----------------- *) Require Import Setoid Morphisms. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis Require Import esum ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr edistr.
From mathcomp    Require  finmap.
From xhl.pwhile Require Import notations inhabited pwhile psemantic range.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

(* -------------------------------------------------------------------- *)

Section EHL.
Context {ps: ident -> (@cmd_ ident cmem ident)}.

Definition psi := ident -> (@cmd_ ident cmem ident).

Definition cond := cmem -> \bar pwhile.R.

Implicit Types  (f g h : cond).

Definition ehl_ (ps:psi) f c g :=
  forall m : cmem, (espe (ssem_ ps c m) g <= f m)%E.

Notation ehl   := (ehl_ ps).

(* -------------------------------------------------------------------- *)
(* Pratical Hoare triple                                                *)
(* -------------------------------------------------------------------- *)

Definition cond2 := cmem -> cmem -> \bar pwhile.R.

Definition kehl_ (ps:psi) f c (g: cond2) :=
  forall m : cmem, (espe (ssem_ ps c m) (g m) <= f m)%E.

Notation kehl   := (kehl_ ps).

Definition bound {T : choiceType} (g : T -> \bar R) m0 m :=
  if (m == m0) then (g m) else +oo%E.

Lemma kehl_ehl P c Q :
  kehl P c Q <-> (forall s0, ehl (bound P s0) c (Q s0)).
Proof.
  rewrite /bound; split.
  + move=> h m0 m.
    case_eq (m == m0).
    - by move => /eqP <-.
    - move => _. exact : leey.
  + move => h m.
    have // := (h m m).
    by rewrite eq_refl.
Qed.

Lemma hl_khl P c Q :
  kehl P c (fun _ => Q) <-> ehl P c Q.
Proof.
  by split; move => h m; apply h.
Qed.

Lemma kehl_conseq c f f' (g g' : cond2):
  kehl f' c g' ->
  (forall m d,  espe d (g' m) <= f' m -> espe d (g m) <= f m)%E ->
  kehl f c g.
Proof.
  move => h' hc m.
  by apply hc.
Qed.


(* -------------------------------------------------------------------- *)

Lemma ehl_skip f g :
  (forall m, (g m <= f m)%E) ->
  ehl f skip g.
Proof.
  move => h m.
  by rewrite ssemE exp_dunit.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_abort f g :
  (forall m, (0 <= f m)%E) ->
  ehl f abort g.
Proof.
  move => h m.
  rewrite ssem_abortE /espe.
  rewrite (@esum.eq_sum _ _ _ (fun _ => 0)).
  - by rewrite esum.sum0.
  - by move => x; rewrite dnullE mule0.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_seq_m (m:cmem) f g h c1 c2:
  (forall m : cmem, 0 <= g m)%E ->
  (espe (ssem ps c1 m) h <= f m)%E ->
  (forall m : cmem, espe (ssem ps c2 m) g <= h m)%E ->
  (espe(\dlet_(m' <- ssem ps c1 m) ssem ps c2 m') g <= f m)%E.
Proof.
  move => Hg h1 h2.
  rewrite exp_dlet //.
  apply: (@le_trans _ _ (espe (ssem ps c1 m) h)); last exact: h1.
  rewrite /espe; apply: esum.le_sum.
  - move => x; apply: mule_ge0; last by apply: lee_tofin; apply: ge0_mu.
    apply: sum_ge0 => x'; apply: mule_ge0; first exact: Hg.
    by apply: lee_tofin; apply: ge0_mu.
  - move => x; apply: lee_wpmul2r.
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

Lemma ehl_assgn {T : IhbType.type} f x (e : expr T) :
  ehl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f.
Proof.
  move => m.
  by rewrite ssemE exp_dunit.
Qed.

(* -------------------------------------------------------------------- *)

Lemma ehl_rnd {T : IhbType.type} f x (e : dexpr T) :
  let g m :=
    espe (\dlet_(v <- `[{e}] m) (dunit m.[x <- v])) f
  in
  ehl g (x <$- e) f.
Proof.
  move => g m.
  by rewrite ssemE.
Qed.

(* -------------------------------------------------------------------- *)

Definition lift (b: cmem -> bool) f (m: cmem) : \bar pwhile.R :=
  match (b m) with
  | true => (f m)
  | false => +oo
  end.

Lemma ehl_if f (e : bexpr) c1 c2 g :
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

Lemma ehl_while (e : bexpr) c f :
  (forall m, 0 <= f m)%E ->
  ehl (lift (esem e) f) c f ->
  ehl f (While e Do c) (lift (fun m => negb (esem e m)) f).
Proof.
move => Hf.
have Hpos : forall m : cmem, (0%R <= (if ~~ `[{e}] m then f m else +oo))%E.
+ by move => m;  case (`[{e}] m) => //=.
rewrite /lift => Hi m.
rewrite  ssemE /espe esum_sum';last first.
- move => x; rewrite mule_ge0 //.
  by rewrite lee_tofin.
apply: (esum_dlim_r (homo_whilen e c m)) => //.
move => n; rewrite -esum_sum';last first.
- move => x; rewrite mule_ge0 //.
  by rewrite lee_tofin.
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
Proof.
  move => h' hc m.
  by apply hc.
Qed.

(* -------------------------------------------------------------------- *)

(** Definition of a procedure contract **)

Definition clause : Type := cond * cond2.

Definition get_pre (an:clause) :=
  let (pre,_) := an in
  pre.

Definition get_post (an:clause) :=
  let (_,post) := an in
  post.

Definition phi : Type := ident -> clause.

Definition empty_precondition : cond := (fun _ => -oo)%E.

Definition empty_postcondition :  cond2 := (fun _ _ => -oo)%E.

Definition empty_clause : clause := (empty_precondition, empty_postcondition).

Definition empty_phi: phi := fun _ => empty_clause.

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx (cl : phi) ps (P: cond) (Q: cond2) (c: cmd) :=
  (forall p, kehl_ ps (get_pre (cl p)) (call p) (get_post (cl p))) ->
  kehl_ ps P c Q.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx (cl : phi) (ps_init: ident -> (@cmd_ ident cmem ident)):=
  forall p ps, hoare_triple_ctx cl ps
            (get_pre (cl p))
            (get_post (cl p))
            (ps_init p).

From xhl.hl Require hl.

Lemma recursive_proc ps' cl' :
  (forall p m, 0 <= (get_pre (cl' p)) m)%E ->
  (forall p m m', 0 <= (get_post (cl' p)) m m')%E ->
  hoare_triple_proc_ctx cl' ps' ->
  (forall p, kehl_ ps' (get_pre (cl' p))
          (call p)
          (get_post (cl' p))).
Proof.
  move => Hpre Hpost h p s.
  rewrite /espe  esum_sum';last first.
    - move => x; rewrite mule_ge0 //.
      rewrite lee_tofin //.
   rewrite !hl.test8.
   apply esum_dlim_r.
    + move => ????.
     apply mono_ssem_aux.
     by apply homo_ubnf.
    + exact: (Hpost p).
  move => n.
  (*This should be a lemma*)
  rewrite hl.ssem_ubnf_dnull hl.ubnf_ssem (hl.test9 _ _ _ _ ps') hl.test5.
  revert p; revert s.
  elim : n => [| n Hn].
  + move => ??. rewrite hl.ssem_false_ps.
    under eq_esum do  rewrite dnullE mule0.
    by rewrite esum1.
  move => s p.
  rewrite (hl.inline2_split n 1) //=.
  rewrite -esum_sum';last first.
  + move => x; rewrite mule_ge0 //.
      rewrite lee_tofin //.
  apply: h => // p0 s0.
  rewrite /espe esum_sum';last first.
  + move => x; rewrite mule_ge0 //.
      rewrite lee_tofin //.
  by apply: Hn.
Qed.

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple :
  forall P Q c cl ps,
    (forall p m, 0 <= (get_pre (cl p)) m)%E ->
    (forall p m m', 0 <= (get_post (cl p)) m m')%E ->
    hoare_triple_proc_ctx cl ps  ->
    hoare_triple_ctx cl ps P Q c ->
    kehl_ ps P c Q .
Proof.
  move => ????? Hpre Hpost H H0.
  apply H0.
  by apply: recursive_proc.
Qed.

(* -------------------------------------------------------------------- *)

From xhl.prhl Require Import prhl.

Lemma espe_coupling (ν : Distr (cmem * cmem)) g g' :
  (forall m, 0 <= g m)%E ->
  (forall m, 0 <= g' m)%E ->
  (forall p, p \in dinsupp ν -> (g p.2 <= g' p.1)%E) ->
  (espe (dsnd ν) g <= espe (dfst ν) g')%E.
Proof.
  move => Hg Hg' Hpw.
  rewrite exp_dlet //.
  rewrite (_ : (fun p => espe (dunit p.2) g) = (fun p => g p.2));
    last by apply/funext => p; rewrite exp_dunit.
  rewrite [espe (dfst ν) g']exp_dlet //.
  rewrite (_ : (fun p => espe (dunit p.1) g') = (fun p => g' p.1));
    last by apply/funext => p; rewrite exp_dunit.
  rewrite /espe; apply: esum.le_sum.
  - move => p; apply: mule_ge0; first exact: Hg.
    by apply: lee_tofin; apply: ge0_mu.
  - move => p.
    case/boolP: (p \in dinsupp ν) => [hp | /dinsuppPn hp].
    + apply: lee_wpmul2r; first by apply: lee_tofin; apply: ge0_mu.
      exact: Hpw _ hp.
    + by rewrite hp !mule0.
Qed.

Lemma ehl_prhl c d f g f' g' P Q:
  (forall m : cmem, 0 <= g m)%E ->
  (forall m : cmem, 0 <= g' m)%E ->
  ehl f' d g' ->
  @prhl ps P d c Q ->
  (forall m, exists m', f' m' <= f m /\ P (m',m))%E ->
  (forall m' m, Q (m',m) -> g m <= g' m')%E ->
  ehl f c g.
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

(* -------------------------------------------------------------------- *)

Inductive derivable : phi -> cond -> cmd -> cond -> Prop :=
  | H_Skip : forall f cl,
      derivable cl f skip f
  | H_Abort : forall f g cl,
      (forall m, (0 <= f m)%E) ->
      derivable cl f abort g
  | H_Asgn : forall {T : IhbType.type} x (e:expr T) f cl,
      derivable cl (fun m => f m.[x <- `[{e}] m]) (x <<- e) f
  | H_Random : forall {T : IhbType.type} x (e:dexpr T) f cl,
    let g m :=
      espe (\dlet_(v <- `[{e}] m) (dunit m.[x <- v])) f
    in
    derivable cl g (x <$- e) f
  | H_Seq : forall f c d g h cl,
      (forall m, (0 <= g m)%E) ->
      derivable cl h d g -> derivable cl f c h -> derivable cl f (c;;d) g
  | H_If : forall f g (e: bexpr) (c1 c2:cmd) cl,
      derivable cl (lift (esem e) f) c1 g ->
      derivable cl (lift (fun m => negb (esem e m)) f) c2 g ->
      derivable cl f (If e then c1 else c2)%S g
  | H_While : forall f (e: bexpr) (c:cmd) cl,
      (forall m, 0 <= f m)%E ->
      derivable cl (lift (esem e) f) c f ->
      derivable cl f (While e Do c) (lift (fun m => negb (esem e m)) f)
  | H_Consequence : forall f' g' f g (c : cmd) cl,
      derivable cl f' c g' ->
      (forall m mu,  espe mu g' <= f' m -> espe mu g <= f m)%E ->
      derivable cl f c g
  | H_khl : forall P Q c cl,
     derivable2 cl P c (fun _ => Q) -> derivable cl P c Q
  with derivable2 : phi -> cond -> cmd -> cond2 -> Prop :=
   | H_hl: forall P Q c cl,
       (forall s0, derivable cl (bound P s0) c (Q s0)) ->
       derivable2 cl P c Q
   | H_call : forall cl (f: ident),
       derivable2 cl (get_pre (cl f)) (call f) (get_post (cl f))
   | H_rec : forall P Q c cl cl',
       (forall p', derivable2 cl (get_pre (cl p')) (ps p') (get_post (cl p'))) ->
       derivable2 cl P c Q ->
       derivable2 cl' P c Q
   | H_adapt : forall (P1 P2 : cond) (Q1 Q2 : cond2) c cl,
       derivable2 cl P2 c Q2 ->
       (forall m mu,  espe mu (Q2 m) <= P2 m -> espe mu (Q1 m) <= P1 m)%E ->
       derivable2 cl P1 c Q1.

Parameter C : cond2.

Definition cl_mgt : phi :=
  fun (f:ident) => ((fun _ => +oo)%E, (fun s0 s => ((ssem_ ps (ps f) s0) s)%:E) (* C *)).

From xhl.hl Require hl.

Lemma rel_complete_d (c : cmd) (f g : cond) :
  (forall m,  (0 <= f m)%E) ->
  (forall m , (0 <= g m)%E) ->
  ehl_ ps f c g -> derivable cl_mgt f c g.
Proof.
elim: c f g => [ | | T x e | T x d | e c1 ih1 c2 ih2 | e c0 ih0 | c1 ih1 c2 ih2 | f ] P Q Hf Hg Hhl.
- (* abort *) exact: H_Abort.
- (* skip *)
  apply: (H_Consequence Q Q) => //.
  + exact: H_Skip.
  + move=> m mu H1.
    apply:  (le_trans H1).
    by move : (Hhl m); rewrite ssem_skipE exp_dunit.
- (* assign *)
  apply: (H_Consequence (fun m => Q m.[x <- `[{e}] m]) Q).
    + exact: H_Asgn.
    + move=> m mu H1.
      apply:  (le_trans H1).
      by move : (Hhl m); rewrite ssem_assnE exp_dunit.
- (* random *)
  apply: (H_Consequence
            (fun m => espe (\dlet_(v <- `[{d}] m) (dunit m.[x <- v])) Q) Q).
  + exact: H_Random.
  + move=> m mu H1.
    apply: (le_trans H1).
    by move : (Hhl m); rewrite ssem_rndE.
- (* if *)
  apply: H_If.
  + rewrite /lift.
    apply: ih1 => m //.
    + by case (`[{e}] m).
    + move: (Hhl m).
      rewrite ssem_ifE.
      case (`[{e}] m) => // _.
      exact : leey.
  + rewrite /lift.
    apply: ih2 => m //.
    + by case (~~ `[{e}] m).
    +  move: (Hhl m).
      rewrite ssem_ifE.
      case (`[{e}] m) => //= _.
      exact : leey.
- (* while *)
  pose I : cond := fun m => espe (ssem_ ps (While e Do c0) m) Q .
  have Ipos :  forall m : cmem, (0%R <= I m)%E.
  + move => m; subst I=> /=.
    rewrite /espe sum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply (H_Consequence I (lift (`[{~~e}]) I)).
  + apply: H_While => //.
    apply ih0 => //.
    + by move => m; rewrite /lift; case (`[{e}] m).
    rewrite /ehl /lift.
    move => m; case_eq (`[{e}] m) => He; last first. exact : leey.
    subst I => /=.
    by rewrite -exp_dlet // ssem_whileS // ssem_seqE.
  + move => m mu H1.
    move : (Hhl m).
    apply: le_trans.
    move : H1; subst I => //=.
    apply: le_trans.
    apply esum.le_sum.
    + by move => x; rewrite mule_ge0 //= lee_tofin.
    move => x; rewrite /lift.
    case_eq ( ~~ `[{e}] x) => ? //=.
    rewrite lee_pmul //=.
    + by rewrite lee_fin.
    + by rewrite ssem_while0 // exp_dunit.
    + rewrite lee_pmul //= ?lee_fin //.
      exact : leey.
- (* seq *)
  pose R : cond := fun x : cmem => espe (ssem_ ps c2 x) Q.
  have Rpos :   forall m : cmem, (0%R <= R m)%E.
  + move => m; subst R => //=; rewrite /espe.
    rewrite /espe sum_ge0 // => x.
    by rewrite mule_ge0 //= lee_tofin.
  apply: (H_Seq _ _ _ _ R) => //=.
  + apply ih2 => //=.
  + apply ih1 => //=.
    move => m.
    by move : (Hhl m);  rewrite ssem_seqE exp_dlet.
- (* call *)
  apply: H_khl.
  apply: (H_adapt _ (get_pre (cl_mgt f)) _ (get_post (cl_mgt f))).
  + by apply: H_call; right.
  + move=> m0 mu h.
    move: (Hhl m0).
    rewrite hl.ssem_call_eq.
    apply: le_trans.
    simpl in h.
    rewrite /espe.
    rewrite /espe in h.
Qed.

Lemma rel_complete (c : cmd) (P : assn) (Q : assn2) :
  khl_ ps P c Q -> derivable2 cl_mgt P c Q.
Proof.
move=> /khl_hl h; apply: H_hl => s0; exact: (rel_complete_d (h s0)).
Qed.


Theorem hoare_complete: forall P c Q,
  kehl_ ps P c Q -> derivable2 empty_phi P c Q.
Proof.
Admitted.


Theorem khoare_sound0 P c Q : derivable2 empty_phi P c Q -> kehl_ ps P c Q.
Proof.
  Admitted.


End EHL.
