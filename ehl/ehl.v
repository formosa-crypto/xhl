(* -------------------------------------------------------------------- *)
(* (* ----------------- *) Require Import Setoid Morphisms. *)
From HB Require Import structures.
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

Definition cond2 := cmem -> \bar pwhile.R -> cmem -> \bar pwhile.R.

Definition kehl_ (ps:psi) f c (g: cond2) :=
  forall m : cmem, (espe (ssem_ ps c m) (fun m' => g m ((ssem_ ps c m m')%:E) m') <= f m)%E.

Notation kehl   := (kehl_ ps).

Definition bound {T : choiceType} (g : T -> \bar R) m0 m :=
  if (m == m0) then (g m) else +oo%E.

Lemma kehl_ehl P c Q :
  kehl P c Q <-> (forall s0, ehl (bound P s0) c (fun s => Q s0 ((ssem_ ps c s0 s)%:E) s)).
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
  kehl P c (fun _ _ => Q) <-> ehl P c Q.
Proof.
  by split; move => h m; apply h.
Qed.

Lemma kehl_conseq c f f' (g g' : cond2):
  kehl f' c g' ->
  (forall m d,  espe d (fun m' => g' m ((d m')%:E) m') <= f' m ->
           espe d (fun m' => g m ((d m')%:E) m') <= f m)%E ->
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

(* (** Hoare triple for a com with procedure context **) *)

(* Definition hoare_triple_ctx (cl : phi) ps (P: cond) (Q: cond2) (c: cmd) := *)
(*   (forall p, kehl_ ps (get_pre (cl p)) (call p) (get_post (cl p))) -> *)
(*   kehl_ ps P c Q. *)

(* (** Hoare triple for a procedure with procedure context **) *)

(* Definition hoare_triple_proc_ctx (cl : phi) (ps_init: ident -> (@cmd_ ident cmem ident)):= *)
(*   forall p ps, hoare_triple_ctx cl ps *)
(*             (get_pre (cl p)) *)
(*             (get_post (cl p)) *)
(*             (ps_init p). *)

(* From xhl.hl Require hl. *)

(* Lemma recursive_proc ps' cl' : *)
(*   (forall p m, 0 <= (get_pre (cl' p)) m)%E -> *)
(*   (forall p m d m', 0 <= (get_post (cl' p)) m d m')%E -> *)
(*   hoare_triple_proc_ctx cl' ps' -> *)
(*   (forall p, kehl_ ps' (get_pre (cl' p)) *)
(*           (call p) *)
(*           (get_post (cl' p))). *)
(* Proof. *)
(*   move => Hpre Hpost h p s. *)
(*   rewrite /espe  esum_sum';last first. *)
(*     - move => x; rewrite mule_ge0 //. *)
(*       rewrite lee_tofin //. *)
(*    rewrite !hl.test8. *)
(*    apply esum_dlim_r. *)
(*     + move => ????. *)
(*      apply mono_ssem_aux. *)
(*      by apply homo_ubnf. *)
(*     + exact: (Hpost p). *)
(*   move => n. *)
(*   (*This should be a lemma*) *)
(*   rewrite hl.ssem_ubnf_dnull hl.ubnf_ssem (hl.test9 _ _ _ _ ps') hl.test5. *)
(*   revert p; revert s. *)
(*   elim : n => [| n Hn]. *)
(*   + move => ??. rewrite hl.ssem_false_ps. *)
(*     under eq_esum do  rewrite dnullE mule0. *)
(*     by rewrite esum1. *)
(*   move => s p. *)
(*   rewrite (hl.inline2_split n 1) //=. *)
(*   rewrite -esum_sum';last first. *)
(*   + move => x; rewrite mule_ge0 //. *)
(*       rewrite lee_tofin //. *)
(*   apply h.  => // p0 s0. *)
(*   rewrite /espe esum_sum';last first. *)
(*   + move => x; rewrite mule_ge0 //. *)
(*       rewrite lee_tofin //. *)
(*   by apply: Hn. *)
(* Qed. *)

(* (** Modular Hoare Triple Verification **) *)

(* Theorem recursion_hoare_triple : *)
(*   forall P Q c cl ps, *)
(*     (forall p m, 0 <= (get_pre (cl p)) m)%E -> *)
(*     (forall p m m', 0 <= (get_post (cl p)) m m')%E -> *)
(*     hoare_triple_proc_ctx cl ps  -> *)
(*     hoare_triple_ctx cl ps P Q c -> *)
(*     kehl_ ps P c Q . *)
(* Proof. *)
(*   move => ????? Hpre Hpost H H0. *)
(*   apply H0. *)
(*   by apply: recursive_proc. *)
(* Qed. *)

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

End EHL.

Definition cond2_mono (c:  cmem -> \bar pwhile.R -> cmem -> \bar pwhile.R) :=
      forall (mu mu' : {distr cmem / R}),
        (forall (x0 : cmem), mu x0 <= mu' x0) ->
        (forall x x' : cmem, c x ((mu x')%:E) x' <= c x ((mu' x')%:E) x')%E.

Definition cl_mono (cl: ident -> clause) := forall (f: ident), cond2_mono (snd (cl f)).

Definition cl_pre_pos (cl: ident -> clause) :=
  forall (f: ident), (forall x , 0 <= (get_pre (cl f)) x )%E.

Definition cl_post_pos (cl: ident -> clause) :=
  forall (f: ident), (forall x mu x', 0 <= (get_post (cl f)) x mu x')%E.

HB.mixin Record isPhi (cl : ident -> clause) :=
  {
    post_mono : cl_mono cl;
    pre_pos : cl_pre_pos cl;
    post_pos : cl_post_pos cl;
  }.

HB.structure Definition Phi :=  {f of @isPhi f}.

Notation "'phi'" := (@Phi.type) (at level 0, format "'phi'"): type_scope.

(* -------------------------------------------------------------------- *)

Section EHL.
Context {ps: ident -> (@cmd_ ident cmem ident)}.

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
     derivable2 cl P c (fun _ _ => Q) -> derivable cl P c Q
  with derivable2 : phi -> cond -> cmd -> cond2 -> Prop :=
  | H_hl: forall P Q c cl,
      (forall m mu m', (0 <= Q m mu m')%E) ->
      cond2_mono Q ->
       (forall s0, derivable cl (bound P s0) c (fun s => Q s0 ((ssem_ ps c s0 s)%:E) s)) ->
       derivable2 cl P c Q
   | H_call : forall cl (f: ident),
       derivable2 cl (get_pre (cl f)) (call f) (get_post (cl f))
   | H_rec : forall P Q c cl cl',
       (forall p', derivable2 cl (get_pre (cl p')) (ps p') (get_post (cl p'))) ->
       derivable2 cl P c Q ->
       derivable2 cl' P c Q
   | H_adapt : forall (P1 P2 : cond) (Q1 Q2 : cond2) c cl,
       derivable2 cl P2 c Q2 ->
       (forall m mu,  espe mu (fun m' => Q2 m ((mu m')%:E) m') <= P2 m ->
                 espe mu (fun m' => Q1 m ((mu m')%:E) m') <= P1 m)%E ->
       derivable2 cl P1 c Q1.

Definition empty_precondition : cond := (fun _ => +oo)%E.

Definition empty_postcondition :  cond2 := (fun _ _ _ => 0)%E.

Definition empty_clause : clause := (empty_precondition, empty_postcondition).

Definition cl_empty: ident -> clause := fun _ => empty_clause.

Lemma post_mono_cl_empty : cl_mono cl_empty.
Proof.
  by rewrite /cl_mono / cond2_mono.
Qed.

Lemma pre_pos_cl_empty : cl_pre_pos cl_empty.
Proof.
  move => f m //=.
  exact: leey.
Qed.

Lemma post_pos_cl_empty : cl_post_pos cl_empty.
Proof.
  by [].
Qed.

HB.instance Definition _ :=
  @isPhi.Build cl_empty  post_mono_cl_empty pre_pos_cl_empty post_pos_cl_empty.

Definition cl_mgt : ident -> clause :=
  fun (f:ident) => ((fun _ => 0)%E,
                  (fun s0 r s =>
                     if (r <= ((ssem_ ps (ps f) s0) s)%:E)%E then 0%E else +oo%E)
                ).

Lemma post_mono_cl_mgt : cl_mono cl_mgt.
Proof.
  move => f mu mu' H x x'.
  rewrite /cl_mgt //=.
  case_eq  (EFin(mu x') <= (ssem_ ps (ps f) x x')%:E)%E.
  case  (EFin(mu' x') <= (ssem_ ps (ps f) x x')%:E)%E => //=.
  case_eq (EFin(mu' x') <= (ssem_ ps (ps f) x x')%:E)%E => //=.
  move =>  H1  H2.
  have : (EFin(mu x') <= (ssem_ ps (ps f) x x')%:E)%E = true.
  + by apply: (le_trans (H x')).
  by rewrite H2.
Qed.

Lemma pre_pos_cl_mgt : cl_pre_pos cl_mgt.
Proof.
  by [].
Qed.

Lemma post_pos_cl_mgt : cl_post_pos cl_mgt.
Proof.
  move => f x r x' //=.
  by case: (r <= EFin (ssem_ ps (ps f) x x'))%E.
Qed.

HB.instance Definition _ :=
  @isPhi.Build cl_mgt  post_mono_cl_mgt  pre_pos_cl_mgt post_pos_cl_mgt.

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
    rewrite /lift.
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
    simpl in h.
    have Hpos : forall s,
        (0 <= (if (EFin (mu s) <= EFin ((ssem_ ps (ps f) m0) s))%E then 0%E else +oo%E)
                * (mu s)%:E)%E.
    { move=> s; apply: mule_ge0; last exact: (lee_tofin (ge0_mu _ s)).
      by case: ifP => _; [exact: lexx | exact: leey]. }
    have Hsum0 :
      (esum.sum (fun s => (if (EFin (mu s) <= EFin ((ssem_ ps (ps f) m0) s))%E
                        then 0%E else +oo%E)
                         * (mu s)%:E) = 0)%E.
    { apply/eqP; rewrite eq_le; apply/andP; split; last first.
      - by apply: sum_ge0; exact: Hpos.
      rewrite /espe /cl_mgt /get_pre /get_post /= in h.
      exact: h. }
    have Hesum :
        (\esum_(i in (@classical_sets.setT cmem))
           ((if (EFin (mu i) <= EFin ((ssem_ ps (ps f) m0) i))%E then 0%E else +oo%E)
              * (mu i)%:E) = 0)%E.
    { rewrite -esum_sum'; last exact: Hpos.
      exact: Hsum0. }
    have Hzero := @esum_eq0P _ _ _ _ (fun x _ => Hpos x) Hesum.
    have Hdom : forall s, (EFin (mu s) <= EFin ((ssem_ ps (ps f) m0) s))%E.
    { move=> s; rewrite leNgt; apply/negP => Hgt.
      have Hmu : (0 < (mu s)%:E)%E.
        by rewrite lte_fin; exact: (le_lt_trans (ge0_mu _ s) Hgt).
      move: (Hzero s Logic.I); rewrite (lt_geF Hgt) => Habs.
      have Hgt0 : (0 < +oo * (mu s)%:E)%E
        by apply: mule_gt0; [exact: lt0y | exact: Hmu].
      by rewrite Habs ltxx in Hgt0. }
    move: (Hhl m0); rewrite hl.ssem_call_eq; apply: le_trans.
    rewrite /espe; apply: esum.le_sum.
    - move=> s; apply: mule_ge0; first exact: Hg.
      exact: (lee_tofin (ge0_mu _ s)).
    - move=> s; apply: (lee_wpmul2l (Hg s)).
      exact: (lee_tofin (Hdom s)).
Qed.

Lemma rel_complete (c : cmd) (P : cond) (Q : cond2) :
  (forall m,  (0 <= P m)%E) ->
  (forall m mu m', (0 <= Q m mu m')%E) ->
  cond2_mono Q ->
  kehl_ ps P c Q -> derivable2 cl_mgt P c Q.
Proof.
  move=> h1 h2 h3 /kehl_ehl h; apply: H_hl => //= s0. apply rel_complete_d => //.
  by move => m; rewrite /bound; case (m == s0).
Qed.

Theorem hoare_complete: forall P c (Q: cmem -> cmem -> \bar R),
  (forall m,  (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  kehl_ ps P c (fun s0 _ s =>Q s0 s) -> derivable2 cl_empty P c (fun s0 _ s =>Q s0 s).
Proof.
move=> P c Q h1 h2 Hvalid.
apply: (H_rec _ _ _ cl_mgt); last first.
- by apply rel_complete.
- move=> p'; apply: rel_complete => //.
  + move=> m mu m'; rewrite /get_post /cl_mgt /=.
    by case: ifP => _; [exact: lexx | exact: leey].
  + rewrite /cond2_mono /get_post //=.
    move => mu mu' hmono x x'.
    case_eq  (EFin(mu x') <= (ssem_ ps (ps p') x x')%:E)%E.
    case  (EFin(mu' x') <= (ssem_ ps (ps p') x x')%:E)%E => //=.
    case_eq (EFin(mu' x') <= (ssem_ ps (ps p') x x')%:E)%E => //=.
    move => H1 H2.
    have : (EFin(mu x') <= (ssem_ ps (ps p') x x')%:E)%E = true.
     + by apply: (le_trans (hmono x')).
    by rewrite H2.
  + move=> m.
    rewrite /get_pre /cl_mgt /= /espe.
    under esum.eq_sum do rewrite lexx mul0e.
    by rewrite esum.sum0.
Qed.

(* -------------------------------------------------------------------- *)
(* Soundness                                                            *)
(* -------------------------------------------------------------------- *)
Definition aehl (l : (ident * cmem) -> {distr cmem / R})
    (f : cond) (c : cmd) (g : cond) :=
  forall m : cmem, (espe (ssem_aux l c m) g <= f m)%E.

Definition akehl (l : ident * cmem -> {distr cmem/R})
  (f : cond) (c : cmd) (g : cond2) :=
  forall m : cmem, (espe (ssem_aux l c m) (fun m' => g m ((ssem_aux l c m m')%:E) m') <= f m)%E.

Lemma aehl_skip l f g :
  (forall m, (g m <= f m)%E) -> aehl l f skip g.
Proof. by move => h m /=; rewrite exp_dunit. Qed.

Lemma aehl_abort l f g :
  (forall m, (0 <= f m)%E) -> aehl l f abort g.
Proof.
move => h m /=.
rewrite /espe (@esum.eq_sum _ _ _ (fun _ => 0%E)).
- by rewrite esum.sum0.
- by move => x; rewrite dnullE mule0.
Qed.

Lemma aehl_assgn l {T : IhbType.type} f x (e : expr T) :
  aehl l (fun m => f m.[x <- `[{e}] m]) (x <<- e) f.
Proof. by move => m /=; rewrite exp_dunit. Qed.

Lemma aehl_rnd l {T : IhbType.type} f x (e : dexpr T) :
  let g m := espe (\dlet_(v <- `[{e}] m) (dunit m.[x <- v])) f in
  aehl l g (x <$- e) f.
Proof. by move => g m /=. Qed.

Lemma aehl_seq l f g h c1 c2:
  (forall m, (0 <= g m)%E) ->
  aehl l f c1 h -> aehl l h c2 g -> aehl l f (c1 ;; c2) g.
Proof.
move => Hg h1 h2 m /=.
rewrite exp_dlet //.
apply: (@le_trans _ _ (espe (ssem_aux l c1 m) h)); last exact: h1.
rewrite /espe; apply: esum.le_sum.
- move => x; apply: mule_ge0; last by apply: lee_tofin; apply: ge0_mu.
  apply: sum_ge0 => x'; apply: mule_ge0; first exact: Hg.
  by apply: lee_tofin; apply: ge0_mu.
- move => x; apply: lee_wpmul2r.
  + by apply: lee_tofin; apply: ge0_mu.
  + exact: h2.
Qed.

Lemma aehl_if l f (e : bexpr) c1 c2 g :
  aehl l (lift (esem e) f) c1 g ->
  aehl l (lift (fun m => negb (esem e m)) f) c2 g ->
  aehl l f (If e then c1 else c2) g.
Proof.
move => Hc1 Hc2 m /=.
case h: (`[{e}] m).
- by move : (Hc1 m); rewrite /lift h /=.
- by move : (Hc2 m); rewrite /lift h /=.
Qed.

Lemma aehl_conseq l c f g f' g':
  aehl l f' c g' ->
  (forall m d,  espe d g' <= f' m -> espe d g <= f m)%E ->
  aehl l f c g.
Proof. by move => h' hc m; apply hc. Qed.

Lemma ssem_aux_whileE l (e : bexpr) (c : @cmd_ ident cmem ident) m :
  ssem_aux l (While e Do c) m = \dlim_(n) ssem_aux l (whilen e c n) m.
Proof.
rewrite /=; apply: eq_dlim => n0; move: m; elim: n0 => [|n0 IHn0] s //=.
case: (`[{e}] s) => //=.
by apply: eq_in_dlet => [s' _|//]; rewrite IHn0.
Qed.

Lemma aehl_while l (e : bexpr) c f :
  (forall m, 0 <= f m)%E ->
  aehl l (lift (esem e) f) c f ->
  aehl l f (While e Do c) (lift (fun m => negb (esem e m)) f).
Proof.
move => Hf.
have Hpos : forall m : cmem, (0%R <= (if ~~ `[{e}] m then f m else +oo))%E.
+ by move => m; case (`[{e}] m) => //=.
rewrite /lift => Hi m.
rewrite ssem_aux_whileE /espe esum_sum'; last first.
- by move => x; rewrite mule_ge0 // lee_tofin.
apply: (esum_dlim_r (hl.hmono_whilen l e c m)) => //.
move => n; rewrite -esum_sum'; last first.
- by move => x; rewrite mule_ge0 // lee_tofin.
move : m.
elim : n.
+ by apply aehl_abort.
+ move => n Hi'.
  apply aehl_if => //=.
  + by apply: (aehl_seq _ _ _ f).
  + by apply aehl_skip.
Qed.

Lemma akehl_aehl l P c Q :
  akehl l P c Q <-> (forall s0, aehl l (bound P s0) c (fun s => Q s0 ((ssem_aux l c s0 s)%:E) s)).
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

Lemma aehl_akehl l P c Q : akehl l P c (fun _ _ => Q) <-> aehl l P c Q.
Proof.
  by split; move => h m; apply h.
Qed.

Definition valid_cl cl :=
  forall (f:ident), kehl_ ps (get_pre (cl f)) (call f) (get_post (cl f)).

Definition valid_cl_n n cl :=
  forall  (f:ident), akehl (ubnf ps n) (get_pre (cl f)) (call f) (get_post (cl f)).

Lemma valid_cl_n_dn n (cl: phi) :
    valid_cl_n n.+1 cl -> valid_cl_n n cl.
Proof.
move=> H f m.
move : (H f m).
rewrite /espe.
apply: le_trans.
apply: esum.le_sum.
+ move =>x.
  rewrite mule_ge0 //=  ?lee_tofin //=.
  exact: post_pos.
move => x.
rewrite lee_pmul //= ?lee_tofin //.
+ exact: post_pos.
+ apply: (post_mono f) => x'.
  by apply: (homo_ubnf (n:=n) (p:=n.+1)).
+ by apply: (homo_ubnf (n:=n) (p:=n.+1)).
Qed.

Lemma valid_cl_to_n (cl: phi) :
  valid_cl cl -> forall n, valid_cl_n n cl.
Proof.
move=> Hv n f m.
move: (Hv f m).
rewrite ssem_callE.
apply: le_trans.
rewrite /espe.
apply: esum.le_sum.
+ move =>x.
  rewrite mule_ge0 //= ?lee_tofin //=.
  exact: post_pos.
move => x.
rewrite lee_pmul //= ?lee_tofin //.
+ exact: post_pos.
+ apply: (post_mono f) => x'.
  apply: dlim_ub => ????.  exact: homo_ubnf.
+ apply: dlim_ub => ????.  exact: homo_ubnf.
Qed.

Lemma cl_calls (cl cl': phi):
  (forall (f : ident) (n : nat), valid_cl_n n cl ->
        akehl (ubnf ps n) (get_pre (cl f)) (ps f) (get_post (cl f))) ->
  (forall (f : ident) (n : nat),
      valid_cl_n n cl' ->
      akehl (ubnf ps n) (get_pre (cl f)) (call f) (get_post (cl f))).
Proof.
move => IH_body f n.
elim: n f => [|k IHk] f Hvk m.
+ rewrite /espe //=.
  under esum.eq_sum do rewrite dnullE  mule0.
  rewrite esum.sum0.
 exact: pre_pos.
apply: (IH_body f k _ m).
move=> g.
apply: IHk => //.
by apply: valid_cl_n_dn.
Qed.

Scheme derivable_min := Minimality for derivable Sort Prop
  with derivable2_min := Minimality for derivable2 Sort Prop.
Combined Scheme derivable_mut from derivable_min, derivable2_min.

Lemma soundness_n :
  (forall (cl: phi) P c Q, derivable cl P c Q ->
     forall n, valid_cl_n n cl -> aehl (ubnf ps n) P c Q) /\
    (forall (cl: phi) P c Q, derivable2 cl P c Q ->
     forall n, valid_cl_n n cl -> akehl (ubnf ps n) P c Q).
Proof.
apply: derivable_mut.
- (* H_Skip *) by move=> *; exact: aehl_skip.
- (* H_Abort *) by move=> *; exact: aehl_abort.
- (* H_Asgn *) by move=> *; exact: aehl_assgn.
- (* H_Random *) by move=> *; exact: aehl_rnd.
- (* H_Seq *)
  move=> f c d g h cl Hg ? IHd ? IHc n Hv.
  by apply: (aehl_seq _ _ _ _ _ _ Hg (IHc n Hv) (IHd n Hv)).
- (* H_If *)
  move => f g e c1 c2 cl ? IH1 ? IH2 n Hv.
  by apply: aehl_if;[exact: IH1 | exact: IH2].
- (* H_While *)
  move => f e c cl m ? IH n Hv; apply: aehl_while => //;  exact: IH.
- (* H_Consequence *)
  move => f' g' f g c cl ? HI H n Hv.
  apply: aehl_conseq. apply: HI => //. apply H.
- (* H_khl *)
  move => P Q c cl ? IH n Hv; rewrite -aehl_akehl; exact: IH.
- (* H_hl *)
  move=> P Q c cl Hpos Hmono ? IH n Hv. rewrite akehl_aehl=> s0.
  move => m.
  move :(IH s0 n Hv m).
  apply: le_trans.
  rewrite /espe.
  apply esum.le_sum.
  +  by move => x; rewrite mule_ge0 // lee_tofin.
  move => x.
  apply: lee_pmul => //=.
  + by rewrite lee_tofin.
  + apply Hmono => ?.
    rewrite hl.test8.
    apply: dlim_ub => ????.
    apply mono_ssem_aux.
    by apply homo_ubnf.
- (* H_call *) by move=> cl f n Hv; exact: Hv.
- (* H_rec *)
  move=> P Q c cl cl' _ IH_body _ IH_c n Hv; apply: (IH_c n).
  move=> f; apply (cl_calls _ cl') => //=.
- (* H_adapt *)
  move=> P1 P2 Q1 Q2 c cl ? HI H n Hv m.
  exact :(H m (ssem_aux (ubnf ps n) c m) (HI n Hv m)).
Qed.

Theorem hoare_sound (cl:phi) P c Q :
  (forall m, (0 <= P m)%E) ->
  (forall m, (0 <= Q m)%E) ->
  valid_cl cl -> derivable cl P c Q -> ehl_ ps P c Q.
Proof.
  move => HP HQ Hv Hd m.
  rewrite /espe  esum_sum';last first.
  - move => x; rewrite mule_ge0 //.
    rewrite lee_tofin //.
  rewrite hl.test8.
  apply: esum_dlim_r => //.
  + move => ????.
     apply mono_ssem_aux.
     by apply homo_ubnf.
  move => n.
  have Hvn : valid_cl_n n cl := @valid_cl_to_n cl Hv n.
  have Hahl := (proj1 soundness_n  _ _ _ _ Hd n Hvn).
  rewrite -esum_sum';last first.
  + move => x; rewrite mule_ge0 //.
     rewrite lee_tofin //.
  exact: (Hahl m).
Qed.

Corollary hoare_sound0 P c Q :
  (forall m, (0 <= P m)%E) ->
  (forall m, (0 <= Q m)%E) ->
  derivable cl_empty P c Q -> ehl_ ps P c Q.
Proof.
  move => HP HQ HD.
  apply: (hoare_sound cl_empty) => //.
  rewrite /valid_cl /kehl_ => //=.
  move => *.
  rewrite /empty_precondition.
  exact: leey.
Qed.

Theorem khoare_sound (cl:phi) P c (Q: cmem -> cmem -> \bar R) :
  (forall m, (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  valid_cl cl -> derivable2 cl P c (fun s0 _ s =>Q s0 s) -> kehl_ ps P c (fun s0 _ s =>Q s0 s).
Proof.
  move => HP HQ Hv Hd m.
  rewrite /espe  esum_sum';last first.
  - move => x; rewrite mule_ge0 //.
    rewrite lee_tofin //.
  rewrite hl.test8.
  apply: esum_dlim_r => //.
  + move => ????.
     apply mono_ssem_aux.
     by apply homo_ubnf.
  move => n.
  have Hvn : valid_cl_n n cl := @valid_cl_to_n cl Hv n.
  have Hahl := (proj2 soundness_n  _ _ _ _ Hd n Hvn).
  rewrite -esum_sum';last first.
  + move => x; rewrite mule_ge0 //.
    rewrite lee_tofin //.
  move : (Hahl m).
  apply: le_trans.
  rewrite /espe.
  apply esum.le_sum => //.
  + move => x; rewrite mule_ge0 //.
    rewrite lee_tofin //.
Qed.

Corollary khoare_sound0 P c (Q: cmem -> cmem -> \bar R) :
  (forall m,  (0 <= P m)%E) ->
  (forall m m', (0 <= Q m m')%E) ->
  derivable2 cl_empty P c (fun s0 _ s =>Q s0 s) -> kehl_ ps P c (fun s0 _ s =>Q s0 s).
Proof.
  move => HP HQ HD.
  apply: (khoare_sound cl_empty) => //.
  rewrite /valid_cl /kehl_ => //=.
  move => *.
  rewrite /empty_precondition.
  exact: leey.
Qed.

End EHL.
