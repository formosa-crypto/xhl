(* -------------------------------------------------------------------- *)
(* (* ----------------- *) Require Import Setoid Morphisms. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis Require Import esum ereal.
From mathcomp.experimental_reals  Require Import realseq realsum distr edistr.
From mathcomp    Require  finmap.
From xhl.pwhile Require Import notations inhabited pwhile psemantic range.


From xhl.hl Require Import hl.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

(* -------------------------------------------------------------------- *)

Definition ehl f c g :=
  forall m : cmem, (espe (ssem c m) g <= f m)%E.

(* -------------------------------------------------------------------- *)

Section Ehl.

  Implicit Types  (f g h : cmem -> \bar pwhile.R).

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
    (espe (ssem c1 m) h <= f m)%E ->
    (forall m : cmem, espe (ssem c2 m) g <= h m)%E ->
    (espe(\dlet_(m' <- ssem c1 m) ssem c2 m') g <= f m)%E.
  Proof.
    move => Hg h1 h2.
    rewrite exp_dlet //.
    apply: (@le_trans _ _ (espe (ssem c1 m) h)); last exact: h1.
    rewrite /espe; apply: esum.le_sum.
    - move => x; apply: mule_ge0; last by apply: lee_tofin; apply: ge0_mu.
      apply: sum_pos => x'; apply: mule_ge0; first exact: Hg.
      by apply: lee_tofin; apply: ge0_mu.
    - move => x; apply: mule_ge0; last by apply: lee_tofin; apply: ge0_mu.
      apply: (@le_trans _ _ (espe (ssem c2 x) g)); last exact: h2.
      apply: sum_pos => x'; apply: mule_ge0; first exact: Hg.
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

  Definition lift (b: bool) f (m: cmem) : \bar pwhile.R :=
    match b with
    | true => (f m)
    | false => +oo
    end.

  Definition ehll P f c g :=
    forall m : cmem,
      ((espe (ssem c m) g) <= lift (P m) f m)%E.

  Lemma ehl_if f (e : bexpr) c1 c2 g :
    ehll (esem e) f c1 g ->
    ehll (fun m => negb (esem e m)) f c2 g ->
    ehl f (If e then c1 else c2) g.
  Proof.
    move => Hc1 Hc2 m.
    rewrite ssemE.
    case h: (`[{e}] m).
    - move : (Hc1 m).
      by  rewrite h /=.
      move : (Hc2 m).
      by  rewrite h /=.
  Qed.

  (* -------------------------------------------------------------------- *)

  Lemma range_while e (c:cmd):
    forall m,  range (`[{~~e}]) (ssem_ (While e Do c) m).
  Proof.
    move => m.
    by apply (@hl_while _ _ xpredT e c).
  Qed.

  Lemma pr_while_e e (c:cmd):
    forall m, \P_[ssem_ (While e Do c) m] (`[{e}]) = 0%R.
  Proof.
    move => m.
    have := (@range_while e c m).
    move => /pr_range <-.
    apply eq_in_pr.
    move => ? ? //=.
    rewrite !unfold_in => //=.
    by rewrite Bool.negb_involutive.
  Qed.

  Definition lift' {T : choiceType} (mu : {distr T / R}) (P : pred T) (g : T -> \bar R) :=
  if (\P_[mu] P == 0)%R then (espe mu g) else +oo%E.

  Definition ehlr P f c g :=
    forall m : cmem, ((lift' (ssem c m) P g) <= f m)%E.

  Lemma ehl_while (e : bexpr) c f :
    (forall m, 0 <= f m)%E ->
    ehll (esem e) f c f ->
    ehlr (esem e) f (While e Do c) f.
  Proof.
    move => Hf Hi m.
    rewrite /lift'.
    case_eq (\P_[ssem (While e Do c) m] (`[{e}]) == 0%R);last first.
    + by rewrite (pr_while_e e c m) eq_refl.
    move => h.
    rewrite ssemE.
    clear h.
    rewrite /espe  esum_sum';last first.
    - move => x; rewrite mule_ge0 //.
      rewrite lee_tofin //.
    apply (esum_dlim_r (homo_whilen e c m) Hf).
    move => n; rewrite -esum_sum' => //;last first.
    - move => x; rewrite mule_ge0 // lee_tofin //.
    move : m.
    elim : n => /=.
    - by apply ehl_abort.
    move => n Hi'.
    apply ehl_if.
    - rewrite /ehll /lift => m0.
      case he: (`[{e}] m0).
       - rewrite ssemE.
         move : (Hi m0).
         rewrite /lift he => h1.
         by apply: (ehl_seq_m m0 _ _ f).
       apply (@leey R).
     move => m.
     case (~~ `[{e}] m) => //=.
      - exact : ehl_skip.
      apply (@leey R).
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
    - move => p; apply: mule_ge0; first exact: Hg'.
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
    prhl P d c Q ->
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

End Ehl.
