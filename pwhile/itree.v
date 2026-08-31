(* -------------------------------------------------------------------- *)
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import counting_distr.
(* ----------------- *) Require Import inhabited passn pwhile psemantic.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Interp.Recursion
  MonadState
  State
  StateFacts
  Rutt
  RuttFacts.

Import Basics.Monads.

From Paco Require Import paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope mem_scope.

Variant Rnd : Type -> Type :=
  | GetRnd : forall t : IhbType.type, {distr t / R} -> Rnd t.

Variant Call : Type -> Type :=
  | CallE (f:ident) (m: cmem): Call cmem.

Section ParSem.

  Context {E} {XI : Rnd -< E}.

  Local Notation continue_loop s := (ret (inl s)).
  Local Notation exit_loop s := (ret (inr s)).

  Definition isem_while_round {E}
    (sem_i: cmd -> cmem -> itree E cmem) (c : cmd) (e : bexpr) (m : cmem) :
    itree E (cmem + cmem) :=
    if esem e m then bind (sem_i c m) (fun m => continue_loop m)
    else exit_loop m.

  Definition isem_while_loop {E}
    (sem_i: cmd -> cmem -> itree E cmem)
    (c : cmd) (e:bexpr) (m : cmem) :
    itree E cmem :=
    ITree.iter (isem_while_round sem_i c e) m.

  Fixpoint com_sem (c : cmd) : cmem -> itree (Call +' E) cmem :=
    match c with
    | abort => fun _ => ITree.spin
    | skip => fun m => Ret m
    | x <<- e => fun m => Ret m.[x <- (esem e m)]
    | G x <<- e => fun m => Ret m.{x <- esem e m}
    | x <$- e => fun m =>
                   bind (trigger (GetRnd (esem e m)))
                     (fun t => Ret m.[x <- t])
    | Block bs Do c Return rs =>
    fun m => bind (com_sem c (minit m bs)) (fun m' => Ret (mret m m' rs))
    | If e then c1 else c2 =>
    fun m =>
      match esem e m with
      | true => com_sem c1 m
      | false => com_sem c2 m
      end
    | While e Do c => isem_while_loop com_sem c e
    | seqc c1 c2 => fun m => bind (com_sem c1 m) (fun m => com_sem c2 m)
    | pwhile.call f => fun m => bind (trigger (CallE f m)) (fun m => Ret m)
  end.

  Definition handle_Call (ps: ident -> cmd) :
    Call ~> itree (Call +' E) :=
    fun T (rc : Call T) =>
      match rc with
      | CallE f m => com_sem (ps f) m
      end.

  Definition interp_call (ps: ident -> cmd)
    T (t: itree (Call +' E) T) : itree E T :=
    interp_mrec (handle_Call ps) t.

End ParSem.

Section Misc.

  Lemma dlim_bumpE (T : choiceType) (f : nat -> {distr T / R}) :
    \dlim_(n) f n.+1 = dlim f.
  Proof. by apply/distr_eqP/dlim_bump. Qed.

  Lemma dlim_sandwich (T : choiceType) (f g : nat -> {distr T / R}) :
    homo f -> homo g ->
    (forall n, f n <=1 g n) -> (forall n, g n <=1 f (n + n)%N) ->
    dlim f = dlim g.
  Proof.
  move=> hf hg le_fg le_gf; apply/distr_eqP => x; apply/eqP; rewrite eq_le.
  apply/andP; split; first exact: le_dlim.
  apply: leub_dlim => n y.
  by apply/(le_trans (le_gf n y))/dlim_ub.
  Qed.

  Lemma ubnS {A : choiceType} (f : A -> Distr A) (t : pred A) n a :
    ubn f t n.+1 a = if t a then \dlet_(x <- f a) ubn f t n x else dunit a.
  Proof. by []. Qed.

End Misc.

Section PropSem.

  Context {T : choiceType}.

  Fixpoint dinterp' (t : itree' Rnd T) (n : nat) : {distr T / R} :=
    if n is n.+1 then
      match t with
      | RetF r => dunit r
      | TauF t => dinterp' (observe t) n
      | VisF _ e k =>
          match e in Rnd A return (A -> itree Rnd T) -> {distr T / R} with
          | GetRnd _ mu =>
              fun k0 => \dlet_(t <- mu) (dinterp' (observe (k0 t)) n)
          end k
      end
    else dnull.

  Definition dinterp (t : itree Rnd T) : {distr T / R} :=
    dlim (dinterp' (observe t)).

  Lemma le_dinterp'_n (t : itree' Rnd T) n : dinterp' t n <=1 dinterp' t n.+1.
  Proof.
  elim: n t => [|n ih] t x /=; first exact: lef_dnull.
  case: t => [r|t|A e k] //=; case: e k => t0 mu k /=.
  by apply/le_in_dlet => // v _; apply: ih.
  Qed.

  Lemma homo_dinterp' (t : itree' Rnd T) : homo (dinterp' t).
  Proof.
  move=> n m; elim: m n => [|m ihm] n; first by rewrite leqn0 => /eqP ->.
  rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le x.
  by apply/(le_trans (ihm _ le x))/le_dinterp'_n.
  Qed.

  Lemma le_dinterp'_dinterp (t : itree Rnd T) n :
    dinterp' (observe t) n <=1 dinterp t.
  Proof. by rewrite /dinterp; apply: dlim_ub; apply: homo_dinterp'. Qed.

  Lemma le_dinterp'_vis (t0 : IhbType.type) (mu : {distr t0 / R})
    (k : t0 -> itree Rnd T) n :
    dinterp' (observe (Vis (GetRnd mu) k)) n <=1 \dlet_(v <- mu) dinterp (k v).
  Proof.
  case: n => [|n] x; first exact: lef_dnull.
  by apply/le_in_dlet => // v _; apply: le_dinterp'_dinterp.
  Qed.

  Lemma dinterp'_eq_itree n : forall (t1 t2 : itree Rnd T),
    eq_itree eq t1 t2 -> dinterp' (observe t1) n = dinterp' (observe t2) n.
  Proof.
  elim: n => [|n ih] t1 t2 eqt //=.
  punfold eqt; inv eqt; pclearbot => //=.
  - by rewrite (ih _ _ REL).
  - case: e k1 k2 REL {H0 H} => t0 mu k1 k2 REL /=.
    by apply/eq_in_dlet => // v _; apply/ih/REL.
  Qed.

  #[global] Instance Proper_dinterp : Proper (eq_itree eq ==> eq) dinterp.
  Proof.
  move=> t1 t2 eqt; rewrite /dinterp.
  suff -> : dinterp' (observe t1) = dinterp' (observe t2) by [].
  by apply/funext => n; apply: dinterp'_eq_itree.
  Qed.

  Lemma dinterp_ret (r : T) : dinterp (Ret r : itree Rnd T) = dunit r.
  Proof. by rewrite /dinterp -dlim_bumpE /= dlimC. Qed.

  Lemma dinterp_tau (t : itree Rnd T) : dinterp (Tau t) = dinterp t.
  Proof. by rewrite /dinterp -dlim_bumpE /=. Qed.

  Lemma dinterp_vis (t0 : IhbType.type) (mu : {distr t0 / R})
    (k : t0 -> itree Rnd T) :
    dinterp (Vis (GetRnd mu) k) = \dlet_(v <- mu) dinterp (k v).
  Proof.
  rewrite /dinterp -dlim_bumpE /=.
  by rewrite dlim_let // => v n m le; apply: homo_dinterp'.
  Qed.

End PropSem.

Section BindSem.

  Context {T U : choiceType}.

  Lemma le_dinterp'_bind n : forall (t : itree Rnd T) (k : T -> itree Rnd U),
    dinterp' (observe (ITree.bind t k)) n
      <=1 \dlet_(m <- dinterp' (observe t) n) dinterp' (observe (k m)) n.
  Proof.
  elim: n => [|n ih] t k x /=; first exact: lef_dnull.
  case: (observe t) => [r|t'|A e ke] /=.
  - by rewrite dlet_unit.
  - by apply/(le_trans (ih _ _ _))/le_in_dlet => // m _; apply: le_dinterp'_n.
  - case: e ke => t0 mu ke /=.
    rewrite dlet_dlet; apply/le_in_dlet => // v _ y.
    by apply/(le_trans (ih _ _ _))/le_in_dlet => // m _; apply: le_dinterp'_n.
  Qed.

  Lemma le_bind_dinterp' n : forall p (t : itree Rnd T) (k : T -> itree Rnd U),
    \dlet_(m <- dinterp' (observe t) n) dinterp' (observe (k m)) p
      <=1 dinterp' (observe (ITree.bind t k)) (n + p).
  Proof.
  elim: n => [|n ih] p t k x.
  - by rewrite /= dlet_null; apply: lef_dnull.
  - rewrite addSn /=; case: (observe t) => [r|t'|A e ke] /=.
    + have h : dinterp' (observe (k r)) p <=1 dinterp' (observe (k r)) (n + p).+1.
        by apply: homo_dinterp'; apply/leqW/leq_addl.
      by rewrite dlet_unit; apply: h.
    + exact: ih.
    + case: e ke => t0 mu ke /=.
      by rewrite dlet_dlet; apply/le_in_dlet => // v _; apply: ih.
  Qed.

  Lemma homo_bind_dinterp' (t : itree Rnd T) (k : T -> itree Rnd U) :
    homo (fun n => \dlet_(m <- dinterp' (observe t) n) dinterp' (observe (k m)) n).
  Proof.
  move=> n p le; apply: le_dlet; first exact: homo_dinterp'.
  by move=> m _; apply: homo_dinterp'.
  Qed.

  Lemma dinterp_bind (t : itree Rnd T) (k : T -> itree Rnd U) :
    dinterp (ITree.bind t k) = \dlet_(m <- dinterp t) dinterp (k m).
  Proof.
  rewrite /dinterp.
  have -> : dlim (dinterp' (observe (ITree.bind t k)))
          = dlim (fun n => \dlet_(m <- dinterp' (observe t) n)
                              dinterp' (observe (k m)) n).
    apply: dlim_sandwich.
    + exact: homo_dinterp'.
    + exact: homo_bind_dinterp'.
    + move=> n; exact: le_dinterp'_bind.
    + move=> n; exact: le_bind_dinterp'.
  apply/esym; apply: dlet_dlim_diag.
  - by move=> n p le; apply: homo_dinterp'.
  - by move=> m n p le; apply: homo_dinterp'.
  Qed.

End BindSem.

Section WhileSandwich.

  Variables (e : bexpr) (body W : cmem -> itree Rnd cmem).
  Hypothesis WE : forall m,
    W m ≅ (if esem e m then ITree.bind (body m) (fun m' => Tau (W m'))
           else Ret m).

  Lemma WT m : esem e m -> W m ≅ ITree.bind (body m) (fun m' => Tau (W m')).
  Proof. move=> He; rewrite WE He; reflexivity. Qed.

  Lemma WF m : esem e m = false -> W m ≅ Ret m.
  Proof. move=> He; rewrite WE He; reflexivity. Qed.

  Lemma dinterp_W_step m :
    dinterp (W m)
      = (if esem e m then \dlet_(m' <- dinterp (body m)) dinterp (W m')
         else dunit m).
  Proof.
  rewrite (WE m); case: (esem e m); last exact: dinterp_ret.
  by rewrite dinterp_bind; apply/eq_in_dlet => // m' _; rewrite dinterp_tau.
  Qed.

  Lemma le_dinterp'_W n : forall m,
    dinterp' (observe (W m)) n
      <=1 ubn (fun m => dinterp (body m)) (esem e) n m.
  Proof.
  elim: n => [|n ih] m x; first exact: lef_dnull.
  rewrite ubnS; case He: (esem e m).
  - rewrite (dinterp'_eq_itree _ (WT He)).
    apply/(le_trans (le_dinterp'_bind _ _ _ _)); apply: le_dlet.
    + by move=> y; rewrite /dinterp; apply: dlim_ub; apply: homo_dinterp'.
    + by move=> m' _; apply: ih.
  - by rewrite (dinterp'_eq_itree _ (WF He)).
  Qed.

  Lemma le_dinterp'_W_fuel n : forall m,
    dinterp' (observe (W m)) n
      <=1 ubn (fun m => dinterp' (observe (body m)) n) (esem e) n m.
  Proof.
  elim: n => [|n ih] m x; first exact: lef_dnull.
  rewrite ubnS; case He: (esem e m).
  - rewrite (dinterp'_eq_itree _ (WT He)).
    apply/(le_trans (le_dinterp'_bind _ _ _ _)).
    apply/le_in_dlet => // m' _ y.
    apply/(le_trans (ih m' y)).
    by apply: le_ubn_body => a a'; apply: homo_dinterp'.
  - by rewrite (dinterp'_eq_itree _ (WF He)).
  Qed.

  Lemma le_W_dinterp' n : forall m,
    ubn (fun m => dinterp (body m)) (esem e) n m <=1 dinterp (W m).
  Proof.
  elim: n => [|n ih] m x; first exact: lef_dnull.
  rewrite ubnS dinterp_W_step; case He: (esem e m); last by [].
  by apply/le_in_dlet => // m' _; apply: ih.
  Qed.

  Lemma dinterp_W m :
    dinterp (W m) = dlim (fun n => ubn (fun m => dinterp (body m)) (esem e) n m).
  Proof.
  apply/distr_eqP => x; apply/eqP; rewrite eq_le; apply/andP; split.
  - by apply: le_dlim => n; apply: le_dinterp'_W.
  - by apply: leub_dlim => n; apply: le_W_dinterp'.
  Qed.

End WhileSandwich.

Section WhileItree.

Lemma isem_while_roundE {E} (sem_i : cmd -> cmem -> itree E cmem) c e m :
  isem_while_round sem_i c e m
    = (if esem e m then ITree.bind (sem_i c m) (fun m' => Ret (inl m'))
       else Ret (inr m)).
Proof. by []. Qed.

Lemma isem_while_loopE {E} (sem_i : cmd -> cmem -> itree E cmem) c e m :
  isem_while_loop sem_i c e m
    ≅ (if esem e m then ITree.bind (sem_i c m)
                          (fun m' => Tau (isem_while_loop sem_i c e m'))
       else Ret m).
Proof.
rewrite /isem_while_loop {1}unfold_iter -/(isem_while_round sem_i c e m)
        isem_while_roundE.
case: (esem e m).
- rewrite bind_bind; apply: eqit_bind; first reflexivity.
  move=> m'; rewrite bind_ret_l; reflexivity.
- rewrite bind_ret_l; reflexivity.
Qed.

End WhileItree.


Section WhileSem.

  Variables (sem_i : cmd -> cmem -> itree Rnd cmem) (c : cmd) (e : bexpr).

  Lemma dinterp_while m :
    dinterp (isem_while_loop sem_i c e m)
      = dlim (fun n => ubn (fun m => dinterp (sem_i c m)) (esem e) n m).
  Proof. exact: (dinterp_W (isem_while_loopE sem_i c e)). Qed.

End WhileSem.

Section SsemLim.

  Lemma dlim_constE (T : choiceType) (mu : {distr T / R}) :
    mu = dlim (fun _ : nat => mu).
  Proof. by rewrite dlimC. Qed.

  Lemma dlim_ubn (f : nat -> cmem -> Distr cmem) (t : pred cmem) k :
    (forall n p, (n <= p)%N -> f n <=2 f p) ->
    forall a, ubn (fun a => dlim (fun n => f n a)) t k a
              = dlim (fun n => ubn (f n) t k a).
  Proof.
  move=> homo_f; elim: k => [|k ih] a.
  - by transitivity (dlim (fun _ : nat => dnull : Distr cmem));
      [rewrite dlimC | apply: eq_dlim].
  - have h1 : forall n p, (n <= p)%N -> f n a <=1 f p a.
      by move=> n p le; apply: homo_f.
    have h2 : forall x n p, (n <= p)%N -> ubn (f n) t k x <=1 ubn (f p) t k x.
      by move=> x n p le; apply: le_ubn_body; apply: homo_f.
    rewrite ubnS; case He: (t a); last first.
      transitivity (dlim (fun _ : nat => (dunit a : Distr cmem)));
        first by rewrite dlimC.
      by apply: eq_dlim => n; rewrite ubnS He.
    transitivity (\dlet_(x <- dlim (fun n => f n a))
                    dlim (fun n => ubn (f n) t k x)).
      by apply: eq_in_dlet; [move=> x _; apply: ih | ].
    rewrite (dlet_dlim_diag h1 h2).
    by apply: eq_dlim => n; rewrite ubnS He.
  Qed.

  Variable (l : nat -> (ident * cmem) -> Distr cmem).
  Hypothesis homo_l : forall n p, (n <= p)%N -> l n <=2 l p.

  Lemma homo_ssem_aux_l c m n p :
    (n <= p)%N -> ssem_aux (l n) c m <=1 ssem_aux (l p) c m.
  Proof. by move=> le; apply: mono_ssem_aux => a; apply: homo_l. Qed.

  Lemma dlim_ssem_aux c m :
    ssem_aux (fun a => dlim (fun n => l n a)) c m
      = dlim (fun n => ssem_aux (l n) c m).
  Proof.
  elim: c m => [||T x e|T x e|T x e|bs c ihc rs|e c1 ih1 c2 ih2|e c ih
               |c1 ih1 c2 ih2|f] m /=.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - transitivity (\dlet_(m' <- dlim (fun n => ssem_aux (l n) c (minit m bs)))
                    (dlim (fun _ : nat => dunit (mret m m' rs)))).
      by rewrite ihc; apply: eq_in_dlet; [move=> m' _; rewrite dlimC | ].
    apply: dlet_dlim_diag.
    + by move=> n p le; apply: homo_ssem_aux_l.
    + by move=> a n p le y.
  - by case: (esem e m); [apply: ih1 | apply: ih2].
  - have -> : ssem_aux (fun a => dlim (fun n => l n a)) c
            = (fun a => dlim (fun n => ssem_aux (l n) c a)).
      by apply/funext => a; apply: ih.
    rewrite (@eq_dlim _ _ (fun k => dlim (fun n => ubn (ssem_aux (l n) c)
                                                     (esem e) k m))).
    + by move=> k; apply: dlim_ubn => n p le a a'; apply: homo_ssem_aux_l.
    + apply: dlim_dlim_com.
      * by move=> k n1 n2 le; apply: homo_ubn_n.
      * by move=> k n1 n2 le; apply: le_ubn_body => a a'; apply: homo_ssem_aux_l.
  - transitivity (\dlet_(m' <- dlim (fun n => ssem_aux (l n) c1 m))
                    (dlim (fun n => ssem_aux (l n) c2 m'))).
      by rewrite ih1; apply: eq_in_dlet; [move=> m' _; apply: ih2 | ].
    apply: dlet_dlim_diag.
    + by move=> n p le; apply: homo_ssem_aux_l.
    + by move=> a n p le; apply: homo_ssem_aux_l.
  - by [].
  Qed.

End SsemLim.

Section CallSem.
  Variable ps : ident -> cmd.

  Local Notation ICM := (interp_mrec (handle_Call (E := Rnd) ps)).
  Local Notation CS := (com_sem (E := Rnd)).

  Lemma interp_callE T (t : itree (Call +' Rnd) T) :
    interp_call (E := Rnd) ps t = ICM t.
  Proof. by []. Qed.

  Lemma icm_ret T (x : T) : ICM (Ret x) ≅ (Ret x : itree Rnd T).
  Proof. rewrite unfold_interp_mrec /=; reflexivity. Qed.

  Lemma icm_tau T (t : itree (Call +' Rnd) T) : ICM (Tau t) ≅ Tau (ICM t).
  Proof. rewrite unfold_interp_mrec /=; reflexivity. Qed.

  Lemma icm_bind T U (t : itree (Call +' Rnd) T)
      (k : T -> itree (Call +' Rnd) U) :
    ICM (ITree.bind t k) ≅ ITree.bind (ICM t) (fun x => ICM (k x)).
  Proof. exact: interp_mrec_bind. Qed.

  Lemma icm_bind_ret T (t : itree (Call +' Rnd) T) :
    ITree.bind (ICM t) (fun x => ICM (Ret x)) ≅ ICM t.
  Proof.
  transitivity (ITree.bind (ICM t) (fun x : T => Ret x)).
    by apply: eqit_bind; [reflexivity | move=> x; apply: icm_ret].
  rewrite bind_ret_r; reflexivity.
  Qed.

  Lemma icm_call f m : ICM (CS (pwhile.call f) m) ≅ Tau (ICM (CS (ps f) m)).
  Proof.
  rewrite /= icm_bind {1}unfold_interp_mrec /= bind_tau bind_ret_r.
  by apply/eqit_Tau; apply: icm_bind_ret.
  Qed.

  Lemma icm_rnd T (x : vars T) (e : dexpr T) m :
    ICM (CS (x <$- e) m)
      ≅ Vis (GetRnd (esem e m)) (fun v => Tau (Ret m.[x <- v])).
  Proof.
  rewrite /= icm_bind {1}unfold_interp_mrec /= bind_vis.
  apply/eqit_Vis => v; rewrite bind_tau; apply/eqit_Tau.
  rewrite (icm_ret v) bind_ret_l; exact: icm_ret.
  Qed.

  Lemma icm_whileE c e m :
    ICM (isem_while_loop CS c e m)
      ≅ (if esem e m then ITree.bind (ICM (CS c m))
                           (fun m' => Tau (ICM (isem_while_loop CS c e m')))
         else Ret m).
  Proof.
  rewrite (isem_while_loopE CS c e m).
  case: (esem e m); last exact: icm_ret.
  rewrite icm_bind; apply: eqit_bind; first reflexivity.
  by move=> m'; apply: icm_tau.
  Qed.

  Lemma dinterp_icm_spin :
    dinterp (ICM (@ITree.spin (Call +' Rnd) cmem)) = dnull.
  Proof.
  rewrite /dinterp (@eq_dlim _ _ (fun _ => dnull)) ?dlimC //.
  by elim=> //= n ->.
  Qed.

  Local Notation D := (fun c m => dinterp (ICM (CS c m))).

  Lemma dinterp_icm_com_sem c m :
    D c m = ssem_aux (fun a => D (ps a.1) a.2) c m.
  Proof.
  elim: c m => [||T x e|T x e|T x e|bs c ihc rs|e c1 ih1 c2 ih2|e c ih
               |c1 ih1 c2 ih2|f] m /=.
  - exact: dinterp_icm_spin.
  - by rewrite (icm_ret m) dinterp_ret.
  - by rewrite (icm_ret _) dinterp_ret.
  - by rewrite (icm_ret _) dinterp_ret.
  - rewrite (icm_rnd x e m) dinterp_vis.
    by apply/eq_in_dlet => // v _; rewrite dinterp_tau dinterp_ret.
  - rewrite icm_bind dinterp_bind ihc.
    by apply/eq_in_dlet => // m' _; rewrite (icm_ret _); exact: dinterp_ret.
  - by case: (esem e m); [apply: ih1 | apply: ih2].
  - rewrite (dinterp_W (@icm_whileE c e)).
    have -> : (fun m => dinterp (ICM (CS c m)))
            = ssem_aux (fun a => D (ps a.1) a.2) c
      by apply/funext => a; apply: ih.
    by [].
  - by rewrite icm_bind dinterp_bind ih1;
       apply/eq_in_dlet => // m' _; apply: ih2.
  - by rewrite (icm_call f m) dinterp_tau.
  Qed.

  Lemma cs_ifE a c1 c2 m :
    CS (If a then c1 else c2) m = (if esem a m then CS c1 m else CS c2 m).
  Proof. by []. Qed.

  Lemma cs_whileE a c m : CS (While a Do c) m = isem_while_loop CS c a m.
  Proof. by []. Qed.

  Lemma ssem_aux_ifE (l : (ident * cmem) -> Distr cmem) a c1 c2 m :
    ssem_aux l (If a then c1 else c2) m
      = (if esem a m then ssem_aux l c1 m else ssem_aux l c2 m).
  Proof. by []. Qed.

  Lemma ssem_aux_whileE (l : (ident * cmem) -> Distr cmem) a c m :
    ssem_aux l (While a Do c) m
      = dlim (fun n => ubn (ssem_aux l c) (esem a) n m).
  Proof. by []. Qed.

  Lemma ssem_aux_seqE (l : (ident * cmem) -> Distr cmem) c1 c2 m :
    ssem_aux l (c1 ;; c2) m
      = \dlet_(m' <- ssem_aux l c1 m) ssem_aux l c2 m'.
  Proof. by []. Qed.

  Lemma ssem_aux_blockE (l : (ident * cmem) -> Distr cmem) bs c rs m :
    ssem_aux l (Block bs Do c Return rs) m
      = \dlet_(m' <- ssem_aux l c (minit m bs)) dunit (mret m m' rs).
  Proof. by []. Qed.

  Lemma ssem_aux_rndE (l : (ident * cmem) -> Distr cmem) T (y : vars T)
      (a : dexpr T) m :
    ssem_aux l (y <$- a) m = \dlet_(v <- esem a m) dunit m.[y <- v].
  Proof. by []. Qed.

  Lemma icm_skip m : ICM (CS skip m) ≅ Ret m.
  Proof. exact: icm_ret. Qed.

  Lemma icm_assign T (y : vars T) (a : expr T) m :
    ICM (CS (y <<- a) m) ≅ Ret m.[y <- esem a m].
  Proof. exact: icm_ret. Qed.

  Lemma icm_gassign T (y : vars T) (a : expr T) m :
    ICM (CS (G y <<- a) m) ≅ Ret m.{y <- esem a m}.
  Proof. exact: icm_ret. Qed.

  Lemma icm_block bs c rs m :
    ICM (CS (Block bs Do c Return rs) m)
      ≅ ITree.bind (ICM (CS c (minit m bs))) (fun m' => Ret (mret m m' rs)).
  Proof.
  rewrite /= icm_bind; apply: eqit_bind; first reflexivity.
  by move=> m'; apply: icm_ret.
  Qed.

  Lemma icm_seq c1 c2 m :
    ICM (CS (c1 ;; c2) m)
      ≅ ITree.bind (ICM (CS c1 m)) (fun m' => ICM (CS c2 m')).
  Proof. exact: icm_bind. Qed.

  Lemma dinterp'_icm_abort n m :
    dinterp' (observe (ICM (CS abort m))) n = dnull.
  Proof. by elim: n => //= n ->. Qed.

  Lemma le_dinterp'_com_sem n : forall c m,
    dinterp' (observe (ICM (CS c m))) n <=1 ssem_aux (ubnf ps n) c m.
  Proof.
  elim: n => [|n ihn]; first by move=> c m x; exact: lef_dnull.
  elim=> [||T y a|T y a|T y a|bs c ihc rs|a c1 ih1 c2 ih2|a c ih
         |c1 ih1 c2 ih2|f] m x.
  - by rewrite dinterp'_icm_abort; exact: lef_dnull.
  - by rewrite (dinterp'_eq_itree _ (icm_skip m)).
  - by rewrite (dinterp'_eq_itree _ (icm_assign y a m)).
  - by rewrite (dinterp'_eq_itree _ (icm_gassign y a m)).
  - rewrite (dinterp'_eq_itree _ (icm_rnd y a m)) ssem_aux_rndE.
    apply/(le_trans (le_dinterp'_vis _ _ _ _)).
    by apply/le_in_dlet => // v _ z; rewrite dinterp_tau dinterp_ret.
  - rewrite (dinterp'_eq_itree _ (icm_block bs c rs m)) ssem_aux_blockE.
    apply/(le_trans (le_dinterp'_bind _ _ _ _)).
    by apply: le_dlet; [exact: ihc | move=> m' _ z].
  - rewrite cs_ifE ssem_aux_ifE; case He: (esem a m).
    + exact: ih1.
    + exact: ih2.
  - rewrite cs_whileE ssem_aux_whileE.
    apply/(le_trans (le_dinterp'_W_fuel (icm_whileE c a) _ _ _)).
    apply/(le_trans (@le_ubn_body _ _ (ssem_aux (ubnf ps n.+1) c)
                       (esem a) n.+1 ih m x)).
    apply: (@dlim_ub _ _ (fun k => ubn (ssem_aux (ubnf ps n.+1) c) (esem a) k m)
                     n.+1).
    by move=> n1 n2 le; apply: homo_ubn_n.
  - rewrite (dinterp'_eq_itree _ (icm_seq c1 c2 m)) ssem_aux_seqE.
    apply/(le_trans (le_dinterp'_bind _ _ _ _)).
    by apply: le_dlet; [exact: ih1 | move=> m' _; apply: ih2].
  - by rewrite (dinterp'_eq_itree _ (icm_call f m)) /=; apply: ihn.
  Qed.

  Lemma ubnfS n a : ubnf ps n.+1 a = ssem_aux (ubnf ps n) (ps a.1) a.2.
  Proof. by []. Qed.

  Lemma ssem_E c m :
    ssem_ ps c m = ssem_aux (fun a => dlim (fun n => ubnf ps n a)) c m.
  Proof. by rewrite unlock. Qed.

  Lemma homo_ubnf_ps n p : (n <= p)%N -> ubnf ps n <=2 ubnf ps p.
  Proof. by move=> le x y; apply: homo_ubnf. Qed.

  Lemma le_ubnf_dinterp n a :
    ubnf ps n a <=1 dinterp (ICM (CS (ps a.1) a.2)).
  Proof.
  elim: n a => [|n ih] a x; first exact: lef_dnull.
  rewrite ubnfS dinterp_icm_com_sem.
  by apply: mono_ssem_aux => b y; apply: ih.
  Qed.

  Theorem dinterp_icm_ssem c m : dinterp (ICM (CS c m)) = ssem_ ps c m.
  Proof.
  have E : ssem_ ps c m = dlim (fun n => ssem_aux (ubnf ps n) c m).
    by rewrite ssem_E; apply: (dlim_ssem_aux homo_ubnf_ps c m).
  apply/distr_eqP => x; apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite E /dinterp; apply: le_dlim => n; exact: le_dinterp'_com_sem.
  - rewrite ssem_E dinterp_icm_com_sem.
    apply: mono_ssem_aux => b y.
    by apply: leub_dlim => n; apply: le_ubnf_dinterp.
  Qed.

End CallSem.

Section FullSem.

  Definition interp_full (c:cmd) (ps: ident -> cmd) : cmem -> {distr cmem / R} :=
    fun s => dinterp (interp_call ps (com_sem c s)).

  Lemma dinterp'_mrec_spin (ps : ident -> cmd) n :
    dinterp' (observe (interp_call (E:=Rnd) ps (@ITree.spin (Call +' Rnd) cmem))) n = dnull.
  Proof. by elim: n => //= n ->. Qed.

  Lemma interp_full_abort (ps : ident -> cmd) m :
    interp_full abort ps m = ssem_ ps abort m.
  Proof.
    rewrite ssem_abortE /interp_full /= /dinterp.
    by rewrite (@eq_dlim _ _ (fun _ => dnull)) ?dlimC //; exact: dinterp'_mrec_spin.
  Qed.

  Theorem interp_fullE (ps : ident -> cmd) c m : interp_full c ps m = ssem_ ps c m.
  Proof. exact: dinterp_icm_ssem. Qed.

End FullSem.
