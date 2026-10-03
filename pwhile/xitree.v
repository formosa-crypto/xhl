(* -------------------------------------------------------------------- *)
(* Interaction-tree semantics (memory-passing style) for the language     *)
(* with exceptions.  Copy of [itree.v] adapted to [xpwhile]/[xpsemantic]. *)
(*                                                                        *)
(* [com_sem : cmd -> M -> itree (Call +' E) outcome] -- the tree now       *)
(* returns an [outcome], not a memory, so an exception is observable at    *)
(* the tree level exactly as it is denotationally.  Sequencing, the loop   *)
(* body and block exit branch on it, mirroring [obind], [oubn] and         *)
(* [osem_aux]'s [block] case.                                             *)
(*                                                                        *)
(* The equivalence theorem is preserved in full, now against [osem_]:      *)
(*                                                                        *)
(*    interp_fullE : interp_full c ps m = osem_ ps c m                     *)
(*                                                                        *)
(* [interp] is shadowed by ITree's, so the [codeType] coercion is used     *)
(* wherever [itree.v] would have written it.                              *)
(* -------------------------------------------------------------------- *)
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import counting_distr.
(* ----------------- *) Require Import inhabited passn mem xpwhile xpsemantic.

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

(* ==================================================================== *)
Section ITreeSem.
Context {R : realType} {A B : codeType} {X Xg Y : eqType}
        {M : memType A B X Xg} {exn : eqType} {exnty : exn -> A}.

Local Notation Distr T := {distr T%type / R}.
Local Notation vars    := (vars_ X).
Local Notation gvars   := (vars_ Xg).
Local Notation expr    := (@expr_ A B X Xg M).
Local Notation cmd     := (@cmd_ R A B X Xg M exn exnty Y).
Local Notation bexpr   := (expr bool).
Local Notation dexpr T := (expr (Distr T)).
Local Notation psi     := (Y -> cmd).
Local Notation outcome := (outcome A B X Xg M exn exnty).

Variant Rnd : Type -> Type :=
  | GetRnd : forall t : A, {distr t / R} -> Rnd t.

Variant Call : Type -> Type :=
  | CallE (f:Y) (m: M): Call outcome.

Section ParSem.

  Context {E} {XI : Rnd -< E}.

  Local Notation continue_loop s := (ret (inl s)).
  Local Notation exit_loop s := (ret (inr s)).

  Definition isem_while_round {E}
    (sem_i: cmd -> M -> itree E outcome) (c : cmd) (e : bexpr) (m : M) :
    itree E (M + outcome) :=
    if esem e m then
      bind (sem_i c m)
        (fun o => if o is ONorm m' then continue_loop m' else exit_loop o)
    else exit_loop (ONorm m).

  Definition isem_while_loop {E}
    (sem_i: cmd -> M -> itree E outcome)
    (c : cmd) (e:bexpr) (m : M) :
    itree E outcome :=
    ITree.iter (isem_while_round sem_i c e) m.

  Fixpoint com_sem (c : cmd) : M -> itree (Call +' E) outcome :=
    match c with
    | abort => fun _ => ITree.spin
    | skip => fun m => Ret (ONorm m)
    | x <<- e => fun m => Ret (ONorm m.[x <- (esem e m)])
    | gassign _ x e => fun m => Ret (ONorm m.{x <- (esem e m)})
    | x <$- e => fun m =>
                   bind (trigger (GetRnd (esem e m)))
                     (fun t => Ret (ONorm m.[x <- t]))
    | block bs c rs => fun m =>
                   bind (com_sem c (minit m bs))
                     (fun o => match o with
                               | ONorm m'  => Ret (ONorm (mret m m' rs))
                               (* locals restored, [rs] skipped *)
                               | OExc m' v => Ret (OExc (mrestore m m') v)
                               end)
    | If e then c1 else c2 =>
    fun m =>
      match esem e m with
      | true => com_sem c1 m
      | false => com_sem c2 m
      end
    | While e Do c => isem_while_loop com_sem c e
    | seqc c1 c2 => fun m =>
        bind (com_sem c1 m)
          (fun o => if o is ONorm m' then com_sem c2 m' else Ret o)
    | xpwhile.call f => fun m => bind (trigger (CallE f m)) (fun o => Ret o)
    | raise k e => fun m => Ret (OExc m (existT _ k (esem e m)))
    | try_ c k x h => fun m =>
        bind (com_sem c m)
          (fun o => match o with
                    | ONorm _ => Ret o
                    | OExc m' t =>
                        let: existT k' v := t in
                        match k' =P k with
                        | ReflectT eq =>
                            com_sem h m'.[x <- ecast z (exnty z) eq v]
                        | ReflectF _ => Ret o
                        end
                    end)
  end.

  Definition handle_Call (ps: psi) :
    Call ~> itree (Call +' E) :=
    fun T (rc : Call T) =>
      match rc with
      | CallE f m => com_sem (ps f) m
      end.

  Definition interp_call (ps: psi)
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

  Lemma ubnS {S : choiceType} (f : S -> Distr S) (t : pred S) n a :
    ubn f t n.+1 a = if t a then \dlet_(x <- f a) ubn f t n x else dunit a.
  Proof. by []. Qed.

  Lemma oubnS (f : M -> Distr outcome) (t : pred M) n a :
    oubn f t n.+1 a =
      if t a then \dlet_(o <- f a) obind (oubn f t n) o else dunit (ONorm a).
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
          match e in Rnd Ty return (Ty -> itree Rnd T) -> {distr T / R} with
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
  case: t => [r|t|Ty e k] //=; case: e k => t0 mu k /=.
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

  Lemma le_dinterp'_vis (t0 : A) (mu : {distr t0 / R})
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

  Lemma dinterp_vis (t0 : A) (mu : {distr t0 / R})
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
  case: (observe t) => [r|t'|Ty e ke] /=.
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
  - rewrite addSn /=; case: (observe t) => [r|t'|Ty e ke] /=.
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

  Variables (e : bexpr) (body W : M -> itree Rnd outcome).
  Hypothesis WE : forall m,
    W m ≅ (if esem e m
           then ITree.bind (body m)
                  (fun o => if o is ONorm m' then Tau (W m') else Ret o)
           else Ret (ONorm m)).

  Lemma WT m : esem e m ->
    W m ≅ ITree.bind (body m)
            (fun o => if o is ONorm m' then Tau (W m') else Ret o).
  Proof. move=> He; rewrite WE He; reflexivity. Qed.

  Lemma WF m : esem e m = false -> W m ≅ Ret (ONorm m).
  Proof. move=> He; rewrite WE He; reflexivity. Qed.

  Lemma dinterp_W_step m :
    dinterp (W m)
      = (if esem e m
         then \dlet_(o <- dinterp (body m)) obind (fun m' => dinterp (W m')) o
         else dunit (ONorm m)).
  Proof.
  rewrite (WE m); case: (esem e m); last exact: dinterp_ret.
  rewrite dinterp_bind; apply/eq_in_dlet => // -[m'|m' v] _ /=.
  - exact: dinterp_tau.
  - exact: dinterp_ret.
  Qed.

  Lemma le_dinterp'_W n : forall m,
    dinterp' (observe (W m)) n
      <=1 oubn (fun m => dinterp (body m)) (esem e) n m.
  Proof.
  elim: n => [|n ih] m x; first exact: lef_dnull.
  rewrite oubnS; case He: (esem e m).
  - rewrite (dinterp'_eq_itree _ (WT He)).
    apply/(le_trans (le_dinterp'_bind _ _ _ _)); apply: le_dlet.
    + by move=> y; rewrite /dinterp; apply: dlim_ub; apply: homo_dinterp'.
    + move=> [m'|m' v] _ /=; first exact: ih.
      by move=> ?; rewrite lexx.
  - by rewrite (dinterp'_eq_itree _ (WF He)).
  Qed.

  Lemma le_dinterp'_W_fuel n : forall m,
    dinterp' (observe (W m)) n
      <=1 oubn (fun m => dinterp' (observe (body m)) n) (esem e) n m.
  Proof.
  elim: n => [|n ih] m x; first exact: lef_dnull.
  rewrite oubnS; case He: (esem e m).
  - rewrite (dinterp'_eq_itree _ (WT He)).
    apply/(le_trans (le_dinterp'_bind _ _ _ _)).
    apply/le_in_dlet => // -[m'|m' v] _ y /=; last by rewrite lexx.
    apply/(le_trans (ih m' y)).
    have hb : forall m0, dinterp' (observe (body m0)) n <=1
                         dinterp' (observe (body m0)) n.+1.
      by move=> m0; exact: le_dinterp'_n.
    exact: (le_oubn_body (esem e) n hb m' y).
  - by rewrite (dinterp'_eq_itree _ (WF He)).
  Qed.

  Lemma le_W_dinterp' n : forall m,
    oubn (fun m => dinterp (body m)) (esem e) n m <=1 dinterp (W m).
  Proof.
  elim: n => [|n ih] m x; first exact: lef_dnull.
  rewrite oubnS dinterp_W_step; case He: (esem e m); last by [].
  apply/le_in_dlet => // -[m'|m' v] _ /=; first exact: ih.
  by move=> ?; rewrite lexx.
  Qed.

  Lemma dinterp_W m :
    dinterp (W m) = dlim (fun n => oubn (fun m => dinterp (body m)) (esem e) n m).
  Proof.
  apply/distr_eqP => x; apply/eqP; rewrite eq_le; apply/andP; split.
  - by apply: le_dlim => n; apply: le_dinterp'_W.
  - by apply: leub_dlim => n; apply: le_W_dinterp'.
  Qed.

End WhileSandwich.

Section WhileItree.

Lemma isem_while_roundE {E} (sem_i : cmd -> M -> itree E outcome) c e m :
  isem_while_round sem_i c e m
    = (if esem e m
       then ITree.bind (sem_i c m)
              (fun o => if o is ONorm m' then Ret (inl m') else Ret (inr o))
       else Ret (inr (ONorm m))).
Proof. by []. Qed.

Lemma isem_while_loopE {E} (sem_i : cmd -> M -> itree E outcome) c e m :
  isem_while_loop sem_i c e m
    ≅ (if esem e m
       then ITree.bind (sem_i c m)
              (fun o => if o is ONorm m'
                        then Tau (isem_while_loop sem_i c e m') else Ret o)
       else Ret (ONorm m)).
Proof.
rewrite /isem_while_loop {1}unfold_iter -/(isem_while_round sem_i c e m)
        isem_while_roundE.
case: (esem e m).
- rewrite bind_bind; apply: eqit_bind; first reflexivity.
  by move=> [m'|m' v]; rewrite bind_ret_l; reflexivity.
- rewrite bind_ret_l; reflexivity.
Qed.

End WhileItree.

Section WhileSem.

  Variables (sem_i : cmd -> M -> itree Rnd outcome) (c : cmd) (e : bexpr).

  Lemma dinterp_while m :
    dinterp (isem_while_loop sem_i c e m)
      = dlim (fun n => oubn (fun m => dinterp (sem_i c m)) (esem e) n m).
  Proof. exact: (dinterp_W (isem_while_loopE sem_i c e)). Qed.

End WhileSem.

Section OsemLim.

  Lemma dlim_constE (T : choiceType) (mu : {distr T / R}) :
    mu = dlim (fun _ : nat => mu).
  Proof. by rewrite dlimC. Qed.

  Lemma dlim_oubn (f : nat -> M -> Distr outcome) (t : pred M) k :
    (forall n p, (n <= p)%N -> f n <=2 f p) ->
    forall a, oubn (fun a => dlim (fun n => f n a)) t k a
              = dlim (fun n => oubn (f n) t k a).
  Proof.
  move=> homo_f; elim: k => [|k ih] a.
  - by transitivity (dlim (fun _ : nat => dnull : Distr outcome));
      [rewrite dlimC | apply: eq_dlim].
  - have h1 : forall n p, (n <= p)%N -> f n a <=1 f p a.
      by move=> n p le; apply: homo_f.
    have h2 : forall o n p, (n <= p)%N ->
        obind (oubn (f n) t k) o <=1 obind (oubn (f p) t k) o.
      move=> o n p le; apply: le_obind => m'.
      by apply: le_oubn_body => a'; apply: homo_f.
    rewrite oubnS; case He: (t a); last first.
      transitivity (dlim (fun _ : nat => (dunit (ONorm a) : Distr outcome)));
        first by rewrite dlimC.
      by apply: eq_dlim => n; rewrite oubnS He.
    transitivity (\dlet_(o <- dlim (fun n => f n a))
                    dlim (fun n => obind (oubn (f n) t k) o)).
      apply: eq_in_dlet; last by [].
      move=> [m0|m0 v] _ /=; first exact: ih.
      by rewrite dlimC.
    rewrite (dlet_dlim_diag h1 h2).
    by apply: eq_dlim => n; rewrite oubnS He.
  Qed.

  Variable (l : nat -> (Y * M) -> Distr outcome).
  Hypothesis homo_l : forall n p, (n <= p)%N -> l n <=2 l p.

  Lemma homo_osem_aux_l c m n p :
    (n <= p)%N -> osem_aux (l n) c m <=1 osem_aux (l p) c m.
  Proof. by move=> le; apply: mono_osem_aux => a; apply: homo_l. Qed.

  Lemma dlim_osem_aux c m :
    osem_aux (fun a => dlim (fun n => l n a)) c m
      = dlim (fun n => osem_aux (l n) c m).
  Proof.
  elim: c m => [||T x e|T x e|T x e|bs c ih rs
               |e c1 ih1 c2 ih2|e c ih|c1 ih1 c2 ih2|f
               |k e|c ih k x ch ihh] m /=.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - exact: dlim_constE.
  - transitivity (\dlet_(o <- dlim (fun n => osem_aux (l n) c (minit m bs)))
                    (dlim (fun _ : nat =>
                       match o with
                       | ONorm m'  => dunit (ONorm (mret m m' rs))
                       | OExc m' v => dunit (OExc (mrestore m m') v)
                       end))).
      by rewrite ih; apply: eq_in_dlet => // o _; rewrite dlimC.
    apply: dlet_dlim_diag.
    + by move=> n p le; apply: homo_osem_aux_l.
    + by move=> a n p le.
  - by case: (esem e m); [apply: ih1 | apply: ih2].
  - have -> : osem_aux (fun a => dlim (fun n => l n a)) c
            = (fun a => dlim (fun n => osem_aux (l n) c a)).
      by apply/funext => a; apply: ih.
    rewrite (@eq_dlim _ _ _ (fun j => dlim (fun n => oubn (osem_aux (l n) c)
                                                     (esem e) j m))).
    + by move=> j; apply: dlim_oubn => n p le a a'; apply: homo_osem_aux_l.
    + apply: dlim_dlim_com.
      * by move=> j n1 n2 le; apply: homo_oubn_n.
      * move=> j n1 n2 le; apply: le_oubn_body => a.
        by apply: homo_osem_aux_l.
  - transitivity (\dlet_(o <- dlim (fun n => osem_aux (l n) c1 m))
                    (dlim (fun n => obind (osem_aux (l n) c2) o))).
      rewrite ih1; apply: eq_in_dlet; last by [].
      move=> [m0|m0 v] _ /=; first exact: ih2.
      by rewrite dlimC.
    apply: dlet_dlim_diag.
    + by move=> n p le; apply: homo_osem_aux_l.
    + move=> o n p le; apply: le_obind => m'.
      by apply: homo_osem_aux_l.
  - by [].
  - exact: dlim_constE.
  - transitivity (\dlet_(o <- dlim (fun n => osem_aux (l n) c m))
                    (dlim (fun n => ocatch k x (osem_aux (l n) ch) o))).
      rewrite ih; apply: eq_in_dlet; last by [].
      move=> [m0|m0 [k' v]] _ /=; first by rewrite dlimC.
      by case: (k' =P k) => [eq|_]; [exact: ihh | rewrite dlimC].
    apply: dlet_dlim_diag.
    + by move=> n p le; apply: homo_osem_aux_l.
    + move=> o n p le; apply: le_ocatch => m'.
      by apply: homo_osem_aux_l.
  Qed.

End OsemLim.

Section CallSem.
  Context { ps : psi}.

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

  Lemma icm_call f m : ICM (CS (xpwhile.call f) m) ≅ Tau (ICM (CS (ps f) m)).
  Proof.
  rewrite /= icm_bind {1}unfold_interp_mrec /= bind_tau bind_ret_r.
  by apply/eqit_Tau; apply: icm_bind_ret.
  Qed.

  Lemma icm_rnd T (x : vars T) (e : dexpr T) m :
    ICM (CS (x <$- e) m)
      ≅ Vis (GetRnd (esem e m)) (fun v => Tau (Ret (ONorm m.[x <- v]))).
  Proof.
  rewrite /= icm_bind {1}unfold_interp_mrec /= bind_vis.
  apply/eqit_Vis => v; rewrite bind_tau; apply/eqit_Tau.
  rewrite (icm_ret v) bind_ret_l; exact: icm_ret.
  Qed.

  Lemma icm_gassign T (y : gvars T) (a : expr T) m :
    ICM (CS (G y <<- a) m) ≅ Ret (ONorm m.{y <- esem a m}).
  Proof. exact: icm_ret. Qed.

  Lemma icm_block bs c rs m :
    ICM (CS (Block bs Do c Return rs) m)
      ≅ ITree.bind (ICM (CS c (minit m bs)))
          (fun o => match o with
                    | ONorm m'  => Ret (ONorm (mret m m' rs))
                    | OExc m' v => Ret (OExc (mrestore m m') v)
                    end).
  Proof.
  rewrite /= icm_bind; apply: eqit_bind; first reflexivity.
  by move=> [m'|m' v]; apply: icm_ret.
  Qed.

  Lemma icm_whileE c e m :
    ICM (isem_while_loop CS c e m)
      ≅ (if esem e m
         then ITree.bind (ICM (CS c m))
                (fun o => if o is ONorm m'
                          then Tau (ICM (isem_while_loop CS c e m')) else Ret o)
         else Ret (ONorm m)).
  Proof.
  rewrite (isem_while_loopE CS c e m).
  case: (esem e m); last exact: icm_ret.
  rewrite icm_bind; apply: eqit_bind; first reflexivity.
  by move=> [m'|m' v]; [apply: icm_tau | apply: icm_ret].
  Qed.

  Lemma dinterp_icm_spin :
    dinterp (ICM (@ITree.spin (Call +' Rnd) outcome)) = dnull.
  Proof.
  rewrite /dinterp (@eq_dlim _ _ _ (fun _ => dnull)) ?dlimC //.
  by elim=> //= n ->.
  Qed.

  Local Notation D := (fun c m => dinterp (ICM (CS c m))).

  (* [ICM] is pushed inside the branches, and the [Ret] branches are
   * collapsed with [icm_ret], so that a later [/=] reduces them without
   * leaving an [ICM (Ret _)] behind. *)
  Lemma icm_seq c1 c2 m :
    ICM (CS (c1 ;; c2) m)
      ≅ ITree.bind (ICM (CS c1 m))
          (fun o => if o is ONorm m' then ICM (CS c2 m') else Ret o).
  Proof.
  rewrite /= icm_bind; apply: eqit_bind; first reflexivity.
  by move=> [m'|m' v]; [reflexivity | apply: icm_ret].
  Qed.

  Lemma icm_try c k x h m :
    ICM (CS (try_ c k x h) m)
      ≅ ITree.bind (ICM (CS c m))
          (fun o => match o with
                    | ONorm _ => Ret o
                    | OExc m' t =>
                        let: existT k' v := t in
                        match k' =P k with
                        | ReflectT eq =>
                            ICM (CS h m'.[x <- ecast z (exnty z) eq v])
                        | ReflectF _ => Ret o
                        end
                    end).
  Proof.
  rewrite /= icm_bind; apply: eqit_bind; first reflexivity.
  move=> [m'|m' [k' v]]; first exact: icm_ret.
  by case: (k' =P k) => [eq|_]; [reflexivity | apply: icm_ret].
  Qed.

  (* [k] is inferable only from [x]'s type, so [Set Implicit Arguments]
   * hides it; we pass it explicitly at the use sites. *)
  Arguments icm_try : clear implicits.

  Lemma dinterp_icm_com_sem c m :
    D c m = osem_aux (fun a => D (ps a.1) a.2) c m.
  Proof.
  elim: c m => [||T x e|T x e|T x e|bs c ih rs
               |e c1 ih1 c2 ih2|e c ih|c1 ih1 c2 ih2|f
               |k e|c ih k x ch ihh] m /=.
  - exact: dinterp_icm_spin.
  - by rewrite (icm_ret _) dinterp_ret.
  - by rewrite (icm_ret _) dinterp_ret.
  - by rewrite (icm_ret _) dinterp_ret.
  - rewrite (icm_rnd x e m) dinterp_vis.
    by apply/eq_in_dlet => // v _; rewrite dinterp_tau dinterp_ret.
  - rewrite (icm_block bs c rs m) dinterp_bind ih.
    by apply/eq_in_dlet => // -[m'|m' v] _ /=; rewrite dinterp_ret.
  - by case: (esem e m); [apply: ih1 | apply: ih2].
  - rewrite (dinterp_W (@icm_whileE c e)).
    have -> : (fun m => dinterp (ICM (CS c m)))
            = osem_aux (fun a => D (ps a.1) a.2) c
      by apply/funext => a; apply: ih.
    by [].
  - rewrite (icm_seq c1 c2 m) dinterp_bind ih1.
    apply/eq_in_dlet => // -[m'|m' v] _ /=; first exact: ih2.
    exact: dinterp_ret.
  - by rewrite (icm_call f m) dinterp_tau.
  - by rewrite (icm_ret _) dinterp_ret.
  - rewrite (icm_try c k x ch m) dinterp_bind ih.
    apply/eq_in_dlet => // -[m'|m' [k' v]] _ /=; first exact: dinterp_ret.
    case: (k' =P k) => [eq|_]; first exact: ihh.
    exact: dinterp_ret.
  Qed.

  Lemma cs_ifE a c1 c2 m :
    CS (If a then c1 else c2) m = (if esem a m then CS c1 m else CS c2 m).
  Proof. by []. Qed.

  Lemma cs_whileE a c m : CS (While a Do c) m = isem_while_loop CS c a m.
  Proof. by []. Qed.

  Lemma osem_aux_ifE (l : (Y * M) -> Distr outcome) a c1 c2 m :
    osem_aux l (If a then c1 else c2) m
      = (if esem a m then osem_aux l c1 m else osem_aux l c2 m).
  Proof. by []. Qed.

  Lemma osem_aux_whileE (l : (Y * M) -> Distr outcome) a c m :
    osem_aux l (While a Do c) m
      = dlim (fun n => oubn (osem_aux l c) (esem a) n m).
  Proof. by []. Qed.

  Lemma osem_aux_seqE (l : (Y * M) -> Distr outcome) c1 c2 m :
    osem_aux l (c1 ;; c2) m
      = \dlet_(o <- osem_aux l c1 m) obind (osem_aux l c2) o.
  Proof. by []. Qed.

  Lemma osem_aux_tryE (l : (Y * M) -> Distr outcome) c k x h m :
    osem_aux l (try_ c k x h) m
      = \dlet_(o <- osem_aux l c m) ocatch k x (osem_aux l h) o.
  Proof. by []. Qed.

  Lemma osem_aux_rndE (l : (Y * M) -> Distr outcome) T (y : vars T)
      (a : dexpr T) m :
    osem_aux l (y <$- a) m = \dlet_(v <- esem a m) dunit (ONorm m.[y <- v]).
  Proof. by []. Qed.

  Lemma osem_aux_gassnE (l : (Y * M) -> Distr outcome) T (y : gvars T)
      (a : expr T) m :
    osem_aux l (G y <<- a) m = dunit (ONorm m.{y <- esem a m}).
  Proof. by []. Qed.

  Lemma osem_aux_blockE (l : (Y * M) -> Distr outcome) bs c rs m :
    osem_aux l (Block bs Do c Return rs) m
      = \dlet_(o <- osem_aux l c (minit m bs))
          match o with
          | ONorm m'  => dunit (ONorm (mret m m' rs))
          | OExc m' v => dunit (OExc (mrestore m m') v)
          end.
  Proof. by []. Qed.

  Lemma osem_aux_raiseE (l : (Y * M) -> Distr outcome) k
      (a : expr (exnty k)) m :
    osem_aux l (raise k a) m = dunit (OExc m (existT _ k (esem a m))).
  Proof. by []. Qed.

  Lemma icm_skip m : ICM (CS skip m) ≅ Ret (ONorm m).
  Proof. exact: icm_ret. Qed.

  Lemma icm_assign T (y : vars T) (a : expr T) m :
    ICM (CS (y <<- a) m) ≅ Ret (ONorm m.[y <- esem a m]).
  Proof. exact: icm_ret. Qed.

  Lemma icm_raise k (a : expr (exnty k)) m :
    ICM (CS (raise k a) m) ≅ Ret (OExc m (existT _ k (esem a m))).
  Proof. exact: icm_ret. Qed.

  Arguments icm_raise : clear implicits.

  Lemma dinterp'_icm_abort n m :
    dinterp' (observe (ICM (CS abort m))) n = dnull.
  Proof. by elim: n => //= n ->. Qed.

  Lemma le_dinterp'_com_sem n : forall c m,
    dinterp' (observe (ICM (CS c m))) n <=1 osem_aux (oubnf ps n) c m.
  Proof.
  elim: n => [|n ihn]; first by move=> c m x; exact: lef_dnull.
  elim=> [||T y a|T y a|T y a|bs c ih rs
         |a c1 ih1 c2 ih2|a c ih|c1 ih1 c2 ih2|f
         |k a|c ih k y ch ihh] m x.
  - by rewrite dinterp'_icm_abort; exact: lef_dnull.
  - by rewrite (dinterp'_eq_itree _ (icm_skip m)).
  - by rewrite (dinterp'_eq_itree _ (icm_assign y a m)).
  - by rewrite (dinterp'_eq_itree _ (icm_gassign y a m)).
  - rewrite (dinterp'_eq_itree _ (icm_rnd y a m)) osem_aux_rndE.
    apply/(le_trans (le_dinterp'_vis _ _ _ _)).
    by apply/le_in_dlet => // v _ z; rewrite dinterp_tau dinterp_ret.
  - rewrite (dinterp'_eq_itree _ (icm_block bs c rs m)) osem_aux_blockE.
    apply/(le_trans (le_dinterp'_bind _ _ _ _)).
    apply: le_dlet; first exact: ih.
    by move=> [m'|m' v] _ /=; rewrite ?lexx.
  - rewrite cs_ifE osem_aux_ifE; case He: (esem a m).
    + exact: ih1.
    + exact: ih2.
  - rewrite cs_whileE osem_aux_whileE.
    apply/(le_trans (le_dinterp'_W_fuel (icm_whileE c a) _ _ _)).
    apply/(le_trans (le_oubn_body (esem a) n.+1 ih m x)).
    apply: (@dlim_ub _ _ (fun j => oubn (osem_aux (oubnf ps n.+1) c) (esem a) j m)
                     n.+1).
    by move=> n1 n2 le; apply: homo_oubn_n.
  - rewrite (dinterp'_eq_itree _ (icm_seq c1 c2 m)) osem_aux_seqE.
    apply/(le_trans (le_dinterp'_bind _ _ _ _)).
    apply: le_dlet; first exact: ih1.
    move=> [m'|m' v] _ /=; first exact: ih2.
    by move=> ?; rewrite lexx.
  - by rewrite (dinterp'_eq_itree _ (icm_call f m)) /=; apply: ihn.
  - by rewrite (dinterp'_eq_itree _ (icm_raise k a m)).
  - rewrite (dinterp'_eq_itree _ (icm_try c k y ch m)) osem_aux_tryE.
    apply/(le_trans (le_dinterp'_bind _ _ _ _)).
    apply: le_dlet; first exact: ih.
    move=> [m'|m' [k' v]] _ /=; first by move=> ?; rewrite lexx.
    case: (k' =P k) => [eq|_]; first exact: ihh.
    by move=> ?; rewrite lexx.
  Qed.

  Lemma oubnfS n a : oubnf ps n.+1 a = osem_aux (oubnf ps n) (ps a.1) a.2.
  Proof. by []. Qed.

  Lemma osem_E c m :
    osem_ ps c m = osem_aux (fun a => dlim (fun n => oubnf ps n a)) c m.
  Proof. by rewrite unlock. Qed.

  Lemma homo_oubnf_ps n p : (n <= p)%N -> oubnf ps n <=2 oubnf ps p.
  Proof. by move=> le x y; apply: homo_oubnf. Qed.

  Lemma le_oubnf_dinterp n a :
    oubnf ps n a <=1 dinterp (ICM (CS (ps a.1) a.2)).
  Proof.
  elim: n a => [|n ih] a x; first exact: lef_dnull.
  rewrite oubnfS dinterp_icm_com_sem.
  by apply: mono_osem_aux => b y; apply: ih.
  Qed.

  Theorem dinterp_icm_osem c m : dinterp (ICM (CS c m)) = osem_ ps c m.
  Proof.
  have E : osem_ ps c m = dlim (fun n => osem_aux (oubnf ps n) c m).
    by rewrite osem_E; apply: (dlim_osem_aux homo_oubnf_ps c m).
  apply/distr_eqP => x; apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite E /dinterp; apply: le_dlim => n; exact: le_dinterp'_com_sem.
  - rewrite osem_E dinterp_icm_com_sem.
    apply: mono_osem_aux => b y.
    by apply: leub_dlim => n; apply: le_oubnf_dinterp.
  Qed.

End CallSem.

Section FullSem.

  Definition interp_full (c:cmd) (ps: psi) : M -> {distr outcome / R} :=
    fun s => dinterp (interp_call ps (com_sem c s)).

  Lemma dinterp'_mrec_spin (ps : psi) n :
    dinterp' (observe (interp_call (E:=Rnd) ps
                         (@ITree.spin (Call +' Rnd) outcome))) n = dnull.
  Proof. by elim: n => //= n ->. Qed.

  Lemma interp_full_abort (ps : psi) m :
    interp_full abort ps m = osem_ ps abort m.
  Proof.
    rewrite osem_abortE /interp_full /= /dinterp.
    by rewrite (@eq_dlim _ _ _ (fun _ => dnull)) ?dlimC //;
       exact: dinterp'_mrec_spin.
  Qed.

  Theorem interp_fullE (ps : psi) c m : interp_full c ps m = osem_ ps c m.
  Proof. exact: dinterp_icm_osem. Qed.

  (* and hence, after projection, the original statement *)
  Corollary interp_full_ssem (ps : psi) c m :
    sproj (interp_full c ps m) = ssem_ ps c m.
  Proof. by rewrite interp_fullE ssem_osemE. Qed.

End FullSem.

End ITreeSem.
