(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import counting_distr esum.
(* ----------------- *) Require Import inhabited passn pwhile.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope syn_scope.
Local Open Scope mem_scope.

Notation ROHS := (X in X <= _)%pattern.
Notation LOHS := (X in _ <= X)%pattern.

Declare Scope sem_scope.

(* -------------------------------------------------------------------- *)

Lemma funext2 : forall {T U V : Type} (f g : T -> U -> V),
  (forall x y, f x y = g x y) -> f = g.
Proof. by move=> T U V f g eq; apply/funext=> x; apply/funext. Qed.

(* -------------------------------------------------------------------- *)
Section DistrRecast.
Variables (T U V : choiceType) (f g : T -> Distr U) (mu nu : Distr T).

Lemma dlet_null : \dlet_(i <- dnull) f i = dnull.
Proof. apply /distr_eqP /dlet_null. Qed.

Lemma dlet_unit x : \dlet_(i <- dunit x) f i = f x.
Proof. by apply/distr_eqP/dlet_unit. Qed.

Lemma dlet_if b :
    \dlet_(t <- if b then mu else nu) f t
  =  if b then \dlet_(t <- mu) f t else \dlet_(t <- nu) f t.
Proof. by case:ifP. Qed.

Lemma dlet_dlet (f1 : T -> Distr U) (f2 : U -> Distr V) :
    \dlet_(x <- \dlet_(y <- mu) f1 y) f2 x
  = \dlet_(y <- mu) \dlet_(x <- f1 y) f2 x.
Proof. by apply/distr_eqP/dlet_dlet. Qed.

Lemma eq_in_dlet :
  {in dinsupp mu, f =1 g} -> mu = nu ->
  \dlet_(i <- mu) f i = \dlet_(i <- nu) g i.
Proof.
by move=> eqf <-; apply/distr_eqP/eq_in_dlet=>// x /eqf ->.
Qed.

Lemma eq_dlim (fn gn : nat -> Distr T):
  fn =1 gn -> \dlim_(n) fn n = \dlim_(n) gn n.
Proof. by move=> eq_fg; apply/distr_eqP/eq_dlim=> ??; rewrite eq_fg. Qed.

Lemma dlet_dmargin (f1 : T -> U) (g1 : U -> Distr V):
       \dlet_(u <- dmargin f1 mu) g1 u = \dlet_(t <- mu) g1 (f1 t).
Proof. apply /distr_eqP/dlet_dmargin. Qed.

Lemma dmargin_dlet (f1 : U -> V) (g1 : T -> Distr U):
       dmargin f1 (\dlet_(t <- mu) g1 t) = \dlet_(t <- mu) dmargin f1 (g1 t).
Proof. apply /distr_eqP/dmargin_dlet. Qed.

Lemma dmargin_dunit (t : T) (f1 : T -> U):
   @dmargin R _ _ f1 (dunit t) = dunit (f1 t).
Proof. apply /distr_eqP/dmargin_dunit. Qed.

Lemma dlet_dunit_id : \dlet_(t <- mu) (dunit t) = mu :> Distr T.
Proof. by apply/distr_eqP/dlet_dunit_id. Qed.

Lemma dlim_let (h : nat -> T -> Distr U) (d : Distr T) :
  (forall x n m, (n <= m)%N -> h n x <=1 h m x) ->
    \dlim_(n) \dlet_(x <- d) (h n x) =
      \dlet_(x <- d) \dlim_(n) (h n x).
Proof. by move=> ?; apply/distr_eqP/dlim_let. Qed.

Lemma dlimC: \dlim_(_) mu = mu.
Proof. by apply/distr_eqP/dlimC. Qed.
End DistrRecast.

(* -------------------------------------------------------------------- *)
Section DLimRecast.
Variables (T U : choiceType).
Variables (f : nat -> {distr T / R}) (h : T -> {distr U / R}).

Lemma dlet_lim : (forall n m, (n <= m)%N -> f n <=1 f m) ->
  \dlet_(x <- \dlim_(n) f n) h x = \dlim_(n) \dlet_(x <- f n) h x.
Proof. by move=> ?; apply/distr_eqP/dlet_lim /dhomo_dnd. Qed.
End DLimRecast.

(* -------------------------------------------------------------------- *)
Section DProj.
Context {T : choiceType} (mu : Distr (T * T)).

Lemma dprojE s x :
  dmargin (fst, snd)#s mu x =
    fine (esum [set: T] (fun y => EFin (mu ((x, y)#s, (y, x)#s)))).
Proof. by case: s => /=; rewrite ?(dfstE, dsndE). Qed.

Lemma summable_proj s x1 :
  esummable [set: T] (fun x2 => EFin (mu ((x1, x2)#s, (x2, x1)#s))).
Proof. by case: s => /=; [apply/summable_fst | apply/summable_snd]. Qed.
End DProj.

(* -------------------------------------------------------------------- *)
Fixpoint ubn {A : choiceType} (f : A -> Distr A) (t : pred A) n := fun a =>
  if n is n.+1 return Distr A then
    if t a then \dlet_(x <- f a) ubn f t n x else dunit a
  else dnull.

(* -------------------------------------------------------------------- *)
Reserved Notation "m .[ x <- v ]"
  (at level 1, x, v at level 200, format "m .[ x  <-  v ]").

Reserved Notation "m .{ x }"
  (at level 1, x at level 200, format "m .{ x }").

Reserved Notation "m .{ x <- v }"
  (at level 1, x, v at level 200, format "m .{ x  <-  v }").

Reserved Notation "m .[+ x <- v ]"
  (at level 1, x, v at level 200, format "m .[+  x  <-  v ]").

(* -------------------------------------------------------------------- *)
Notation "m .[ x ]"      := (@mget _ _ (vtype x%V) m (vname x%V)) : mem_scope.
Notation "m .[ x <- v ]" := (@mset _ _ (vtype x%V) m (vname x%V) v) : mem_scope.

(* the main (global) store, reached only through [gvar_]/[gassign] *)
Notation "m .{ x }"      := (@mgetg _ _ (vtype x%V) m (vname x%V)) : mem_scope.
Notation "m .{ x <- v }" := (@msetg _ _ (vtype x%V) m (vname x%V) v) : mem_scope.

(* entering a block: a fresh local store in which only [x] is set *)
Notation "m .[+ x <- v ]" := (@mpush _ _ (vtype x%V) m (vname x%V) v) : mem_scope.

Notation "m .[+]" := (mnew m) (at level 2, format "m .[+]") : mem_scope.

(* -------------------------------------------------------------------- *)
Section Semantics.
  Context {X Y : eqType} {cmem: memType X} {ps : Y -> (@cmd_  X cmem Y)}.

Notation vars    := (@vars_ X).
Notation expr    := (@expr_ X cmem).
Notation cmd     := (@cmd_  X cmem Y).
Notation bexpr   := (expr bool).
Notation dexpr T := (expr (Distr T)).

Notation mdistr := (Distr cmem).
Notation mnull  := (@dnull R cmem).

(* -------------------------------------------------------------------- *)
Fixpoint esem {T : Type} (e : expr T) (m : cmem) : T :=
  match e in expr_ _ _ T return T with
  | var_ T x => m.[x]
  | cst_ T c => c
  | prp_ P   => P m
  | app_ T U e1 e2 => (esem e1 m) (esem e2 m)
  | gvar_ T x => m.{x}
  end.

(* -------------------------------------------------------------------- *)
(* Entering a block: a fresh local store, then one assignment per declared
 * local.  Every initialiser is read in the *outer* memory [m]. *)
Definition minit (m : cmem) (bs : seq binding) : cmem :=
  foldl (fun m' b => let: existT _ (x, e) := b in m'.[x <- esem e m]) m.[+] bs.

(* Leaving a block: the enclosing local store is put back while [m']'s main
 * store is kept, then one assignment per returned value.  Every return
 * expression is read in the *inner* memory [m'], and every assignment lands
 * outside the scope -- so a return target may be one of the locals. *)
Definition mret (m m' : cmem) (rs : seq binding) : cmem :=
  foldl (fun mm b => let: existT _ (r, e') := b in mm.[r <- esem e' m'])
        (mrestore m m') rs.

(* -------------------------------------------------------------------- *)
Fixpoint ssem_aux (l: (Y * cmem) -> mdistr) (s : cmd) (m : cmem) : mdistr :=
  match s with
  | abort => mnull
  | skip  => dunit m

  | x <<- e =>
      dunit (m.[x <- esem e m])

  | x <$- e =>
      \dlet_(v <- esem e m) (dunit m.[x <- v])

  | If e then c1 else c2 =>
      match esem e m with
      | true  => ssem_aux l c1 m
      | false => ssem_aux l c2 m
      end

  | While e Do c =>
      dlim (fun n => ubn (ssem_aux l c) (esem e) n m)

  | seqc c1 c2 =>
      \dlet_(m' <- ssem_aux l c1 m) (ssem_aux l c2 m')

  | call n => l (n, m)

  | gassign _ x e =>
      dunit m.{x <- esem e m}

  | block bs c rs =>
      \dlet_(m' <- ssem_aux l c (minit m bs)) dunit (mret m m' rs)
  end.

Fixpoint ubnf (ps: Y -> cmd) n :=
  fun (a: Y * cmem) =>
    if n is n.+1 return Distr cmem then
      ssem_aux (ubnf ps n) (ps (fst a)) (snd a)
    else dnull.

Definition ssem_r s m := ssem_aux (fun l => dlim (fun n => ubnf ps n l)) s m.

(* -------------------------------------------------------------------- *)
Fact ssem_key : unit. Proof. by []. Qed.
Definition ssem_ := locked_with ssem_key ssem_r.
Canonical ssem_unlockable := [unlockable fun ssem_].

(* -------------------------------------------------------------------- *)
Implicit Types (m : cmem) (c : cmd).

Notation ssem := ssem_.
Notation prp  := prp_.

Lemma sem_eqP c1 c2 :
  (forall m, ssem c1 m = ssem c2 m) <-> ssem c1 = ssem c2.
Proof. by split=> [|->//] eq; apply/funext=> m. Qed.

Fixpoint whilen e c n :=
  if n is n.+1 then
    (If e then (c;; whilen e c n) else skip)
  else abort.

Lemma ssem_abortE m : ssem abort m = mnull.
Proof. by rewrite unlock. Qed.

Lemma ssem_skipE m : ssem skip m = dunit m.
Proof. by rewrite unlock. Qed.

Lemma ssem_assnE {T} (x : vars T) (e : expr T) m :
  ssem (x <<- e) m = dunit (m.[x <- esem e m]).
Proof. by rewrite unlock. Qed.

Lemma ssem_rndE {T} (x : vars T) (e : dexpr T) m :
  ssem (x <$- e) m = \dlet_(v <- esem e m) (dunit m.[x <- v]).
Proof. by rewrite unlock. Qed.

Lemma ssem_ifE e c1 c2 m :
  ssem (If e then c1 else c2) m =
    if esem e m then ssem c1 m else ssem c2 m.
Proof. by rewrite unlock. Qed.

Lemma ssem_seqE c1 c2 m :
  ssem (c1 ;; c2) m = \dlet_(m' <- ssem c1 m) (ssem c2 m').
Proof. by rewrite unlock. Qed.

Lemma esem_varE {T : IhbType.type} (x : vars T) m :
   esem (@var_ _ _ T x) m = m.[x].
Proof. by []. Qed.

Lemma esem_cstE {T : Type} (c : T) m : esem (cst_ c) m = c.
Proof. by []. Qed.

Lemma esem_prpE (P : pred cmem) m : esem (prp_ P) m = P m.
Proof. by []. Qed.

Lemma esem_appE {T U : Type} (e1 : expr (T -> U)) (e2 : expr T) m :
  esem (app_ e1 e2) m = (esem e1 m) (esem e2 m).
Proof. by []. Qed.

Lemma esem_gvarE {T : IhbType.type} (x : vars T) m :
   esem (@gvar_ _ _ T x) m = m.{x}.
Proof. by []. Qed.

Lemma ssem_gassnE {T} (x : vars T) (e : expr T) m :
  ssem (G x <<- e) m = dunit m.{x <- esem e m}.
Proof. by rewrite unlock. Qed.

Lemma ssem_blockE bs c rs m :
  ssem (Block bs Do c Return rs) m =
    \dlet_(m' <- ssem c (minit m bs)) dunit (mret m m' rs).
Proof. by rewrite unlock. Qed.

Lemma ssem_whileE e c m :
  ssem (While e Do c) m = dlim (fun n => ssem (whilen e c n) m).
Proof.
rewrite {1}unlock /=; apply/eq_dlim=> n /=.
elim: n m => /= [|n ih] m; first by rewrite ssem_abortE.
rewrite ssem_ifE; case: (esem e m); last by rewrite ssem_skipE.
rewrite ssem_seqE /=;apply/eq_in_dlet => //.
by rewrite unlock.
Qed.

Lemma ssem_while_ubn e c m :
  ssem (While e Do c) m = dlim (fun n => ubn (ssem c) (esem e) n m).
Proof. by rewrite unlock. Qed.

Lemma ssem_callE f m :
  ssem (call f) m = dlim (fun n => ubnf ps n (f,m)).
Proof.
  by rewrite unlock.
Qed.

Definition semE :=
  (ssem_abortE, ssem_skipE, @ssem_assnE, @ssem_rndE,
   ssem_ifE   , ssem_seqE , ssem_whileE, ssem_callE,
   @ssem_gassnE, ssem_blockE).

Definition bsemE := locked (
  funext ssem_abortE,
  funext ssem_skipE,
  fun T (x : vars T) (e : expr _) => funext (ssem_assnE x e),
  fun T (x : vars T) (e : expr _) => funext (ssem_rndE x e),
  fun e c1 c2 => funext (ssem_ifE e c1 c2),
  fun c1 c2 => funext (ssem_seqE c1 c2),
  fun e c => funext (ssem_whileE e c),
  fun f => funext (ssem_callE f),
  fun T (x : vars T) (e : expr _) => funext (ssem_gassnE x e),
  fun bs c rs => funext (ssem_blockE bs c rs)).

Lemma sem_seqA c1 c2 c3 :
  ssem ((c1 ;; c2) ;; c3) = ssem (c1 ;; (c2 ;; c3)).
Proof. by apply/sem_eqP=> m; rewrite !bsemE dlet_dlet. Qed.

Lemma sem_ifseq e ct cf c :
    ssem ((If e then ct else cf) ;; c)
  = ssem (If e then (ct ;; c) else (cf ;; c)).
Proof. by apply/sem_eqP=> m; rewrite !bsemE; case: ifP. Qed.

Lemma sem_seql c1 c1' c2 :
  ssem c1 =1 ssem c1' -> ssem (c1 ;; c2) = ssem (c1' ;; c2).
Proof. by move/sem_eqP=> eq; rewrite !bsemE eq. Qed.

Lemma sem_seqr c1 c2 c2' :
  ssem c2 =1 ssem c2' -> ssem (c1 ;; c2) = ssem (c1 ;; c2').
Proof. by move/sem_eqP=> eq; rewrite !bsemE eq. Qed.

Lemma sem_ift e ct ct' cf : ssem ct =1 ssem ct' ->
  ssem (If e then ct else cf) = ssem (If e then ct' else cf).
Proof. by move=> /sem_eqP eq; rewrite !bsemE eq. Qed.

Lemma sem_iff e ct cf cf' : ssem cf =1 ssem cf' ->
  ssem (If e then ct else cf) = ssem (If e then ct else cf').
Proof. by move=> /sem_eqP eq; rewrite !bsemE eq. Qed.

Lemma sem_whileb e c c' :
  ssem c =1 ssem c' -> ssem (While e Do c) = ssem (While e Do c').
Proof.
 move=> /sem_eqP eq;apply/sem_eqP=> m;rewrite !semE.
 apply/eq_dlim=> /= n; elim: n m => //= n /sem_eqP ih m.
 by rewrite !bsemE ih eq .
Qed.

(* -------------------------------------------------------------------- *)
Lemma dlim_seql (C : nat -> cmd) (c : cmd) m :
     (forall m n p, (n <= p)%N -> ssem (C n) m <=1 ssem (C p) m)
  -> \dlim_(n) (ssem (C n ;; c) m)
   = \dlet_(m' <- \dlim_(n) ssem (C n) m) ssem c m'.
Proof.
move=> leC; rewrite dlet_lim.
+ by apply/leC.
by apply/eq_dlim=> n; rewrite semE.
Qed.

Lemma dlim_seqr (C : nat -> cmd) (c : cmd) m :
     (forall m n p, (n <= p)%N -> ssem (C n) m <=1 ssem (C p) m)
  -> \dlim_(n) (ssem (c ;; C n) m)
   = \dlet_(m' <- ssem c m) \dlim_(n) (ssem (C n) m').
Proof.
move=> leC; rewrite -dlim_let //.
by apply/eq_dlim => n; rewrite semE.
Qed.

Lemma dlim_ift (e : expr bool) (C : nat -> cmd) (c : cmd) m :
    \dlim_(n) (ssem (If e then C n else c) m)
  = if esem e m then \dlim_(n) ssem (C n) m else ssem c m.
Proof.
pose F n := if esem e m then ssem (C n) m else ssem c m.
rewrite -(@eq_dlim _ F) {}/F => [k |].
+ by rewrite !semE.
by case: ifPn => _; rewrite ?dlimC.
Qed.

Lemma dlim_iff (e : expr bool) (C : nat -> cmd) (c : cmd) m :
    \dlim_(n) (ssem (If e then c else C n) m)
  = if esem e m then ssem c m else \dlim_(n) ssem (C n) m.
Proof.
pose F n := if esem e m then ssem c m else ssem (C n) m.
rewrite -(@eq_dlim _ F) {}/F => [k|].
+ by rewrite !semE.
by case: ifPn => _; rewrite ?dlimC.
Qed.

(* -------------------------------------------------------------------- *)
Definition iterc n (c : cmd) := (iterop n seqc c skip).

Arguments iterc : simpl never.

Lemma iterc0 c : iterc 0 c = skip.
Proof. by []. Qed.

Lemma itercS n c : iterc n.+1 c = iter n (seqc c) c.
Proof. by rewrite /iterc iteropS. Qed.

(* -------------------------------------------------------------------- *)
Lemma homo_ssem (mu1 mu2 : Distr cmem) c :
  mu1 <=1 mu2 -> \dlet_(m <- mu1) ssem c m <=1 \dlet_(m <- mu2) ssem c m.
Proof. by move=> le_mu m; apply/le_dlet. Qed.

Lemma sem_seq_le c1 c2 c1' c2' :
     ssem c1 <=2 ssem c1'
  -> ssem c2 <=2 ssem c2'
  -> ssem (c1 ;; c2) <=2 ssem (c1' ;; c2').
Proof. by move=> le1 le2 m1 m2; rewrite !semE; apply/le_dlet. Qed.

Lemma le_whilen (n : nat) (e : expr bool) (c : cmd) m m' :
  ssem (whilen e c n) m m' <= ssem (whilen e c n.+1) m m'.
Proof.
elim: n m m' => /= [|n ih] m m'.
  by rewrite ssem_abortE dnullE ge0_mu.
rewrite !ssem_ifE; case: (esem e m) => //.
rewrite !ssem_seqE; apply/le_in_dlet.
by move=> {m'} m _ m'; apply/ih.
Qed.

Lemma homo_whilen e c m n p : (n <= p)%N ->
  ssem (whilen e c n) m <=1 ssem (whilen e c p) m.
Proof.
elim: p n => [|p ih] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le_np m'.
by apply/(le_trans (ih _ le_np m'))/le_whilen.
Qed.

(* Lemma dcvg_whilen e c m : dcvg (fun n => ssem (whilen e c n) m). *)
(* Proof. *)
(* move=> m'; set u := fun n : nat => _; case: (@ncvg_mono_bnd _ u). *)
(* + by move=> n p le_np; apply/homo_whilen. *)
(* + apply/asboolP/nboundedP; exists 2%:R => // n. *)
(*   apply/(@le_lt_trans _ _ 1%:R); rewrite ?ltr1n //. *)
(*   by rewrite ger0_norm (ge0_mu, le1_mu1). *)
(* by move=> l ul; exists l%:E. *)
(* Qed. *)

Lemma unroll_while_w (e e' : expr bool) c m :
     (forall m, esem e' m -> esem e m)
  -> ssem (While e Do c) m =
     ssem (IfT e' then c ;; While e Do c) m.
Proof.
move=> impe; apply/distr_eqP=> m'; rewrite !semE.
case: ifPn => h; last by rewrite dlet_unit -semE.
rewrite -dlim_bump /= -ssem_seqE dlim_ift.
rewrite dlim_seqr.
+ by apply/homo_whilen.
rewrite impe // semE; apply/distr_eqP: m'.
by apply/eq_in_dlet=> // m' _; rewrite semE.
Qed.

Lemma unroll_while (e : expr bool) c m :
  ssem (While e Do c) m =
  ssem (IfT e then c ;; While e Do c) m.
Proof. by apply/unroll_while_w. Qed.

Lemma unroll_while_in (e : expr bool) c m :
  ssem (While e Do c) m =
  ssem (IfT e then (c ;; While e Do c)) m.
Proof.
rewrite unroll_while !semE; case: ifP => // h.
rewrite dlet_unit semE; apply/distr_eqP=> m'.
by rewrite -dlim_bump /= dlim_ift h semE.
Qed.

Lemma ssem_while0 (e : expr bool) c m : ~~ esem e m ->
  ssem (While e Do c) m = dunit m.
Proof. by rewrite unroll_while_in !semE => /negbTE ->. Qed.

Lemma ssem_whileS (e : expr bool) c m : esem e m ->
  ssem (While e Do c) m = ssem (c ;; While e Do c) m.
Proof. by rewrite unroll_while_in !semE => ->. Qed.

Lemma unrolls_while_w (e e' : expr bool) c m :
     (forall m, esem e' m -> esem e m)
  -> ssem (While e Do c) m =
     ssem (While e' Do c;; While e Do c) m.
Proof.
move=> impe; apply/distr_eqP=> m'; apply/eqP.
rewrite eq_le andbC; apply/andP; split.
+ rewrite ssem_seqE (ssem_whileE e') dlet_lim.
  + apply/homo_whilen.
  apply/leub_dlim => n {}m'; rewrite -ssem_seqE.
  elim: n m m' => [|n ihn] m m' /=.
    by rewrite !semE dlet_null; apply/lef_dnull.
  rewrite sem_ifseq ssem_ifE; case: ifPn => [/impe em|].
    by rewrite ssem_whileS // sem_seqA; apply/sem_seq_le.
  by rewrite 2!semE dlet_unit.
+ rewrite ssem_whileE; apply/leub_dlim; move: {m'} m => [:a] m n m'.
  case/asboolP: (esem e' m) => [|/negP]; last first.
  abstract: a n m m' => h; rewrite ssem_seqE (@ssem_while0 e') //.
  rewrite dlet_unit semE; apply/dlim_ub=> {m'} k p le_kp m'.
  by apply/homo_whilen.
elim: n m m' => [|n ihn] m m' h.
  by rewrite ssem_abortE; apply/lef_dnull.
rewrite ssem_ifE impe // !ssem_seqE ssem_whileS //.
rewrite ssem_seqE dlet_dlet; apply/le_in_dlet=> {h m'} m _ m'.
rewrite -ssem_seqE; case/asboolP: (esem e' m) => [|/negP h].
  by move/ihn. by apply/a.
Qed.

Lemma split_while (e1 e2 : expr bool) c:
     ssem (While e1 Do c)
   = ssem (While (e1 && e2) Do c ;; While e1 Do c).
Proof. by apply/funext=> m; apply/unrolls_while_w => {}m /= /andP[]. Qed.

Lemma prpP (P : pred cmem) m : reflect (P m) (esem (prp_ P) m).
Proof. by apply/idP. Qed.
End Semantics.

(* -------------------------------------------------------------------- *)
Section EqCmd.
Context {I J : eqType} {M : memType I} {ps : J -> (@cmd_  I M J)}.
Local Notation cmd := (cmd_ I M J).

Definition eqcmd (c1 c2 : cmd) :=
  forall m, @ssem_ _ _ _ ps c1 m = @ssem_ _ _ _ ps c2 m.

Global Instance eqcmd_R : Equivalence eqcmd.
Proof.
constructor=> //.
+ by move=> f1 f2 eq s; rewrite eq.
+ by move=> f1 f2 f3 eq1 eq2 s; rewrite eq1.
Qed.

Notation "c1 '=C' c2" := (eqcmd c1 c2) (at level 70, no associativity).

Notation CLHS := (X in X =C _)%pattern.
Notation CRHS := (X in _ =C X)%pattern.

Lemma seq_skip_l (c : cmd) : (skip ;; c) =C c.
Proof. by move=> m;rewrite !semE dlet_unit. Qed.

Lemma seq_skip_r (c : cmd) : (c ;; skip) =C c.
Proof.
move=> m; rewrite semE -[X in _ = X]dlet_dunit_id;
by apply eq_in_dlet => // ??; rewrite semE.
Qed.

Lemma seqA (c1 c2 c3 : cmd) : (c1 ;; (c2 ;; c3)) =C (c1 ;; c2 ;; c3).
Proof.
move=> m;rewrite !semE dlet_dlet.
by apply eq_in_dlet=> // m' _;rewrite semE.
Qed.

Lemma iter_seq_out n c c1 c2 :
  iter n (seqc c) (c1 ;; c2) =C (iter n (seqc c) c1 ;; c2).
Proof.
by elim: n => //= n ih m; rewrite -seqA !ssem_seqE; apply/eq_in_dlet.
Qed.

Lemma iter_seq_swap n c : iter n (seqc^~ c) c =C iter n (seqc c) c.
Proof.
elim: n => // n ih m; rewrite [in RHS]iterSr.
by rewrite iter_seq_out !ssem_seqE; apply/eq_in_dlet.
Qed.

Lemma itercSl n c: iterc n.+1 c =C (c ;; iterc n c).
Proof. by move=> m; case: n => [|n] //=; rewrite seq_skip_r. Qed.

Lemma itercSr n c: iterc n.+1 c =C (iterc n c ;; c).
Proof.
move=> m; case: n => [|n]; first by rewrite iterc0 seq_skip_l.
rewrite !itercS /= -iterS -iter_seq_swap /=.
by rewrite !ssem_seqE; apply/eq_in_dlet=> //; apply/iter_seq_swap.
Qed.

Global Instance seq_m : Proper (eqcmd ==> eqcmd ==> eqcmd) seqc.
Proof. by move=> ?? H1 ?? H2 m;rewrite !semE; apply eq_in_dlet. Qed.

Global Instance while_m : Proper (eq ==> eqcmd ==> eqcmd) while.
Proof.
move=> ?? H1 ?? H2 m; rewrite !ssem_while_ubn H1; apply/eq_dlim=> n.
by elim: n m => //= n ih m; case: ifP => // _; apply eq_in_dlet.
Qed.

Global Instance cond_m : Proper (eq ==> eqcmd ==> eqcmd ==> eqcmd) cond.
Proof. by move=> ?? H1 ?? H2 ?? H3 m; rewrite !semE H1; case: ifP. Qed.

Global Instance block_m : Proper (eq ==> eqcmd ==> eq ==> eqcmd) (@block I M J).
Proof.
move=> ?? <- c1 c2 hc ?? <- m.
by rewrite !ssem_blockE hc.
Qed.

Fixpoint mk_seqr (c1 c2 : cmd) :=
  match c2 with
  | skip        => c1
  | seqc c2 c2' => mk_seqr (mk_seqr c1 c2) c2'
  | _           => seqc c1 c2
  end.

Definition mk_seq (c1 c2 : cmd) :=
  if c1 is skip then c2 else  mk_seqr c1 c2.
 
Fixpoint normc (c : cmd) :=
  match c with
  | abort | skip | assign _ _ _ | random _ _ _ | call _
  | gassign _ _ _ => c
  | cond e c1 c2 => cond e (normc c1) (normc c2)
  | while e c    => while e (normc c)
  | seqc c1 c2   => mk_seq (normc c1) (normc c2)
  | block bs c rs => block bs (normc c) rs
  end.

Lemma mk_seqrP (c1 c2 : cmd) : mk_seqr c1 c2 =C seqc c1 c2.
Proof.
elim:c2 c1=> //= [|c2 H1 c3 H2] c1;first by rewrite seq_skip_r.
by rewrite seqA H2 H1.
Qed.

Lemma mk_seqP (c1 c2 : cmd) : mk_seq c1 c2 =C seqc c1 c2.
Proof. by case:c1 => //= *;rewrite ?mk_seqrP // seq_skip_l. Qed.

Lemma normcP (c : cmd) : c =C normc c.
Proof.
by elim: c=> //= [?? H1 ? H2|?? H1|? H1 ? H2|?? H1 ?];
rewrite ?mk_seqP [in CLHS]H1 ?[in CLHS]H2.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ssem_iterop_iter n c :
  iterc n c =C iter n (seqc c) skip.
Proof.
case: n => // n; rewrite itercS /=; elim: n => [|n ih] /=.
  by rewrite seq_skip_r. by rewrite ih.
Qed.

Lemma ssem_iterop_iterrev n c :
  iterc n c =C iter n (seqc^~ c) skip.
Proof.
rewrite ssem_iterop_iter; elim: n=> // n ih.
rewrite iterSr iterS -{}ih; elim: n => /= [|n ih].
- by rewrite seq_skip_l seq_skip_r.
- by rewrite ih seqA.
Qed.

Lemma whilen_iterc n b c :
  whilen b c n.+1 =C (iterc n (IfT b then c) ;; (IfT b then abort)).
Proof.
rewrite ssem_iterop_iter; elim: n => [|n ihn] /=.
  rewrite seq_skip_l => m; rewrite !semE; case: ifP=> // _.
  by rewrite bsemE; apply/distr_eqP=> m'; rewrite dletC dnullE mulr0.
rewrite -seqA -ihn /= => m; rewrite !semE; case: ifP => // bm.
by rewrite dlet_unit !semE bm.
Qed.
End EqCmd.

Arguments eqcmd {_} {_} {_} _.

Arguments ssem_ {_} {_} {_} _.

Notation "c1 '=C' c2 ';' ps" := (eqcmd ps c1 c2) (at level 70, no associativity).

(* -------------------------------------------------------------------- *)
Lemma unrolln_while {J: eqType} n (e : expr bool) c (ps: (J -> cmd_ _ _ J)) :
  (While e Do c) =C (iterc n (IfT e then c) ;; While e Do c) ; ps.
Proof.
rewrite ssem_iterop_iter; elim: n => [|n ih] /=.
  by rewrite seq_skip_l.
by rewrite -seqA -ih => m; rewrite unroll_while.
Qed.

(* -------------------------------------------------------------------- *)
Lemma if_same {J: eqType} (e : expr bool) c (ps: (J -> cmd_ _ _ J)) :
  If e then c else c =C c ; ps.
Proof. by move=> m; rewrite !semE; case: (esem _ _). Qed.

(* -------------------------------------------------------------------- *)
Lemma if_seq {J: eqType} (e : expr bool) c c1 c2 (ps: (J -> cmd_ _ _ J)) :
  (If e then c1 else c2 ;; c) =C If e then (c1 ;; c) else (c2 ;; c) ; ps.
Proof. by move=> m; rewrite !semE; case: ifPn. Qed.

(* -------------------------------------------------------------------- *)
Lemma le_while {J: eqType} (e : expr bool) c1 c2 m (ps: (J -> cmd_ _ _ J)):
     (forall m, esem e m -> ssem_ ps c1 m <=1 ssem_ ps c2 m)
  -> ssem_ ps (While e Do c1) m <=1 ssem_ ps (While e Do c2) m.
Proof.
move=> lec m'; rewrite !semE; apply/le_dlim => n.
elim: n m => //= n ihn m {}m'; rewrite !semE.
by case: ifP => // hem; apply/le_dlet => {} m' //; apply: lec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xsplit_while {J: eqType} (e e1 e2 : expr bool) c (ps: (J -> cmd_ _ _ J)):
     (forall m, esem e2 m -> esem e m)
  -> (forall m, esem e m -> ~~ esem e1 m -> esem e2 m)
  -> (While e Do c) =C (While e Do (If e1 then c else While e2 Do c)); ps.
Proof.
move=> h1 h2 m; apply/distr_eqP => m'.
rewrite (rwP eqP) eq_le -(rwP andP); split; last first.
  rewrite semE; apply: leub_dlim => {m'} n m'.
  elim: n m m' => /= [|n ihn] m m'; first by rewrite !semE lef_dnull.
  rewrite semE; case: ifP => hem; last first.
    by rewrite unroll_while_in ssem_ifE hem.
  rewrite if_seq ssem_ifE; case: ifPn => he1m.
    by rewrite unroll_while_in ssem_ifE hem !ssem_seqE le_dlet.
  by rewrite (unrolls_while_w _ _ h1) !ssem_seqE le_dlet.
rewrite ssem_whileE; apply: leub_dlim => {m'} n m'.
elim: n m m' => /= [|n ihn] m m'; first by rewrite !semE lef_dnull.
rewrite semE; case: ifP => hem; last first.
  by rewrite unroll_while_in ssem_ifE hem.
rewrite unroll_while_in ssem_ifE hem 2![in X in _ <= X]semE.
case: ifPn => he1m; first by rewrite !ssem_seqE le_dlet.
rewrite unroll_while -!ssem_seqE -seqA 2![in X in _ <= X]semE.
rewrite (h2 _ hem he1m) ssem_seqE le_dlet => // {m' hem he1m} m _ m'.
rewrite 2!semE dlet_lim.
+ by apply: homo_whilen.
apply: (le_trans _ (dlim_ub n _ _)); last first.
  move=> k1 k2 le_k1k2 {}m'; apply: le_dlet => //.
  by move=> {}m'; apply: homo_whilen.
elim: n m m' ihn => /= [|k ihk] m m' ihn; first by rewrite semE lef_dnull.
rewrite !ssem_ifE; case: ifP => hem; last first.
  case: ifPn => [/h1|he2m]; first by rewrite hem.
  by rewrite -ssem_seqE seq_skip_l unroll_while_in ssem_ifE hem.
case: ifPn => he2m; rewrite -!ssem_seqE.
  rewrite -seqA 2!ssem_seqE le_dlet => // {m' hem he2m} m _ m'.
  rewrite ssem_seqE; apply: ihk => {m'} m m'.
  by apply: (le_trans (le_whilen _ _ _ _ _)) => /=.
rewrite seq_skip_l unroll_while_in ssem_ifE hem.
rewrite 2![in X in _ <= X]semE; case: ifPn => [he1m|]; last first.
  by move/(h2 _ hem); rewrite (negbTE he2m).
rewrite ssem_seqE le_dlet => // {m' hem he1m he2m} m _ m'.
by apply: (le_trans (le_whilen _ _ _ _ _)).
Qed.

(* (* -------------------------------------------------------------------- *) *)
Notation ssem   := (@ssem_ _ ident cmem).
Notation mdistr := (Distr cmem).
Notation mnull  := (@dnull R cmem).

Arguments ssem_ X Y cmem ps s%_S m%_M.
Arguments esem X cmem T e%_X m%_M.

Notation "e `_ m" := (@esem _ _ _ e%X m%M) : sem_scope.

(* -------------------------------------------------------------------- *)
Definition dssem ps c mu := (\dlet_(m <- mu) ssem ps c m).

Instance dsem_m ps : Proper (@eqcmd _ _ _ ps ==> eq ==> eq) (dssem ps).
Proof. by move=> c1 c2 eqc /= mu _ <-; apply/eq_in_dlet. Qed.

(* -------------------------------------------------------------------- *)
Lemma dssem_abortE ps mu : dssem ps abort mu = mnull.
Proof.
by apply/distr_eqP=> m; rewrite /dssem bsemE dletC dnullE mulr0.
Qed.

Lemma dssem_skipE ps mu : dssem ps skip mu = mu.
Proof.
by apply/distr_eqP=> m; rewrite /dssem bsemE dlet_dunit_id.
Qed.

Lemma dssem_seqE ps c1 c2 mu :
  dssem ps (c1 ;; c2) mu = dssem ps c2 (dssem ps c1 mu).
Proof.
by apply/distr_eqP=> m; rewrite /dssem bsemE dlet_dlet.
Qed.

(* -------------------------------------------------------------------- *)
Definition lossless (P : assn) c :=
  forall ps m, m \in P -> dweight (ssem ps c m) = 1.

Definition dlossless (P : dassn) c :=
  forall ps mu, mu \in P -> dweight (dssem ps c mu) = 1.

(* -------------------------------------------------------------------- *)
Reserved Notation "m .[ x @ s <- v ]"
  (at level 1, x, s, v at level 200, format "m .[ x @ s  <-  v ]").

Reserved Notation "m .[~1 x <- v ]"
  (at level 1, x, v at level 200, format "m .[~1  x  <-  v ]").

Reserved Notation "m .[~2 x <- v ]"
  (at level 1, x, v at level 200, format "m .[~2  x  <-  v ]").

Notation rsem    := (@ssem_ _ rmem).
Notation rmdistr := (Distr rmem).
Notation rmnull  := (@dnull R rmem).

Notation "m .[ x @ s <- v ]" := m.[x # s <- v].
Notation "m .[~1 x <- v ]"   := m.[x @ '1 <- v].
Notation "m .[~2 x <- v ]"   := m.[x @ '2 <- v].

Lemma mselect_mset T s s' (m : rmem) (x : vars T) (v : T) :
  m.[x @ s <- v] # s' = if s == s' then (m#s).[x <- v] else m#s'.
Proof. by case: s s' x => [] [] []. Qed.

Lemma esem_iE T s (e : expr T) (m : rmem) : esem (e#s) m = esem e m#s.
Proof. by elim: e => {T} /= [ ?[?]| | | ??? -> ? ->| ?[?]]. Qed.

Lemma esem_1E T (e : expr T) (m : rmem): esem (e#'1) m = esem e m.1.
Proof. by rewrite esem_iE. Qed.

Lemma esem_2E T (e : expr T) (m : rmem): esem (e#'2) m = esem e m.2.
Proof.  by rewrite esem_iE. Qed.

Definition esemE := (@esem_appE, @esem_cstE, esem_1E, esem_2E).

Definition ssemE := (esemE, @semE).

Lemma mget_iE {T : IhbType.type} (m : rmem) (x : vars T) s :
  m.[irvar s x] = (m#s).[x].
Proof. by case:s x=> -[]. Qed.

Lemma mset_iE {T : IhbType.type} (m : rmem) (x : vars T) (v : T) s :
  m.[x#s <- v] =
  (((m#'1).[x <- v], m.1)#s, (m.2, (m#'2).[x <- v])#s)%M.
Proof. by case:x m s => xid [m1 m2] []. Qed.

Lemma mgetg_iE {T : IhbType.type} (m : rmem) (x : vars T) s :
  m.{irvar s x} = (m#s).{x}.
Proof. by case:s x=> -[]. Qed.

Lemma msetg_iE {T : IhbType.type} (m : rmem) (x : vars T) (v : T) s :
  m.{x#s <- v} =
  (((m#'1).{x <- v}, m.1)#s, (m.2, (m#'2).{x <- v})#s)%M.
Proof. by case:x m s => xid [m1 m2] []. Qed.

Lemma mnew_iE (m : rmem) : m.[+] = ((m#'1).[+], (m#'2).[+]).
Proof. by case: m. Qed.

Lemma mrestore_iE (m0 m : rmem) :
  mrestore m0 m = (mrestore m0.1 m.1, mrestore m0.2 m.2).
Proof. by case: m0 m => a1 a2 [b1 b2]. Qed.

Definition rps s (ps : nat -> cmd) := fun n => ircmd s (ps n).

(* Lemma ssem_iE ps s c (m : rmem): rsem (rps s ps) (ircmd s c) m = *)
(*   \dlet_(m' <- ssem ps c m#s) dunit ((m', m.1)#s, (m.2, m')#s)%M. *)
(* Proof. *)
(* elim: c m => [||T v e|T v e|e c1 Hc1 c2 Hc2|e c Hc|c1 Hc1 c2 Hc2| n ] [m1 m2]. *)
(* + by rewrite !ssemE dlet_null. *)
(* + by rewrite !ssemE dlet_unit; case:s. *)
(* + by rewrite !ssemE esem_iE dlet_unit mset_iE;case:s. *)
(* + rewrite !ssemE esem_iE dlet_dlet; apply eq_in_dlet => // t _. *)
(*   by rewrite dlet_unit mset_iE;case: s. *)
(* + by rewrite !ssemE esem_iE;case:ifP. *)
(* + rewrite !ssemE dlet_lim; last by apply/homo_whilen. *)
(*   apply eq_dlim=> n; elim: n (m1,m2)=> [ | n Hn] m /=. *)
(*   + by rewrite !ssemE dlet_null. *)
(*   rewrite !ssemE esem_iE;case:ifP => _. *)
(*   + rewrite Hc !dlet_dlet;apply eq_in_dlet=>// m' _. *)
(*     by rewrite dlet_unit Hn;case s. *)
(*   by rewrite dlet_unit;case: m s {Hc Hn}=> ?? []. *)
(* + rewrite !ssemE Hc1 !dlet_dlet;apply eq_in_dlet=>// m _. *)
(*   by rewrite !dlet_unit Hc2;apply eq_in_dlet =>[? _|];case s. *)
(* rewrite !ssemE dlet_lim. *)
(* Qed. *)

(* Lemma ssem_1E (m : rmem) c : *)
(*   rsem (c#'1) m = \dlet_(m1 <- ssem c m.1) (dunit (m1, m.2)). *)
(* Proof. by apply ssem_iE. Qed. *)

(* Lemma ssem_2E (m : rmem) c : *)
(*   rsem (c#'2) m = \dlet_(m2 <- ssem c m.2) (dunit (m.1, m2)). *)
(* Proof. by apply ssem_iE. Qed. *)

(* -------------------------------------------------------------------- *)
Notation "`[{ e }]" := (@esem _ _ _ e%X) (at level 2, format "`[{ e }]").

(* -------------------------------------------------------------------- *)
Ltac diff_v := try (right; (assumption || rewrite eq_sym; assumption)).

Notation SET := ((_.[_ <- _].[_])%pattern) (only parsing).

Ltac mem_t := rewrite ?mget_iE ![SET](mget_eq, mget_neq); diff_v.

(* -------------------------------------------------------------------- *)
Lemma le_ubn_body {A : choiceType} (f g : A -> Distr A) (t : pred A) n :
  f <=2 g -> ubn f t n <=2 ubn g t n.
Proof.
move=> le_fg; elim: n => [|n ih] a m' //=.
by case: ifP => // _; apply/le_dlet => // x _; exact: ih.
Qed.

Lemma le_ubn_n {A : choiceType} (f : A -> Distr A) (t : pred A) n :
  ubn f t n <=2 ubn f t n.+1.
Proof.
elim: n => [|n ih] a m' /=; first exact: lef_dnull.
by case: ifP => // _; apply/le_in_dlet => // x _; exact: ih.
Qed.

Lemma homo_ubn_n {A : choiceType} (f : A -> Distr A) (t : pred A) n p :
  (n <= p)%N -> ubn f t n <=2 ubn f t p.
Proof.
elim: p n => [|p ihp] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le.
by move=> a m'; apply/(le_trans (ihp _ le a m'))/le_ubn_n.
Qed.

(* -------------------------------------------------------------------- *)
Lemma mono_ssem_aux
  {X Y : eqType} {cmem: memType X}
  (l l' : (Y * cmem) -> {distr cmem / R}) c  (m : cmem) :
  (forall x, l x <=1 l' x) -> ssem_aux l c m <=1 ssem_aux l' c m.
Proof.
move=> le_ll'; elim: c m =>
  [||T x e|T x e|e c1 ih1 c2 ih2|e c ih|c1 ih1 c2 ih2|f|???|? c ih ?] m m' //=.
- by case: ifP => _; [exact: ih1 | exact: ih2].
- have hb : ssem_aux l c <=2 ssem_aux l' c by move=> a a'; exact: ih.
  apply/leub_dlim => n m0.
  apply: (le_trans (@le_ubn_body _ _ _ (esem e) n hb m m0)).
  by apply/dlim_ub => n1 n2 hle; exact: homo_ubn_n.
- by apply/le_dlet => [|x _]; [exact: ih1 | exact: ih2].
by apply/le_dlet => [|m0 _]; [exact: ih | by []].
Qed.

Lemma mono_ubnf {X Y : eqType} {cmem: memType X} {ps : Y -> (@cmd_  X cmem Y)} n :
  ubnf ps n <=2 ubnf ps n.+1.
Proof.
elim: n => [|n ih] [f m'] m /=; first exact: lef_dnull.
by apply/mono_ssem_aux => x; exact: ih.
Qed.

Lemma homo_ubnf {X Y : eqType} {cmem: memType X} {ps : Y -> (@cmd_  X cmem Y)} n p :
  (n <= p)%N -> ubnf ps n <=2 ubnf ps p.
Proof.
elim: p n => [|p ihp] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le a m'.
by apply/(le_trans (ihp _ le a m'))/mono_ubnf.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dlim_dlim_com {T: choiceType} (f : nat -> nat -> {distr T / R})
(hmono1: (forall k n1 n2, (n1 <= n2)%N -> f n1 k <=1 f n2 k))
(hmono2: (forall k n1 n2, (n1 <= n2)%N -> f k n1 <=1 f k n2)):
  \dlim_(n) (\dlim_(m) f n m) =  \dlim_(m) (\dlim_(n) f n m).
Proof.
 have main (g : nat -> nat -> {distr T / R}) :
      (forall k n1 n2, (n1 <= n2)%N -> g n1 k <=1 g n2 k) ->
      \dlim_(n) (\dlim_(m) g n m) <=1 \dlim_(m) (\dlim_(n) g n m).
    move=> hg; apply: leub_dlim => n; apply: le_dlim => m.
    by apply: dlim_ub => n1 n2 le_n; exact: hg.
  apply/distr_eqP => x; apply/eqP; rewrite eq_le; apply/andP; split.
  + exact: main f hmono1 x.
  + exact: main (fun a b => f b a) hmono2 x.
Qed.

Lemma dlet_dlim_diag {T U : choiceType}
  (d : nat -> Distr T) (h : nat -> T -> Distr U) :
  (forall n m, (n <= m)%N -> d n <=1 d m) ->
  (forall x n m, (n <= m)%N -> h n x <=1 h m x) ->
  \dlet_(x <- \dlim_(n) d n) \dlim_(n) h n x =1
    \dlim_(n) \dlet_(x <- d n) h n x.
Proof.
move=> mono_d mono_h u; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite dlet_lim //; apply/leub_dlim => n.
  rewrite -dlim_let.
  + by move=> x k1 k2 hle; apply: mono_h.
  apply/leub_dlim => k u'.
  have hle_d : d n <=1 d (maxn k n) by apply/mono_d/leq_maxr.
  have hle_h : {in dinsupp (d n), forall x, h k x <=1 h (maxn k n) x}.
    by move=> x _; apply/mono_h/leq_maxl.
  have h1 := le_dlet hle_d hle_h u'.
  have h2 : (\dlet_(x <- d (maxn k n)) h (maxn k n) x) u' <=
             dlim (fun j => \dlet_(x <- d j) h j x) u'.
    by apply/dlim_ub => j1 j2 hj;
       apply/le_dlet => [|x _]; [apply: mono_d | apply: mono_h].
  exact (le_trans h1 h2).
- apply/leub_dlim => n; apply/le_dlet.
    by apply/dlim_ub => k1 k2; apply: mono_d.
  by move=> x _; apply/dlim_ub => k1 k2 hle; apply: mono_h.
Qed.

Lemma dlet_dlim_diag' {T U : choiceType}
  (d : nat -> Distr T) (h : nat -> T -> Distr U) :
  (forall n m, (n <= m)%N -> d n <=1 d m) ->
  (forall x n m, (n <= m)%N -> h n x <=1 h m x) ->
  \dlet_(x <- \dlim_(n) d n) \dlim_(n) h n x =
    \dlim_(n) \dlet_(x <- d n) h n x.
Proof.
  move => mono_n mono_k.
  by apply/distr_eqP /dlet_dlim_diag.
Qed.

Section MISC.
Context {X Y : eqType} {mem : memType X}.
Definition psi := Y -> (@cmd_ X mem Y).

Lemma dlim_whilen n e c0 (ps':psi) s:
  ssem_aux (ubnf ps' n) (While e Do c0) s =
    \dlim_(n0) ssem_aux (ubnf ps' n) (whilen e c0 n0) s.
Proof.
rewrite /=.
apply: eq_dlim => n0.
move: s; elim: n0 => [|n0 IHn0] s //=.
case: (`[{e}] s) => //=.
apply: eq_in_dlet; [by move=> s' _; rewrite IHn0 | by []].
Qed.

Lemma le_whilen_aux (l : (Y * mem) -> {distr mem / R}) n e c m m' :
  ssem_aux l (whilen e c n) m m' <= ssem_aux l (whilen e c n.+1) m m'.
Proof.
elim: n m m' => /= [|n ih] m m'.
  by rewrite dnullE ge0_mu.
case: (esem e m) => //.
apply/le_in_dlet.
by move=> {m'} m _ m'; apply/ih.
Qed.

Lemma hmono_whilen (l  : (Y * mem) -> {distr mem / R})
  e c m n p :
  (n <= p)%N ->
  ssem_aux l (whilen e c n) m <=1  ssem_aux l (whilen e c p) m.
Proof.
elim: p n => [|p ih] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le_np m'.
by apply/(le_trans (ih _ le_np m'))/le_whilen_aux.
Qed.

Lemma test8 (ps' : psi) c s:
  ssem_ ps' c s =
  \dlim_(n) ssem_aux (ubnf ps' n) c s.
Proof.
  move : s.
  elim c.
  1-4,9: by move => * //=; rewrite /ssem_ unlock /ssem_r dlimC.
  + move => e ? hc1 ? hc2 s //=.
    rewrite semE.
    case (`[{e}] s).
    + by rewrite hc1.
    + by rewrite hc2.
  + move => e c0 h s.
    rewrite semE.
    symmetry; under eq_dlim do rewrite dlim_whilen.
    rewrite dlim_dlim_com.
    + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
    + by move => k *; rewrite hmono_whilen .
    apply eq_dlim => n.
    move : s.
    elim n.
    + by move => ? //=;rewrite semE dlimC.
    + move => {}n hi s //=.
      rewrite semE.
      case :(`[{e}] s); [|by rewrite semE dlimC].
      + rewrite semE -dlet_dlim_diag' //=.
        + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
        + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
        + apply /eq_in_dlet;[| by rewrite h].
          by move => ??;rewrite hi.
  + move => c1 hc1 c2 hc2 s //=.
    rewrite semE.
    rewrite -dlet_dlim_diag' //=.
    + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
    + by move => *; rewrite mono_ssem_aux // => *; rewrite homo_ubnf.
    + apply eq_in_dlet;[|by rewrite hc1].
      by move => *; rewrite hc2.
  + by move => f s; rewrite semE.
  + move => bs c0 h rs s //=.
    rewrite semE.
    rewrite -dlet_dlim_diag' //=.
    + by move => n m le; apply: mono_ssem_aux; exact: homo_ubnf.
    + apply eq_in_dlet; last by rewrite h.
      by move => *; rewrite dlimC.
Qed.

Lemma ssem_call_eq (ps0 : psi) f s:
  ssem_ ps0 (call f) s = ssem_ ps0 (ps0 f) s.
Proof.
rewrite [LHS]semE  [RHS]test8.
transitivity (\dlim_(n) ubnf ps0 n.+1 (f, s)).
  by apply/distr_eqP => x; rewrite (dlim_bump (fun n => ubnf ps0 n (f, s))).
by apply: eq_dlim => n /=.
Qed.

Lemma while_true_null s :
  dnull = \dlim_(n) ubn [eta dunit (T:=mem)] xpredT n s.
Proof.
  rewrite -(dlimC dnull).
  apply eq_dlim => n0.
  elim n0 => //=.
  move => n1 h.
  by rewrite dlet_unit h.
Qed.

Lemma ssem_loop_while (ps' : psi) s:
  ssem_ ps' (While true%:S Do skip) s = dnull.
Proof.
  rewrite semE //=.
  rewrite (eq_dlim (gn := fun _ => dnull)); last first. by rewrite dlimC.
  move=> k /=.
  elim k => [|{}k IHk] //=.
  +   by rewrite semE.
  by rewrite !semE dlet_unit IHk.
Qed.

(* -------------------------------------------------------------------- *)
(* [c] contains no [block].  The proof systems in hl/, ehl/, phl/, prhl/
 * and ellora/ have no rule for [block] yet, so their completeness proofs,
 * which proceed by induction on the command, are stated for such [c]. *)
Fixpoint noblock (c : cmd_ X mem Y) : Prop :=
  match c with
  | abort | skip | assign _ _ _ | random _ _ _ | call _ | gassign _ _ _ => True
  | cond _ c1 c2 => noblock c1 /\ noblock c2
  | while _ c    => noblock c
  | seqc c1 c2   => noblock c1 /\ noblock c2
  | block _ _ _ => False
  end.

End MISC.

Section Inliner.
  Context {X Y : eqType} {mem : memType X}.

Fixpoint inliner (c : cmd_ X mem Y) inline :=
  match c with
  | seqc p1 p2 => seqc (inliner p1 inline) (inliner p2 inline)
  | cond b p1 p2 => cond b (inliner p1 inline) (inliner p2 inline)
  | while b p => while b (inliner p inline)
  | call f => inline f
  | block bs p rs => block bs (inliner p inline) rs
  | _ => c
  end.

Fixpoint k_inliner1 n c (ps : psi) :=
  match n with
  | 0 => while (cst_ true) skip
  | S n' => inliner c (fun f => k_inliner1 n' (ps f) ps)
  end.

Definition k_inliner_ps1 n ps := fun p => k_inliner1 n (ps p) ps.

Fixpoint k_inliner2 n c (ps : psi) :=
  match n with
  | 0 => c
  | S n' => inliner c (fun f => k_inliner2 n' (ps f) ps)
  end.

Definition k_inliner_ps2 n ps := fun p => k_inliner2 n (ps p) ps.

Definition false_ps : @psi X Y mem  := (fun _ => while (cst_ true) skip).

Lemma ubnf_dnull n p s:
  (ubnf false_ps) n (p, s) = dnull.
Proof.
case n => [|{}n] //=.
rewrite (eq_dlim (gn := fun _ => dnull)); last first. by rewrite dlimC.
move=> k /=.
elim k => [|{}k IHk] //=.
by rewrite dlet_unit IHk.
Qed.

Lemma ssem_false_ps p s :
  ssem_ false_ps (call p) s = dnull.
Proof.
rewrite semE.
rewrite (eq_dlim (gn := fun _ => dnull)); last first. by rewrite dlimC.
move => n.
exact: ubnf_dnull.
Qed.

Lemma kinliner1_cseq n ps' p1 p2: k_inliner1 (S n) (seqc p1 p2) ps' =
                                seqc (k_inliner1 (S n) p1 ps') (k_inliner1 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner1_cif n ps' b p1 p2: k_inliner1 (S n) (cond b p1 p2) ps' =
                                 cond b (k_inliner1 (S n) p1 ps') (k_inliner1 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner1_cwhile n ps' p b: k_inliner1 (S n) (while b p) ps' =
                                           while b (k_inliner1 (S n) p ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner1_ccall n f ps' :
  k_inliner1 (S n) (call f) ps' = k_inliner1 n (ps' f) ps'.
Proof.
  reflexivity.
Qed.

Lemma kinliner1_cblock n ps' bs p rs :
  k_inliner1 (S n) (@block X mem Y bs p rs) ps' =
  block bs (k_inliner1 (S n) p ps') rs.
Proof.
  reflexivity.
Qed.


Lemma kinliner2_cseq n ps' p1 p2: k_inliner2 (S n) (seqc p1 p2) ps' =
                                seqc (k_inliner2 (S n) p1 ps') (k_inliner2 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner2_cif n ps' b p1 p2: k_inliner2 (S n) (cond b p1 p2) ps' =
                                 cond b (k_inliner2 (S n) p1 ps') (k_inliner2 (S n) p2 ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner2_cwhile n ps' p b: k_inliner2 (S n) (while b p) ps' =
                                           while b (k_inliner2 (S n) p ps').
Proof.
  reflexivity.
Qed.

Lemma kinliner2_ccall n f ps' :
  k_inliner2 (S n) (call f) ps' = k_inliner2 n (ps' f) ps'.
Proof.
  reflexivity.
Qed.

Lemma kinliner2_cblock n ps' bs p rs :
  k_inliner2 (S n) (@block X mem Y bs p rs) ps' =
  block bs (k_inliner2 (S n) p ps') rs.
Proof.
  reflexivity.
Qed.

Lemma inline12_split n m (ps1 : psi) c :
  k_inliner1 (S n) (k_inliner2 m c ps1) ps1 =
  k_inliner1 ((S n) + m) c ps1.
Proof.
  move: n c ps1.
  elim m.
  + move => n c ps1 //=.
    by rewrite addn0.
  + move => {}m h n c ps1.
    elim c.
    1-4,9 : move => //=.
    + move => e ? hc1 ? hc2.
      rewrite kinliner2_cif.
      rewrite kinliner1_cif.
      rewrite hc1 hc2.
      by rewrite (kinliner1_cif (n + m.+1)).
    + move => e ? hc1.
      rewrite kinliner2_cwhile.
      rewrite kinliner1_cwhile.
      rewrite hc1.
      by rewrite (kinliner1_cwhile (n + m.+1)).
    + move => ? hc1 ? hc2.
      rewrite kinliner2_cseq.
      rewrite kinliner1_cseq.
      rewrite hc1 hc2.
      by rewrite (kinliner1_cseq (n + m.+1)).
    + move => s.
      rewrite kinliner2_ccall.
      rewrite h.
      rewrite (kinliner1_ccall (n + m.+1)).
      by rewrite addSnnS.
    + move => ? ? hc ?.
      rewrite kinliner2_cblock.
      rewrite kinliner1_cblock.
      rewrite hc.
      by rewrite (kinliner1_cblock (n + m.+1)).
Qed.

Lemma ssem_ubnf_dnull (ps' : psi) c n s:
 ssem_aux (ubnf ps' n) c s =
   ssem_aux (fun _ => dnull) (k_inliner2 n c ps') s.
Proof.
  move : c s.
  elim n => [//=|n0 h c].
  elim c .
  10: { move => ? ? hc ? s //=.
        by apply: eq_in_dlet. }
  9: by move => * //=.
  1-4: move => * //=.
  + move => e ? hc1 ? hc2 s //=.
    case (`[{e}] s).
    + by rewrite hc1.
    + by rewrite hc2.
  + move => e c0 //= hi s.
    apply eq_dlim.
    move => n1.
    move :s.
    elim n1 => //=.
    move => n2 hii s.
    case (`[{e}] s) => //=.
    apply eq_in_dlet.
    + by move => s' ?;rewrite hii.
    + by rewrite hi.
  + move => ? hc1 ? hc2 s //=.
    apply: eq_in_dlet.
    + by move => ??; rewrite hc2.
    + by rewrite hc1.
  + move => f s //=.
Qed.

Lemma ubnf_ssem  c s:
  ssem_aux (fun _ => dnull) c s =
  ssem_ false_ps c s.
Proof.
  move :s.
  elim c.
  10: { move => ? ? hc ? s //=.
        rewrite semE.
        by apply: eq_in_dlet. }
  9: by move => * //=; rewrite !semE.
  + 1-4: by move => * //=; rewrite !semE.
  + move => e ? hc1 ? hc2 s //=.
    rewrite semE.
    case (`[{e}] s).
    + by rewrite hc1.
    + by rewrite hc2.
  + move => e c0 //= hi s.
    rewrite semE.
    apply eq_dlim.
    move => n1.
    move :s.
    elim n1 => //=.
    + by move => s; rewrite semE.
    move => n2 hii s; rewrite semE.
    case (`[{e}] s) => //=.
    rewrite semE.
    apply eq_in_dlet.
    + by move => s' ?;rewrite hii.
    + by rewrite hi.
     by rewrite semE.
  + move => ? hc1 ? hc2 s //=.
    rewrite semE.
    apply: eq_in_dlet.
    + by move => ??; rewrite hc2.
    + by rewrite hc1.
    + move => f s //=.
      rewrite semE.
      rewrite -(dlimC dnull).
      apply eq_dlim => n0.
      case : n0 => //= ?.
      by rewrite -while_true_null.
Qed.

Lemma test9 (ps' : psi) c n s:
  forall ps0,
    ssem_ false_ps (k_inliner2 n c ps') s =
    ssem_ ps0 (k_inliner1 (S n) c ps') s.
Proof.
move=> ps0.
move: c s.
elim: n => [|n IH] c s.
- (* n = 0 *)
  move: s.
  elim: c.
  10: { move=> ? ? hc ? s /=.
        rewrite !semE.
        by apply: eq_in_dlet. }
  9: by move=> * /=; rewrite !semE.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    by rewrite ssem_false_ps ssem_loop_while.
- (* n.+1 *)
  move: s.
  elim: c.
  10: { move=> ? ? hc ? s /=.
        rewrite !semE.
        by apply: eq_in_dlet. }
  9: by move=> * /=; rewrite !semE.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    exact: IH.
Qed.

Lemma test5 (ps1 ps2: psi) c s n:
  ssem_ ps2 (k_inliner1 (S n) c ps1) s = ssem_ (k_inliner_ps1 n ps1) c s.
Proof.
move: ps2 c s.
elim: n => [|n IH] ps2 c s.
- (* n = 0 *)
  move: s.
  elim: c.
  10: { move=> ? ? hc ? s /=.
        rewrite !semE.
        by apply: eq_in_dlet. }
  9: by move=> * /=; rewrite !semE.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    by rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    by rewrite ssem_loop_while ssem_false_ps.
- (* n.+1 *)
  move: s.
  elim: c.
  10: { move=> ? ? hc ? s /=.
        rewrite !semE.
        by apply: eq_in_dlet. }
  9: by move=> * /=; rewrite !semE.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    by rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    rewrite IH.
    symmetry; rewrite ssem_call_eq /=.
    by rewrite IH.
Qed.

Lemma inline2_split n m (ps1 : psi) c s:
  ssem_ (k_inliner_ps1 (m + n) ps1) c s  =
  ssem_ (k_inliner_ps1 n ps1) (k_inliner2 m c ps1) s.
Proof.
move: c s.
elim: m => [|m IH] c s.
- by [].
- move: s.
  elim: c.
  10: { move=> ? ? hc ? s /=.
        rewrite !semE.
        by apply: eq_in_dlet. }
  9: by move=> * /=; rewrite !semE.
  1-4: by move=> * /=; rewrite !semE.
  + move=> e c1 hc1 c2 hc2 s /=.
    by rewrite !semE; case: (`[{e}] s); [exact: hc1 | exact: hc2].
  + move=> e c0 hc s /=.
    rewrite [LHS]ssem_while_ubn [RHS]ssem_while_ubn.
    apply: eq_dlim => k.
    move: s; elim: k => [|k IHk] s //=.
    case: (`[{e}] s) => //.
    by apply: eq_in_dlet; [move=> s' _; exact: IHk | exact: hc].
  + move=> c1 hc1 c2 hc2 s /=.
    rewrite !semE.
    by apply: eq_in_dlet; [move=> s' _; exact: hc2 | exact: hc1].
  + move=> f s /=.
    rewrite -IH ssem_call_eq /= addSn.
    by rewrite test5.
Qed.

Lemma test1 (ps' : psi) c s:
  \dlim_(n) ssem_ (k_inliner_ps1 n ps') c s =  ssem_ ps' c s.
Proof.
  rewrite test8.
  apply: eq_dlim.
  + by move => ?; rewrite ssem_ubnf_dnull ubnf_ssem (test9 _ _ _ _ ps') test5.
Qed.

End Inliner.
