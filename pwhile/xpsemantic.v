(* -------------------------------------------------------------------- *)
(* Denotational semantics of the while language extended with exceptions. *)
(*                                                                        *)
(* This file is a copy of [psemantic.v] adapted to [xpwhile.v].            *)
(*                                                                        *)
(* WHY THE CODOMAIN HAD TO GROW.  In [psemantic.v], [abort] denotes        *)
(* [dnull], and so do a diverging loop and an exhausted call budget.       *)
(* Since [dnull] absorbs [dlet], [abort ;; c] *is* [abort] definitionally, *)
(* which is exactly why no continuation can observe it.  A catchable       *)
(* [raise] must be observable, so the result type has to distinguish a     *)
(* normal from an exceptional outcome:                                     *)
(*                                                                        *)
(*    osem_ ps c m : {distr outcome / R}    outcome = ONorm m | OExc m v   *)
(*                                                                        *)
(* WHY [ssem_] SURVIVES.  [ssem_] is kept, but *defined* as the normal-    *)
(* outcome projection [sproj] of [osem_].  Because an exceptional outcome  *)
(* of [c1] can never become a normal outcome of [c1 ;; c2], every equation *)
(* of the original [semE]/[bsemE] still holds verbatim -- see the block of *)
(* [ssem_*E] lemmas below.  In particular [ssem_ ps (raise k e) m = dnull]:*)
(* an *uncaught* exception is [abort] at the projected level, so the       *)
(* [H_Abort] rule of every logic already covers [raise].  [try_] is the    *)
(* one command with no projected equation -- which is the content of the   *)
(* feature, and why exception-aware rules must be stated against [osem_].  *)
(*                                                                        *)
(* This file must not be imported alongside [psemantic.v]/[pwhile.v]: the  *)
(* constructor names and notation strings coincide.  That is also why the  *)
(* [DistrRecast]/[DLimRecast]/[DProj]/[Ubn] preamble -- pure distribution  *)
(* theory, no command dependence -- is duplicated here rather than         *)
(* imported.  The duplication disappears when the two files are merged.    *)
(* -------------------------------------------------------------------- *)
From HB                 Require Import structures.
From Stdlib             Require Import ClassicalFacts Setoid Morphisms.
From mathcomp           Require Import boot order.
From mathcomp.algebra   Require Import algebra.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis  Require Import counting_distr esum.
(* ----------------- *) Require Import inhabited passn xpwhile mem.
(* [dinsupp_dlim], used only by the [noexc] bridge at the end of the file;
 * this is the same dependency [pwhile/range.v] has. *)
From xhl                Require Import misc.

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
(* Verbatim from [psemantic.v]: distribution lemmas at the equality level *)
Section DistrRecast.
Context {R : realType}.
Local Notation Distr T := {distr T%type / R}.
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

Lemma dlim_dlim_com (h : nat -> nat -> {distr T / R})
(hmono1: (forall k n1 n2, (n1 <= n2)%N -> h n1 k <=1 h n2 k))
(hmono2: (forall k n1 n2, (n1 <= n2)%N -> h k n1 <=1 h k n2)):
  \dlim_(n) (\dlim_(m) h n m) = \dlim_(m) (\dlim_(n) h n m).
Proof. apply /distr_eqP; exact: dlim_dlim_com. Qed.

Lemma dlet_dlim_diag
  (d : nat -> Distr T) (h : nat -> T -> Distr U) :
  (forall n m, (n <= m)%N -> d n <=1 d m) ->
  (forall x n m, (n <= m)%N -> h n x <=1 h m x) ->
  \dlet_(x <- \dlim_(n) d n) \dlim_(n) h n x =
    \dlim_(n) \dlet_(x <- d n) h n x.
Proof.  move => *; apply /distr_eqP; exact: dlet_dlim_diag. Qed.

End DistrRecast.

(* -------------------------------------------------------------------- *)
Section DLimRecast.
Context {R : realType}.
Variables (T U : choiceType).
Variables (f : nat -> {distr T / R}) (h : T -> {distr U / R}).

Lemma dlet_lim : (forall n m, (n <= m)%N -> f n <=1 f m) ->
  \dlet_(x <- \dlim_(n) f n) h x = \dlim_(n) \dlet_(x <- f n) h x.
Proof. by move=> ?; apply/distr_eqP/dlet_lim /dhomo_dnd. Qed.
End DLimRecast.

(* -------------------------------------------------------------------- *)
Section DProj.
Context {R : realType}.
Local Notation Distr T := {distr T%type / R}.
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
Section Ubn.
Context {R : realType}.
Local Notation Distr T := {distr T%type / R}.

Fixpoint ubn {A : choiceType} (f : A -> Distr A) (t : pred A) n := fun a =>
  if n is n.+1 return Distr A then
    if t a then \dlet_(x <- f a) ubn f t n x else dunit a
  else dnull.
End Ubn.

(* -------------------------------------------------------------------- *)
Reserved Notation "m .[ x <- v ]"
  (at level 1, x, v at level 200, format "m .[ x  <-  v ]").

Reserved Notation "m .{ x }"
  (at level 1, x at level 200, format "m .{ x }").

Reserved Notation "m .{ x <- v }"
  (at level 1, x, v at level 200, format "m .{ x  <-  v }").

Reserved Notation "m .[+ x <- v ]"
  (at level 1, x, v at level 200, format "m .[+  x  <-  v ]").

Reserved Notation "m .[+]" (at level 2, format "m .[+]").

(* -------------------------------------------------------------------- *)
Notation "m .[ x ]"     := (@mget _ _ _ _ _ (vtype x%V) m (vname x%V)) : mem_scope.
Notation "m .[ x <- v ]" := (@mset _ _ _ _ _ (vtype x%V) m (vname x%V) v) : mem_scope.

Notation "m .{ x }"     := (@mgetg _ _ _ _ _ (vtype x%V) m (vname x%V)) : mem_scope.
Notation "m .{ x <- v }" := (@msetg _ _ _ _ _ (vtype x%V) m (vname x%V) v) : mem_scope.

Notation "m .[+ x <- v ]" := (@mpush _ _ _ _ _ (vtype x%V) m (vname x%V) v) : mem_scope.

Notation "m .[+]" := (mnew m) (at level 2, format "m .[+]") : mem_scope.

(* -------------------------------------------------------------------- *)
Section Semantics.
  Context {R : realType} {A B : codeType} {X Xg Y : eqType} {M: memType A B X Xg}
          {exn : eqType} {exnty : exn -> A}.

Local Notation Distr T := {distr T%type / R}.

Notation vars    := (vars_ X).
Notation gvars   := (vars_ Xg).
Notation expr    := (@expr_ A B X Xg M).
Notation cmd     := (@cmd_ R A B X Xg M exn exnty Y).
Notation binding := (@binding A B X Xg M).
Notation bexpr   := (expr bool).
Notation dexpr T := (expr (Distr T)).

Notation mdistr := (Distr M).
Notation mnull  := (@dnull R M).

(* -------------------------------------------------------------------- *)
(* Expressions are unchanged: [esem] is total, no expression can fail.    *)
Fixpoint esem {T : Type} (e : expr T) (m : M) : T :=
  match e in expr_ _ _ _ _ _ T return T with
  | var_ T x => m.[x]
  | cst_ T c => c
  | prp_ P   => P m
  | app_ T U e1 e2 => (esem e1 m) (esem e2 m)
  | gvar_ T x => m.{x}
  end.

(* -------------------------------------------------------------------- *)
Definition minit (m : M) (bs : seq binding) : M :=
  foldl (fun m' (b : binding) => let: existT _ (x, e) := b in m'.[x <- esem e m])
        m.[+] bs.

Definition mret (m m' : M) (rs : seq binding) : M :=
  foldl (fun mm (b : binding) => let: existT _ (r, e') := b in mm.[r <- esem e' m'])
        (mrestore m m') rs.

(* -------------------------------------------------------------------- *)
(* Outcomes                                                              *)
(*                                                                       *)
(* [OExc m v] records the memory *at the raise point* together with the   *)
(* raised value, tagged by its name.                                     *)
(* -------------------------------------------------------------------- *)
Definition exnv := {k : exn & interp (exnty k)}.

Variant outcome := ONorm of M | OExc of M & exnv.

Lemma outcome_comparable : comparable outcome.
Proof. by move=> o1 o2; apply/pselect. Qed.

HB.instance Definition outcome_eqType :=
  hasDecEq.Build outcome (compareP outcome_comparable).

HB.instance Definition outcome_choiceType := gen_choiceMixin outcome.

Notation odistr := (Distr outcome).
Notation onull  := (@dnull R outcome).

(* Kleisli bind that propagates an exceptional outcome untouched. *)
Definition obind (f : M -> odistr) (o : outcome) : odistr :=
  if o is ONorm m then f m else dunit o.

(* The normal-outcome projection: this is what turns [osem_] into [ssem_]. *)
Definition oproj (o : outcome) : mdistr :=
  if o is ONorm m then dunit m else mnull.

Definition sproj (mu : odistr) : mdistr := \dlet_(o <- mu) oproj o.

(* [ocatch k x h o]: if [o] raised exactly [k], bind the payload to [x] in
 * the raise-point memory and run the handler; otherwise re-raise. *)
Definition ocatch (k : exn) (x : vars (exnty k)) (h : M -> odistr)
    (o : outcome) : odistr :=
  match o with
  | ONorm _ => dunit o
  | OExc m t =>
      let: existT k' v := t in
      match k' =P k with
      | ReflectT eq => h (m.[x <- ecast z (interp (exnty z)) eq v])
      | ReflectF _  => dunit o
      end
  end.

Arguments ocatch : clear implicits.

(* -------------------------------------------------------------------- *)
(* Bounded unfolding of a loop.  As in [psemantic.v] the exhausted budget *)
(* contributes no mass ([onull]); the normal exit is [ONorm m].          *)
Fixpoint oubn (f : M -> odistr) (t : pred M) n := fun m =>
  if n is n.+1 return odistr then
    (if t m then \dlet_(o <- f m) obind (oubn f t n) o else dunit (ONorm m))
  else onull.

(* -------------------------------------------------------------------- *)
Fixpoint osem_aux (l: (Y * M) -> odistr) (s : cmd) (m : M) : odistr :=
  match s with
  | abort => onull
  | skip  => dunit (ONorm m)

  | x <<- e =>
      dunit (ONorm m.[x <- esem e m])

  | gassign _ x e =>
      dunit (ONorm m.{x <- esem e m})

  | x <$- e =>
      \dlet_(v <- esem e m) (dunit (ONorm m.[x <- v]))

  | block bs c rs =>
      \dlet_(o <- osem_aux l c (minit m bs))
        match o with
        | ONorm m'  => dunit (ONorm (mret m m' rs))
        (* an exception escaping a block still restores the caller's local
         * store (and keeps the callee's globals); [rs] is skipped *)
        | OExc m' v => dunit (OExc (mrestore m m') v)
        end

  | If e then c1 else c2 =>
      match esem e m with
      | true  => osem_aux l c1 m
      | false => osem_aux l c2 m
      end

  | While e Do c =>
      dlim (fun n => oubn (osem_aux l c) (esem e) n m)

  | seqc c1 c2 =>
      \dlet_(o <- osem_aux l c1 m) obind (osem_aux l c2) o

  | call n => l (n, m)

  | raise k e =>
      dunit (OExc m (existT _ k (esem e m)))

  | try_ c k x h =>
      \dlet_(o <- osem_aux l c m) ocatch k x (osem_aux l h) o
  end.

Fixpoint oubnf (ps: Y -> cmd) n :=
  fun (a: Y * M) =>
    if n is n.+1 return odistr then
      osem_aux (oubnf ps n) (ps (fst a)) (snd a)
    else onull.

Definition osem_r (ps : Y -> cmd) s m :=
  osem_aux (fun l => dlim (fun n => oubnf ps n l)) s m.

(* -------------------------------------------------------------------- *)
Fact osem_key : unit. Proof. by []. Qed.
Definition osem_ := locked_with osem_key osem_r.
Canonical osem_unlockable := [unlockable fun osem_].

(* [ssem_] is the normal-outcome projection of [osem_]. *)
Definition ssem_r (ps : Y -> cmd) s m := sproj (osem_r ps s m).

Fact ssem_key : unit. Proof. by []. Qed.
Definition ssem_ := locked_with ssem_key ssem_r.
Canonical ssem_unlockable := [unlockable fun ssem_].

(* -------------------------------------------------------------------- *)
Implicit Types (m : M) (c : cmd) (ps : Y -> cmd).

Notation prp := prp_.

(* -------------------------------------------------------------------- *)
(* Monotonicity                                                          *)
(* -------------------------------------------------------------------- *)
Lemma le_obind (f g : M -> odistr) o :
  (forall m, f m <=1 g m) -> obind f o <=1 obind g o.
Proof.
by move=> le_fg; case: o => [m|m v] /=; [exact: le_fg | move=> ?; rewrite lexx].
Qed.

Lemma le_ocatch k x (h h' : M -> odistr) o :
  (forall m, h m <=1 h' m) -> ocatch k x h o <=1 ocatch k x h' o.
Proof.
move=> le_h; case: o => [m|m [k' v]] /=; first by move=> ?; rewrite lexx.
by case: (k' =P k) => [e|_]; [exact: le_h | move=> ?; rewrite lexx].
Qed.

(* congruence for the two new combinators; used all over the ports below *)
Lemma eq_obind (f g : M -> odistr) o :
  (forall m, f m = g m) -> obind f o = obind g o.
Proof. by move=> h; case: o => [m|m v] /=; first exact: h. Qed.

Lemma eq_ocatch k x (h h' : M -> odistr) o :
  (forall m, h m = h' m) -> ocatch k x h o = ocatch k x h' o.
Proof.
move=> hh; case: o => [m|m [k' v]] /=; first by [].
by case: (k' =P k) => [e|_]; first exact: hh.
Qed.

Lemma le_oubn_body (f g : M -> odistr) (t : pred M) n :
  (forall m, f m <=1 g m) -> forall m, oubn f t n m <=1 oubn g t n m.
Proof.
move=> le_fg; elim: n => [|n ih] m o //=.
case: ifP => // _; apply/le_dlet => [|o' _]; first exact: le_fg.
by apply/le_obind => m'; exact: ih.
Qed.

Lemma le_oubn_n (f : M -> odistr) (t : pred M) n m :
  oubn f t n m <=1 oubn f t n.+1 m.
Proof.
elim: n m => [|n ih] m o /=; first exact: lef_dnull.
case: ifP => // _; apply/le_in_dlet => // o' _.
by apply/le_obind => m'; exact: ih.
Qed.

Lemma homo_oubn_n (f : M -> odistr) (t : pred M) n p m :
  (n <= p)%N -> oubn f t n m <=1 oubn f t p m.
Proof.
elim: p n => [|p ihp] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le o.
by apply/(le_trans (ihp _ le o))/le_oubn_n.
Qed.

Lemma mono_osem_aux (l l' : (Y * M) -> odistr) c m :
  (forall x, l x <=1 l' x) -> osem_aux l c m <=1 osem_aux l' c m.
Proof.
move=> le_ll'; elim: c m =>
  [||T x e|???|T x e|? c ih ?|e c1 ih1 c2 ih2|e c ih|c1 ih1 c2 ih2|f
   |k e|c ih k x ch ihh] m o //=.
- apply/le_dlet => [|[m0|m0 v] _]; first exact: ih.
  + by move=> ?; rewrite lexx.
  + by move=> ?; rewrite lexx.
- by case: ifP => _; [exact: ih1 | exact: ih2].
- have hb : forall m0, osem_aux l c m0 <=1 osem_aux l' c m0 by exact: ih.
  apply/leub_dlim => n o0.
  apply: (le_trans (@le_oubn_body _ _ (esem e) n hb m o0)).
  by apply/dlim_ub => n1 n2 hle; exact: homo_oubn_n.
- apply/le_dlet => [|o' _]; first exact: ih1.
  by apply/le_obind => m'; exact: ih2.
- apply/le_dlet => [|o' _]; first exact: ih.
  by apply/le_ocatch => m'; exact: ihh.
Qed.

Lemma mono_oubnf ps n a : oubnf ps n a <=1 oubnf ps n.+1 a.
Proof.
elim: n a => [|n ih] [f m'] /=; first exact: lef_dnull.
by apply/mono_osem_aux => x; exact: ih.
Qed.

Lemma homo_oubnf ps n p a : (n <= p)%N -> oubnf ps n a <=1 oubnf ps p a.
Proof.
elim: p n => [|p ihp] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le o.
by apply/(le_trans (ihp _ le o))/mono_oubnf.
Qed.

(* -------------------------------------------------------------------- *)
(* Equations for the exception-aware semantics                           *)
(* -------------------------------------------------------------------- *)
Lemma osem_eqP ps c1 c2 :
  (forall m, osem_ ps c1 m = osem_ ps c2 m) <-> osem_ ps c1 = osem_ ps c2.
Proof. by split=> [|->//] eq; apply/funext=> m. Qed.

Fixpoint whilen (e : bexpr) (c : cmd) n :=
  if n is n.+1 then
    (If e then (c;; whilen e c n) else skip)
  else abort.

Lemma osem_abortE ps m : osem_ ps abort m = onull.
Proof. by rewrite unlock. Qed.

Lemma osem_skipE ps m : osem_ ps skip m = dunit (ONorm m).
Proof. by rewrite unlock. Qed.

Lemma osem_assnE ps {T} (x : vars T) (e : expr T) m :
  osem_ ps (x <<- e) m = dunit (ONorm m.[x <- esem e m]).
Proof. by rewrite unlock. Qed.

Lemma osem_gassnE ps {T} (x : gvars T) (e : expr T) m :
  osem_ ps (G x <<- e) m = dunit (ONorm m.{x <- esem e m}).
Proof. by rewrite unlock. Qed.

Lemma osem_rndE ps {T} (x : vars T) (e : dexpr T) m :
  osem_ ps (x <$- e) m = \dlet_(v <- esem e m) (dunit (ONorm m.[x <- v])).
Proof. by rewrite unlock. Qed.

Lemma osem_blockE ps bs c rs m :
  osem_ ps (Block bs Do c Return rs) m =
    \dlet_(o <- osem_ ps c (minit m bs))
      match o with
      | ONorm m'  => dunit (ONorm (mret m m' rs))
      | OExc m' v => dunit (OExc (mrestore m m') v)
      end.
Proof. by rewrite unlock. Qed.

Lemma osem_ifE ps e c1 c2 m :
  osem_ ps (If e then c1 else c2) m =
    if esem e m then osem_ ps c1 m else osem_ ps c2 m.
Proof. by rewrite unlock. Qed.

Lemma osem_seqE ps c1 c2 m :
  osem_ ps (c1 ;; c2) m = \dlet_(o <- osem_ ps c1 m) obind (osem_ ps c2) o.
Proof. by rewrite unlock. Qed.

Lemma osem_while_ubn ps e c m :
  osem_ ps (While e Do c) m = dlim (fun n => oubn (osem_ ps c) (esem e) n m).
Proof. by rewrite unlock. Qed.

Lemma osem_callE ps f m :
  osem_ ps (call f) m = dlim (fun n => oubnf ps n (f,m)).
Proof. by rewrite unlock. Qed.

Lemma osem_raiseE ps k (e : expr (interp (exnty k))) m :
  osem_ ps (raise k e) m = dunit (OExc m (existT _ k (esem e m))).
Proof. by rewrite unlock. Qed.

Lemma osem_tryE ps c k x h m :
  osem_ ps (try_ c k x h) m =
    \dlet_(o <- osem_ ps c m) ocatch k x (osem_ ps h) o.
Proof. by rewrite unlock. Qed.

Lemma osem_whileE ps e c m :
  osem_ ps (While e Do c) m = dlim (fun n => osem_ ps (whilen e c n) m).
Proof.
rewrite osem_while_ubn; apply/eq_dlim=> n /=.
elim: n m => /= [|n ih] m; first by rewrite osem_abortE.
rewrite osem_ifE; case: (esem e m); last by rewrite osem_skipE.
rewrite osem_seqE; apply/eq_in_dlet => //.
by move=> [m0|m0 v] _ /=; rewrite ?ih.
Qed.

Definition osemE :=
  (osem_abortE , osem_skipE  , @osem_assnE , @osem_gassnE,
   @osem_rndE  , osem_blockE , osem_ifE    , osem_whileE ,
   osem_seqE   , osem_callE  , @osem_raiseE, osem_tryE).

(* -------------------------------------------------------------------- *)
(* The projection toolkit                                                *)
(* -------------------------------------------------------------------- *)
Lemma sproj_dunit_n m : sproj (dunit (ONorm m)) = dunit m.
Proof. by rewrite /sproj dlet_unit. Qed.

Lemma sproj_dunit_e m v : sproj (dunit (OExc m v)) = mnull.
Proof. by rewrite /sproj dlet_unit. Qed.

Lemma sproj_dnull : sproj onull = mnull.
Proof. by rewrite /sproj dlet_null. Qed.

Lemma sproj_dlet {T : choiceType} (mu : Distr T) (f : T -> odistr) :
  sproj (\dlet_(x <- mu) f x) = \dlet_(x <- mu) sproj (f x).
Proof. by rewrite /sproj dlet_dlet. Qed.

(* The key compositionality fact: projecting a bind is binding the
 * projections.  This is what preserves every equation of [semE]. *)
Lemma sproj_obind (f : M -> odistr) (mu : odistr) :
  sproj (\dlet_(o <- mu) obind f o) = \dlet_(m <- sproj mu) sproj (f m).
Proof.
rewrite /sproj !dlet_dlet; apply/eq_in_dlet => // -[m|m v] _ /=;
  by rewrite ?dlet_unit ?dlet_null.
Qed.

Lemma sproj_oubn (f : M -> odistr) (t : pred M) n m :
  sproj (oubn f t n m) = ubn (fun m0 => sproj (f m0)) t n m.
Proof.
elim: n m => [|n ih] m /=; first exact: sproj_dnull.
case: ifP => _; last exact: sproj_dunit_n.
by rewrite sproj_obind; apply/eq_in_dlet => // m0 _; exact: ih.
Qed.

Lemma sproj_dlim (F : nat -> odistr) :
  (forall n p, (n <= p)%N -> F n <=1 F p) ->
  sproj (\dlim_(n) F n) = \dlim_(n) sproj (F n).
Proof. by move=> h; rewrite /sproj dlet_lim. Qed.

(* -------------------------------------------------------------------- *)
(* Equations for the projected semantics: all of [psemantic.v]'s [semE]  *)
(* holds verbatim.                                                       *)
(* -------------------------------------------------------------------- *)
Lemma ssem_osemE ps c m : ssem_ ps c m = sproj (osem_ ps c m).
Proof. by rewrite !unlock. Qed.

Lemma sem_eqP ps c1 c2 :
  (forall m, ssem_ ps c1 m = ssem_ ps c2 m) <-> ssem_ ps c1 = ssem_ ps c2.
Proof. by split=> [|->//] eq; apply/funext=> m. Qed.

Lemma ssem_abortE ps m : ssem_ ps abort m = mnull.
Proof. by rewrite ssem_osemE osem_abortE sproj_dnull. Qed.

Lemma ssem_skipE ps m : ssem_ ps skip m = dunit m.
Proof. by rewrite ssem_osemE osem_skipE sproj_dunit_n. Qed.

Lemma ssem_assnE ps {T} (x : vars T) (e : expr T) m :
  ssem_ ps (x <<- e) m = dunit (m.[x <- esem e m]).
Proof. by rewrite ssem_osemE osem_assnE sproj_dunit_n. Qed.

Lemma ssem_gassnE ps {T} (x : gvars T) (e : expr T) m :
  ssem_ ps (G x <<- e) m = dunit m.{x <- esem e m}.
Proof. by rewrite ssem_osemE osem_gassnE sproj_dunit_n. Qed.

Lemma ssem_rndE ps {T} (x : vars T) (e : dexpr T) m :
  ssem_ ps (x <$- e) m = \dlet_(v <- esem e m) (dunit m.[x <- v]).
Proof.
rewrite ssem_osemE osem_rndE sproj_dlet.
by apply/eq_in_dlet => // v _; exact: sproj_dunit_n.
Qed.

Lemma ssem_ifE ps e c1 c2 m :
  ssem_ ps (If e then c1 else c2) m =
    if esem e m then ssem_ ps c1 m else ssem_ ps c2 m.
Proof. by rewrite !ssem_osemE osem_ifE; case: (esem e m). Qed.

Lemma ssem_seqE ps c1 c2 m :
  ssem_ ps (c1 ;; c2) m = \dlet_(m' <- ssem_ ps c1 m) (ssem_ ps c2 m').
Proof.
rewrite !ssem_osemE osem_seqE sproj_obind.
by apply/eq_in_dlet => // m' _; rewrite ssem_osemE.
Qed.

Lemma ssem_blockE ps bs c rs m :
  ssem_ ps (Block bs Do c Return rs) m =
    \dlet_(m' <- ssem_ ps c (minit m bs)) dunit (mret m m' rs).
Proof.
rewrite !ssem_osemE osem_blockE sproj_dlet /sproj dlet_dlet.
by apply/eq_in_dlet => // -[m'|m' v] _ /=; rewrite !dlet_unit ?dlet_null.
Qed.

Lemma ssem_while_ubn ps e c m :
  ssem_ ps (While e Do c) m = dlim (fun n => ubn (ssem_ ps c) (esem e) n m).
Proof.
have mono : forall n p, (n <= p)%N ->
    oubn (osem_ ps c) (esem e) n m <=1 oubn (osem_ ps c) (esem e) p m.
  by move=> n p le; exact: homo_oubn_n.
rewrite ssem_osemE osem_while_ubn (sproj_dlim mono).
apply/eq_dlim => n; rewrite sproj_oubn.
congr (ubn _ _ _ _); apply/funext => m0.
by rewrite ssem_osemE.
Qed.

Lemma ssem_whileE ps e c m :
  ssem_ ps (While e Do c) m = dlim (fun n => ssem_ ps (whilen e c n) m).
Proof.
rewrite ssem_while_ubn; apply/eq_dlim => n /=.
elim: n m => /= [|n ih] m; first by rewrite ssem_abortE.
rewrite ssem_ifE; case: (esem e m); last by rewrite ssem_skipE.
by rewrite ssem_seqE; apply/eq_in_dlet => // m0 _; exact: ih.
Qed.

(* the projected call-depth approximant: [psemantic.v]'s [ubnf] *)
Definition ubnf (ps : Y -> cmd) n (a : Y * M) : mdistr := sproj (oubnf ps n a).

Lemma ssem_callE ps f m :
  ssem_ ps (call f) m = dlim (fun n => ubnf ps n (f,m)).
Proof.
have mono : forall n p, (n <= p)%N -> oubnf ps n (f,m) <=1 oubnf ps p (f,m).
  by move=> n p le; exact: homo_oubnf.
by rewrite ssem_osemE osem_callE (sproj_dlim mono).
Qed.

Lemma le_sproj (mu nu : odistr) : mu <=1 nu -> sproj mu <=1 sproj nu.
Proof. by move=> h; apply/le_dlet => [|o _ m]; [exact: h | rewrite lexx]. Qed.

Lemma mono_ubnf ps n a : ubnf ps n a <=1 ubnf ps n.+1 a.
Proof. by apply/le_sproj/mono_oubnf. Qed.

Lemma homo_ubnf ps n p a : (n <= p)%N -> ubnf ps n a <=1 ubnf ps p a.
Proof. by move=> le; apply/le_sproj/homo_oubnf. Qed.

(* An *uncaught* exception is [abort] at the projected level. *)
Lemma ssem_raiseE ps k (e : expr (interp (exnty k))) m :
  ssem_ ps (raise k e) m = mnull.
Proof. by rewrite ssem_osemE osem_raiseE sproj_dunit_e. Qed.

(* [try_] is the one command whose projection is not determined by the
 * projections of its sub-commands -- that is exactly the feature. *)
Lemma ssem_tryE ps c k x h m :
  ssem_ ps (try_ c k x h) m =
    \dlet_(o <- osem_ ps c m) sproj (ocatch k x (osem_ ps h) o).
Proof. by rewrite ssem_osemE osem_tryE sproj_dlet. Qed.

Definition semE :=
  (ssem_abortE , ssem_skipE  , @ssem_assnE , @ssem_gassnE,
   @ssem_rndE  , ssem_blockE , ssem_ifE    , ssem_whileE ,
   ssem_seqE   , ssem_callE  , @ssem_raiseE, ssem_tryE).

Definition bsemE := locked (
  fun ps => funext (ssem_abortE ps),
  fun ps => funext (ssem_skipE ps),
  fun ps T (x : vars T) (e : expr _) => funext (ssem_assnE ps x e),
  fun ps T (x : gvars T) (e : expr _) => funext (ssem_gassnE ps x e),
  fun ps T (x : vars T) (e : expr _) => funext (ssem_rndE ps x e),
  fun ps bs c rs => funext (ssem_blockE ps bs c rs),
  fun ps e c1 c2 => funext (ssem_ifE ps e c1 c2),
  fun ps e c => funext (ssem_whileE ps e c),
  fun ps c1 c2 => funext (ssem_seqE ps c1 c2),
  fun ps f => funext (ssem_callE ps f),
  fun ps k e => funext (@ssem_raiseE ps k e),
  fun ps c k x h => funext (@ssem_tryE ps c k x h)).

(* -------------------------------------------------------------------- *)
(* Expression equations, unchanged                                       *)
(* -------------------------------------------------------------------- *)
Lemma esem_varE {T : A} (x : vars T) m :
   esem (@var_ _ _ _ _ _ T x) m = m.[x].
Proof. by []. Qed.

Lemma esem_cstE {T : Type} (c : T) m : esem (cst_ c) m = c.
Proof. by []. Qed.

Lemma esem_prpE (P : pred M) m : esem (prp_ P) m = P m.
Proof. by []. Qed.

Lemma esem_appE {T U : Type} (e1 : expr (T -> U)) (e2 : expr T) m :
  esem (app_ e1 e2) m = (esem e1 m) (esem e2 m).
Proof. by []. Qed.

Lemma esem_gvarE {T : B} (x : gvars T) m :
   esem (@gvar_ _ _ _ _ _ T x) m = m.{x}.
Proof. by []. Qed.

Lemma prpP (P : pred M) m : reflect (P m) (esem (prp_ P) m).
Proof. by apply/idP. Qed.

(* -------------------------------------------------------------------- *)
(* Equational theory of [ssem_], ported from [psemantic.v:354-537].      *)
(* Every one of these proofs goes through unchanged: they only ever use   *)
(* the [semE]/[bsemE] equations, which the projection preserves.  The     *)
(* only edit is that [ps] is an explicit argument here.                   *)
(* -------------------------------------------------------------------- *)
Lemma sem_seqA ps c1 c2 c3 :
  ssem_ ps ((c1 ;; c2) ;; c3) = ssem_ ps (c1 ;; (c2 ;; c3)).
Proof. by apply/sem_eqP=> m; rewrite !bsemE dlet_dlet. Qed.

Lemma sem_ifseq ps e ct cf c :
    ssem_ ps ((If e then ct else cf) ;; c)
  = ssem_ ps (If e then (ct ;; c) else (cf ;; c)).
Proof. by apply/sem_eqP=> m; rewrite !bsemE; case: ifP. Qed.

Lemma sem_seql ps c1 c1' c2 :
  ssem_ ps c1 =1 ssem_ ps c1' -> ssem_ ps (c1 ;; c2) = ssem_ ps (c1' ;; c2).
Proof. by move/sem_eqP=> eq; rewrite !bsemE eq. Qed.

Lemma sem_seqr ps c1 c2 c2' :
  ssem_ ps c2 =1 ssem_ ps c2' -> ssem_ ps (c1 ;; c2) = ssem_ ps (c1 ;; c2').
Proof. by move/sem_eqP=> eq; rewrite !bsemE eq. Qed.

Lemma sem_ift ps e ct ct' cf : ssem_ ps ct =1 ssem_ ps ct' ->
  ssem_ ps (If e then ct else cf) = ssem_ ps (If e then ct' else cf).
Proof. by move=> /sem_eqP eq; rewrite !bsemE eq. Qed.

Lemma sem_iff ps e ct cf cf' : ssem_ ps cf =1 ssem_ ps cf' ->
  ssem_ ps (If e then ct else cf) = ssem_ ps (If e then ct else cf').
Proof. by move=> /sem_eqP eq; rewrite !bsemE eq. Qed.

Lemma sem_whileb ps e c c' :
  ssem_ ps c =1 ssem_ ps c' ->
  ssem_ ps (While e Do c) = ssem_ ps (While e Do c').
Proof.
move=> /sem_eqP eq; apply/sem_eqP=> m; rewrite !semE.
apply/eq_dlim=> /= n; elim: n m => //= n /sem_eqP ih m.
by rewrite !bsemE ih eq.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dlim_seql ps (C : nat -> cmd) (c : cmd) m :
     (forall m n p, (n <= p)%N -> ssem_ ps (C n) m <=1 ssem_ ps (C p) m)
  -> \dlim_(n) (ssem_ ps (C n ;; c) m)
   = \dlet_(m' <- \dlim_(n) ssem_ ps (C n) m) ssem_ ps c m'.
Proof.
move=> leC; rewrite dlet_lim.
+ by apply/leC.
by apply/eq_dlim=> n; rewrite semE.
Qed.

Lemma dlim_seqr ps (C : nat -> cmd) (c : cmd) m :
     (forall m n p, (n <= p)%N -> ssem_ ps (C n) m <=1 ssem_ ps (C p) m)
  -> \dlim_(n) (ssem_ ps (c ;; C n) m)
   = \dlet_(m' <- ssem_ ps c m) \dlim_(n) (ssem_ ps (C n) m').
Proof.
move=> leC; rewrite -dlim_let //.
by apply/eq_dlim => n; rewrite semE.
Qed.

Lemma dlim_ift ps (e : bexpr) (C : nat -> cmd) (c : cmd) m :
    \dlim_(n) (ssem_ ps (If e then C n else c) m)
  = if esem e m then \dlim_(n) ssem_ ps (C n) m else ssem_ ps c m.
Proof.
pose F n := if esem e m then ssem_ ps (C n) m else ssem_ ps c m.
rewrite -(@eq_dlim _ _ F) {}/F => [k |].
+ by rewrite !semE.
by case: ifPn => _; rewrite ?dlimC.
Qed.

Lemma dlim_iff ps (e : bexpr) (C : nat -> cmd) (c : cmd) m :
    \dlim_(n) (ssem_ ps (If e then c else C n) m)
  = if esem e m then ssem_ ps c m else \dlim_(n) ssem_ ps (C n) m.
Proof.
pose F n := if esem e m then ssem_ ps c m else ssem_ ps (C n) m.
rewrite -(@eq_dlim _ _ F) {}/F => [k|].
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
Lemma homo_ssem ps (mu1 mu2 : mdistr) c :
  mu1 <=1 mu2 ->
  \dlet_(m <- mu1) ssem_ ps c m <=1 \dlet_(m <- mu2) ssem_ ps c m.
Proof. by move=> le_mu m; apply/le_dlet. Qed.

Lemma sem_seq_le ps c1 c2 c1' c2' :
     ssem_ ps c1 <=2 ssem_ ps c1'
  -> ssem_ ps c2 <=2 ssem_ ps c2'
  -> ssem_ ps (c1 ;; c2) <=2 ssem_ ps (c1' ;; c2').
Proof. by move=> le1 le2 m1 m2; rewrite !semE; apply/le_dlet. Qed.

Lemma le_whilen ps (n : nat) (e : bexpr) (c : cmd) m m' :
  ssem_ ps (whilen e c n) m m' <= ssem_ ps (whilen e c n.+1) m m'.
Proof.
elim: n m m' => /= [|n ih] m m'.
  by rewrite ssem_abortE dnullE ge0_mu.
rewrite !ssem_ifE; case: (esem e m) => //.
rewrite !ssem_seqE; apply/le_in_dlet.
by move=> {m'} m _ m'; apply/ih.
Qed.

Lemma homo_whilen ps e c m n p : (n <= p)%N ->
  ssem_ ps (whilen e c n) m <=1 ssem_ ps (whilen e c p) m.
Proof.
elim: p n => [|p ih] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le_np m'.
by apply/(le_trans (ih _ le_np m'))/le_whilen.
Qed.

Lemma unroll_while_w ps (e e' : bexpr) c m :
     (forall m, esem e' m -> esem e m)
  -> ssem_ ps (While e Do c) m =
     ssem_ ps (IfT e' then c ;; While e Do c) m.
Proof.
move=> impe; apply/distr_eqP=> m'; rewrite !semE.
case: ifPn => h; last by rewrite dlet_unit -semE.
rewrite -dlim_bump /= -ssem_seqE dlim_ift.
rewrite dlim_seqr.
+ by apply/homo_whilen.
rewrite impe // semE; apply/distr_eqP: m'.
by apply/eq_in_dlet=> // m' _; rewrite semE.
Qed.

Lemma unroll_while ps (e : bexpr) c m :
  ssem_ ps (While e Do c) m =
  ssem_ ps (IfT e then c ;; While e Do c) m.
Proof. by apply/unroll_while_w. Qed.

Lemma unroll_while_in ps (e : bexpr) c m :
  ssem_ ps (While e Do c) m =
  ssem_ ps (IfT e then (c ;; While e Do c)) m.
Proof.
rewrite unroll_while !semE; case: ifP => // h.
rewrite dlet_unit semE; apply/distr_eqP=> m'.
by rewrite -dlim_bump /= dlim_ift h semE.
Qed.

Lemma ssem_while0 ps (e : bexpr) c m : ~~ esem e m ->
  ssem_ ps (While e Do c) m = dunit m.
Proof. by rewrite unroll_while_in !semE => /negbTE ->. Qed.

Lemma ssem_whileS ps (e : bexpr) c m : esem e m ->
  ssem_ ps (While e Do c) m = ssem_ ps (c ;; While e Do c) m.
Proof. by rewrite unroll_while_in !semE => ->. Qed.

Lemma unrolls_while_w ps (e e' : bexpr) c m :
     (forall m, esem e' m -> esem e m)
  -> ssem_ ps (While e Do c) m =
     ssem_ ps (While e' Do c;; While e Do c) m.
Proof.
move=> impe; apply/distr_eqP=> m'; apply/eqP.
rewrite eq_le andbC; apply/andP; split.
+ rewrite ssem_seqE (ssem_whileE ps e') dlet_lim.
  + apply/homo_whilen.
  apply/leub_dlim => n {}m'; rewrite -ssem_seqE.
  elim: n m m' => [|n ihn] m m' /=.
    by rewrite !semE dlet_null; apply/lef_dnull.
  rewrite sem_ifseq ssem_ifE; case: ifPn => [/impe em|].
    by rewrite ssem_whileS // sem_seqA; apply/sem_seq_le.
  by rewrite 2!semE dlet_unit.
+ rewrite ssem_whileE; apply/leub_dlim; move: {m'} m => [:a] m n m'.
  case/asboolP: (esem e' m) => [|/negP]; last first.
  abstract: a n m m' => h; rewrite ssem_seqE (@ssem_while0 ps e') //.
  rewrite dlet_unit semE; apply/dlim_ub=> {m'} k p le_kp m'.
  by apply/homo_whilen.
elim: n m m' => [|n ihn] m m' h.
  by rewrite ssem_abortE; apply/lef_dnull.
rewrite ssem_ifE impe // !ssem_seqE ssem_whileS //.
rewrite ssem_seqE dlet_dlet; apply/le_in_dlet=> {h m'} m _ m'.
rewrite -ssem_seqE; case/asboolP: (esem e' m) => [|/negP h].
  by move/ihn. by apply/a.
Qed.

Lemma split_while ps (e1 e2 : bexpr) c :
     ssem_ ps (While e1 Do c)
   = ssem_ ps (While (e1 && e2) Do c ;; While e1 Do c).
Proof. by apply/funext=> m; apply/unrolls_while_w => {}m /= /andP[]. Qed.

(* -------------------------------------------------------------------- *)
(* Bridge to the exception-free language                                 *)
(*                                                                       *)
(* [noexc] is a structural predicate in the same family as [psemantic.v]'s*)
(* [noblock] and [nocall].  On exception-free programs the new semantics  *)
(* *is* the old one: [osem_] is the pushforward of [ssem_] along [ONorm]. *)
(* This is the regression test for the whole construction.               *)
(* -------------------------------------------------------------------- *)
Fixpoint noexc (c : cmd) : Prop :=
  match c with
  | abort | skip | assign _ _ _ | gassign _ _ _ | random _ _ _ | call _ => True
  | block _ c0 _ => noexc c0
  | cond _ c1 c2 => noexc c1 /\ noexc c2
  | while _ c0   => noexc c0
  | seqc c1 c2   => noexc c1 /\ noexc c2
  | raise _ _    => False
  | try_ _ _ _ _ => False
  end.

Definition onorm (o : outcome) : bool := if o is ONorm _ then true else false.

Definition onormal (mu : odistr) := forall o, o \in dinsupp mu -> onorm o.

Lemma onormal_dnull : onormal onull.
Proof. by move=> o /dinsuppP; rewrite dnullE. Qed.

Lemma onormal_dunit m : onormal (dunit (ONorm m)).
Proof. by move=> o /in_dunit ->. Qed.

Lemma onormal_dlet {T : choiceType} (mu : Distr T) (f : T -> odistr) :
  (forall v, onormal (f v)) -> onormal (\dlet_(v <- mu) f v).
Proof. by move=> h o /dinsupp_dlet[v _ ho]; exact: (h _ _ ho). Qed.

(* the shape needed for [block], [seqc] and [try_]: the continuation is
 * only ever reached on a normal outcome *)
Lemma onormal_dleto (mu : odistr) (g : outcome -> odistr) :
  onormal mu -> (forall m, onormal (g (ONorm m))) ->
  onormal (\dlet_(o <- mu) g o).
Proof.
move=> hmu hg o /dinsupp_dlet[o' ho' ho].
case: o' ho' ho => [m|m v] ho' ho; first exact: (hg _ _ ho).
by move: (hmu _ ho').
Qed.

Lemma onormal_dlim (F : nat -> odistr) :
  (forall n, onormal (F n)) -> onormal (\dlim_(n) F n).
Proof.
by move=> h o /dinsupp_dlim[K] /(_ _ (leqnn _)) ho; exact: (h _ _ ho).
Qed.

Lemma onormal_oubn (f : M -> odistr) (t : pred M) n m :
  (forall m0, onormal (f m0)) -> onormal (oubn f t n m).
Proof.
move=> hf; elim: n m => [|n ih] m /=; first exact: onormal_dnull.
case: ifP => _; last exact: onormal_dunit.
by apply: (onormal_dleto (hf m)) => m0; exact: ih.
Qed.

Lemma onormal_osem_aux (l : (Y * M) -> odistr) c :
  (forall a, onormal (l a)) -> noexc c ->
  forall m, onormal (osem_aux l c m).
Proof.
move=> hl; elim: c =>
  [||T x e|T gx ge|T x d|bs c0 ih rs|e c1 ih1 c2 ih2|e c0 ih|c1 ih1 c2 ih2|f
   |k e|c0 ih k x ch ihh] hc m /=.
- exact: onormal_dnull.
- exact: onormal_dunit.
- exact: onormal_dunit.
- exact: onormal_dunit.
- by apply: onormal_dlet => v; exact: onormal_dunit.
- by apply: (onormal_dleto (ih hc _)) => m0; exact: onormal_dunit.
- by case: hc => hc1 hc2; case: (esem e m); [exact: ih1 | exact: ih2].
- by apply: onormal_dlim => n; apply: onormal_oubn => m0; exact: ih hc m0.
- by case: hc => hc1 hc2;
     apply: (onormal_dleto (ih1 hc1 m)) => m0; exact: ih2 hc2 m0.
- exact: hl.
- by [].
- by [].
Qed.

Lemma onormal_oubnf ps n a :
  (forall f, noexc (ps f)) -> onormal (oubnf ps n a).
Proof.
move=> hps; elim: n a => [|n ih] [f m] /=; first exact: onormal_dnull.
exact: (onormal_osem_aux ih (hps f)).
Qed.

Lemma onormal_osem ps c m :
  (forall f, noexc (ps f)) -> noexc c -> onormal (osem_ ps c m).
Proof.
move=> hps hc.
have hL : forall a : Y * M, onormal ((fun l => dlim (fun n => oubnf ps n l)) a).
  by move=> a /=; apply: onormal_dlim => n; exact: onormal_oubnf.
by rewrite unlock /osem_r; apply: (onormal_osem_aux hL hc).
Qed.

Lemma dmargin_sproj (mu : odistr) :
  onormal mu -> dmargin ONorm (sproj mu) = mu.
Proof.
move=> hn; rewrite /sproj dmargin_dlet -[RHS]dlet_dunit_id.
apply/eq_in_dlet => // o ho.
case: o ho => [m0|m0 v] ho /=; first exact: dmargin_dunit.
by move: (hn _ ho).
Qed.

Lemma osem_noexc ps c m :
  (forall f, noexc (ps f)) -> noexc c ->
  osem_ ps c m = dmargin ONorm (ssem_ ps c m).
Proof.
by move=> hps hc; rewrite ssem_osemE (dmargin_sproj (@onormal_osem ps c m hps hc)).
Qed.

(* -------------------------------------------------------------------- *)
(* Sanity checks on the exception constructors                           *)
(* -------------------------------------------------------------------- *)

(* catching: the handler runs on the raise-point memory, with the payload
 * bound to [x] *)
Lemma osem_catchE ps k x (e : expr (interp (exnty k))) h m :
  osem_ ps (Try (Raise k With e) Catch k (x) h) m
    = osem_ ps h m.[x <- esem e m].
Proof.
rewrite osem_tryE osem_raiseE dlet_unit /=.
case: (k =P k) => [eq|/(_ erefl)//].
by rewrite (eq_irrelevance eq (erefl k)).
Qed.

(* a name that does not match is re-raised, memory and payload untouched *)
Lemma osem_reraiseE ps k k' x (e : expr (interp (exnty k'))) h m : k' != k ->
  osem_ ps (Try (Raise k' With e) Catch k (x) h) m
    = dunit (OExc m (existT _ k' (esem e m))).
Proof.
move=> ne; rewrite osem_tryE osem_raiseE dlet_unit /=.
by case: (k' =P k) => // eq; rewrite eq eqxx in ne.
Qed.

(* an exception escaping a block restores the caller's local store,
 * keeps the callee's globals, and skips the return bindings *)
Lemma osem_block_raiseE ps bs k (e : expr (interp (exnty k))) rs m :
  osem_ ps (Block bs Do (Raise k With e) Return rs) m
    = dunit (OExc (mrestore m (minit m bs))
                  (existT _ k (esem e (minit m bs)))).
Proof. by rewrite osem_blockE osem_raiseE dlet_unit. Qed.

(* -------------------------------------------------------------------- *)
(* [psemantic.v]'s [Section MISC] (993-1133).                            *)
(*                                                                       *)
(* These are stated at the exception-aware level: they talk about        *)
(* [osem_aux]/[oubnf], of which [psemantic.v]'s [ssem_aux]/[ubnf] are now *)
(* the projections.  The [ssem_] corollaries follow by [ssem_osemE].     *)
(* -------------------------------------------------------------------- *)
Lemma odlim_whilen n e c0 ps m :
  osem_aux (oubnf ps n) (While e Do c0) m =
    \dlim_(n0) osem_aux (oubnf ps n) (whilen e c0 n0) m.
Proof.
rewrite /=; apply: eq_dlim => n0.
move: m; elim: n0 => [|n0 ihn0] m //=.
case: (esem e m) => //=.
by apply: eq_in_dlet => // o _; apply: eq_obind; exact: ihn0.
Qed.

Lemma le_owhilen_aux (l : (Y * M) -> odistr) n e c m o :
  osem_aux l (whilen e c n) m o <= osem_aux l (whilen e c n.+1) m o.
Proof.
move: m o; elim: n => /= [|n ih] m o; first by rewrite dnullE ge0_mu.
case: (esem e m) => //; apply/le_in_dlet => // o' _.
by apply/le_obind => m'; exact: ih.
Qed.

Lemma hmono_owhilen (l : (Y * M) -> odistr) e c m n p : (n <= p)%N ->
  osem_aux l (whilen e c n) m <=1 osem_aux l (whilen e c p) m.
Proof.
elim: p n => [|p ih] n; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|]; rewrite ltnS => le_np o.
by apply/(le_trans (ih _ le_np o))/le_owhilen_aux.
Qed.

(* the call-depth approximation is exact in the limit *)
Lemma osem_dlim_oubnf ps c m :
  osem_ ps c m = \dlim_(n) osem_aux (oubnf ps n) c m.
Proof.
have mol : forall c0 n p, (n <= p)%N -> forall m0,
    osem_aux (oubnf ps n) c0 m0 <=1 osem_aux (oubnf ps p) c0 m0.
  by move=> c0 n p le m0; apply: mono_osem_aux => a; exact: homo_oubnf.
move: m; elim c.
1-5: by move=> * //=; rewrite /osem_ unlock /osem_r dlimC.
+ move=> bs c0 h rs m //=.
  rewrite osemE -dlet_dlim_diag //=.
  + by move=> n p le; exact: mol.
  + apply: eq_in_dlet; last by rewrite h.
    by move=> *; rewrite dlimC.
+ move=> e c1 hc1 c2 hc2 m //=.
  by rewrite osemE; case: (esem e m); [rewrite hc1 | rewrite hc2].
+ move=> e c0 h m.
  rewrite osemE.
  symmetry; under eq_dlim do rewrite odlim_whilen.
  have hcom : \dlim_(n) (\dlim_(n0) osem_aux (oubnf ps n) (whilen e c0 n0) m)
            = \dlim_(n0) (\dlim_(n) osem_aux (oubnf ps n) (whilen e c0 n0) m).
    apply: (dlim_dlim_com
      (h := fun n n0 => osem_aux (oubnf ps n) (whilen e c0 n0) m)).
    + by move=> k n1 n2 le; exact: mol.
    + by move=> k n1 n2 le; exact: hmono_owhilen.
  rewrite {}hcom.
  apply: eq_dlim => n; move: m.
  elim n.
  + by move=> ? //=; rewrite osemE dlimC.
  + move=> {}n hi m //=.
    rewrite osemE; case: (esem e m); last by rewrite osemE dlimC.
    rewrite osemE -dlet_dlim_diag //=.
    + by move=> n1 n2 le; exact: mol.
    + move=> [m0|m0 v] n1 n2 le /=; first exact: mol.
      by move=> ?; rewrite lexx.
    apply: eq_in_dlet; last by rewrite h.
    by move=> [m0|m0 v] _ /=; rewrite ?hi ?dlimC.
+ move=> c1 hc1 c2 hc2 m //=.
  rewrite osemE -dlet_dlim_diag //=.
  + by move=> n p le; exact: mol.
  + move=> [m0|m0 v] n p le /=; first exact: mol.
    by move=> ?; rewrite lexx.
  apply: eq_in_dlet; last by rewrite hc1.
  by move=> [m0|m0 v] _ /=; rewrite ?hc2 ?dlimC.
+ by move=> f m; rewrite osemE.
+ by move=> k e m //=; rewrite /osem_ unlock /osem_r dlimC.
+ move=> c0 hc k x h0 hh m //=.
  rewrite osemE -dlet_dlim_diag //=.
  + by move=> n p le; exact: mol.
  + move=> [m0|m0 [k' v]] n p le /=; first by move=> ?; rewrite lexx.
    by case: (k' =P k) => [eq|_]; [exact: mol | move=> ?; rewrite lexx].
  apply: eq_in_dlet; last by rewrite hc.
  move=> [m0|m0 [k' v]] _ /=; first by rewrite dlimC.
  by case: (k' =P k) => [eq|_]; rewrite ?hh ?dlimC.
Qed.

Lemma osem_call_eq ps f m : osem_ ps (call f) m = osem_ ps (ps f) m.
Proof.
rewrite [LHS]osemE [RHS]osem_dlim_oubnf.
transitivity (\dlim_(n) oubnf ps n.+1 (f, m)).
  by apply/distr_eqP => x; rewrite (dlim_bump (fun n => oubnf ps n (f, m))).
by apply: eq_dlim => n /=.
Qed.

Lemma ssem_call_eq ps f m : ssem_ ps (call f) m = ssem_ ps (ps f) m.
Proof. by rewrite !ssem_osemE osem_call_eq. Qed.

Lemma while_true_null m :
  (mnull : mdistr) = \dlim_(n) ubn [eta dunit (T:=M)] xpredT n m.
Proof.
rewrite -(dlimC mnull); apply: eq_dlim => n0.
elim: n0 => //= n1 h.
by rewrite dlet_unit h.
Qed.

Lemma owhile_true_null m :
  (onull : odistr) = \dlim_(n) oubn (fun m0 => dunit (ONorm m0)) xpredT n m.
Proof.
rewrite -(dlimC onull); apply: eq_dlim => n0.
elim: n0 => //= n1 h.
by rewrite dlet_unit /= h.
Qed.

Lemma osem_loop_while ps m : osem_ ps (While true%:S Do skip) m = onull.
Proof.
rewrite osemE //=.
rewrite (eq_dlim (gn := fun _ => onull)); last first. by rewrite dlimC.
move=> k /=.
elim: k => [|k ihk] //=; first by rewrite osemE.
by rewrite !osemE dlet_unit /= ihk.
Qed.

Lemma ssem_loop_while ps m : ssem_ ps (While true%:S Do skip) m = mnull.
Proof. by rewrite ssem_osemE osem_loop_while sproj_dnull. Qed.

(* -------------------------------------------------------------------- *)
Fixpoint noblock (c : cmd) : Prop :=
  match c with
  | abort | skip | assign _ _ _ | gassign _ _ _ | random _ _ _ | call _
  | raise _ _     => True
  | block _ _ _   => False
  | cond _ c1 c2  => noblock c1 /\ noblock c2
  | while _ c0    => noblock c0
  | seqc c1 c2    => noblock c1 /\ noblock c2
  | try_ c0 _ _ h => noblock c0 /\ noblock h
  end.

Fixpoint nocall (c : cmd) : Prop :=
  match c with
  | abort | skip | assign _ _ _ | gassign _ _ _ | random _ _ _
  | raise _ _     => True
  | block _ c0 _  => nocall c0
  | cond _ c1 c2  => nocall c1 /\ nocall c2
  | while _ c0    => nocall c0
  | seqc c1 c2    => nocall c1 /\ nocall c2
  | call _        => False
  | try_ c0 _ _ h => nocall c0 /\ nocall h
  end.

(* -------------------------------------------------------------------- *)
(* [psemantic.v]'s [Section Inliner] (1135-1503), at the exception-aware  *)
(* level.  [inliner] gains a [try_] case; [raise] is covered by the       *)
(* catch-all.                                                             *)
(* -------------------------------------------------------------------- *)
Fixpoint inliner (c : cmd) inline :=
  match c with
  | block bs p rs => block bs (inliner p inline) rs
  | cond b p1 p2  => cond b (inliner p1 inline) (inliner p2 inline)
  | while b p     => while b (inliner p inline)
  | seqc p1 p2    => seqc (inliner p1 inline) (inliner p2 inline)
  | call f        => inline f
  | try_ p k x h  => try_ (inliner p inline) k x (inliner h inline)
  | _ => c
  end.

Fixpoint k_inliner1 (n : nat) (c : cmd) (ps : Y -> cmd) :=
  match n with
  | 0 => while (cst_ true) skip
  | S n' => inliner c (fun f => k_inliner1 n' (ps f) ps)
  end.

Definition k_inliner_ps1 (n : nat) (ps : Y -> cmd) := fun p => k_inliner1 n (ps p) ps.

Fixpoint k_inliner2 (n : nat) (c : cmd) (ps : Y -> cmd) :=
  match n with
  | 0 => c
  | S n' => inliner c (fun f => k_inliner2 n' (ps f) ps)
  end.

Definition k_inliner_ps2 (n : nat) (ps : Y -> cmd) := fun p => k_inliner2 n (ps p) ps.

Definition false_ps : Y -> cmd := (fun _ => while (cst_ true) skip).

Lemma oubnf_dnull (n : nat) p m : (oubnf false_ps) n (p, m) = onull.
Proof.
case: n => [|n] //=.
rewrite (eq_dlim (gn := fun _ => onull)); last first. by rewrite dlimC.
move=> j /=.
elim: j => [|j ihj] //=.
by rewrite dlet_unit /= ihj.
Qed.

Lemma osem_false_ps p m : osem_ false_ps (call p) m = onull.
Proof.
rewrite osemE.
rewrite (eq_dlim (gn := fun _ => onull)); last first. by rewrite dlimC.
by move=> n; exact: oubnf_dnull.
Qed.

Lemma ssem_false_ps p m : ssem_ false_ps (call p) m = mnull.
Proof. by rewrite ssem_osemE osem_false_ps sproj_dnull. Qed.

Lemma kinliner1_cblock (n : nat) ps' bs p rs :
  k_inliner1 (S n) (@block R A B X Xg M exn exnty Y bs p rs) ps' =
  block bs (k_inliner1 (S n) p ps') rs.
Proof. reflexivity. Qed.

Lemma kinliner1_cif (n : nat) ps' b p1 p2 :
  k_inliner1 (S n) (cond b p1 p2) ps' =
  cond b (k_inliner1 (S n) p1 ps') (k_inliner1 (S n) p2 ps').
Proof. reflexivity. Qed.

Lemma kinliner1_cwhile (n : nat) ps' p b :
  k_inliner1 (S n) (while b p) ps' = while b (k_inliner1 (S n) p ps').
Proof. reflexivity. Qed.

Lemma kinliner1_cseq (n : nat) ps' p1 p2 :
  k_inliner1 (S n) (seqc p1 p2) ps' =
  seqc (k_inliner1 (S n) p1 ps') (k_inliner1 (S n) p2 ps').
Proof. reflexivity. Qed.

Lemma kinliner1_ccall (n : nat) f ps' :
  k_inliner1 (S n) (call f) ps' = k_inliner1 n (ps' f) ps'.
Proof. reflexivity. Qed.

Lemma kinliner1_ctry (n : nat) ps' p k x h :
  k_inliner1 (S n) (try_ p k x h) ps' =
  try_ (k_inliner1 (S n) p ps') k x (k_inliner1 (S n) h ps').
Proof. reflexivity. Qed.

Lemma kinliner2_cblock (n : nat) ps' bs p rs :
  k_inliner2 (S n) (@block R A B X Xg M exn exnty Y bs p rs) ps' =
  block bs (k_inliner2 (S n) p ps') rs.
Proof. reflexivity. Qed.

Lemma kinliner2_cif (n : nat) ps' b p1 p2 :
  k_inliner2 (S n) (cond b p1 p2) ps' =
  cond b (k_inliner2 (S n) p1 ps') (k_inliner2 (S n) p2 ps').
Proof. reflexivity. Qed.

Lemma kinliner2_cwhile (n : nat) ps' p b :
  k_inliner2 (S n) (while b p) ps' = while b (k_inliner2 (S n) p ps').
Proof. reflexivity. Qed.

Lemma kinliner2_cseq (n : nat) ps' p1 p2 :
  k_inliner2 (S n) (seqc p1 p2) ps' =
  seqc (k_inliner2 (S n) p1 ps') (k_inliner2 (S n) p2 ps').
Proof. reflexivity. Qed.

Lemma kinliner2_ccall (n : nat) f ps' :
  k_inliner2 (S n) (call f) ps' = k_inliner2 n (ps' f) ps'.
Proof. reflexivity. Qed.

Lemma kinliner2_ctry (n : nat) ps' p k x h :
  k_inliner2 (S n) (try_ p k x h) ps' =
  try_ (k_inliner2 (S n) p ps') k x (k_inliner2 (S n) h ps').
Proof. reflexivity. Qed.

Lemma inline12_split (n p : nat) (ps1 : Y -> cmd) c :
  k_inliner1 (S n) (k_inliner2 p c ps1) ps1 = k_inliner1 ((S n) + p) c ps1.
Proof.
move: n c ps1; elim p.
+ by move=> n c ps1 //=; rewrite addn0.
+ move=> {}p h n c ps1.
  elim c.
  1-5 : move=> //=.
  + move=> ? ? hc ?.
    rewrite kinliner2_cblock kinliner1_cblock hc.
    by rewrite (kinliner1_cblock (n + p.+1)).
  + move=> e ? hc1 ? hc2.
    rewrite kinliner2_cif kinliner1_cif hc1 hc2.
    by rewrite (kinliner1_cif (n + p.+1)).
  + move=> e ? hc1.
    rewrite kinliner2_cwhile kinliner1_cwhile hc1.
    by rewrite (kinliner1_cwhile (n + p.+1)).
  + move=> ? hc1 ? hc2.
    rewrite kinliner2_cseq kinliner1_cseq hc1 hc2.
    by rewrite (kinliner1_cseq (n + p.+1)).
  + move=> s.
    rewrite kinliner2_ccall h (kinliner1_ccall (n + p.+1)).
    by rewrite addSnnS.
  + by move=> ?? //=.
  + move=> c0 hc k x h0 hh.
    rewrite kinliner2_ctry kinliner1_ctry hc hh.
    by rewrite (kinliner1_ctry (n + p.+1)).
Qed.

Lemma osem_oubnf_dnull (ps' : Y -> cmd) c (n : nat) m :
  osem_aux (oubnf ps' n) c m =
    osem_aux (fun _ => onull) (k_inliner2 n c ps') m.
Proof.
move: c m; elim n => [//=|n0 h c].
elim c.
1-5: by move=> * //=.
+ by move=> ? ? hc ? m //=; apply: eq_in_dlet.
+ by move=> e ? hc1 ? hc2 m //=; case: (esem e m); [rewrite hc1 | rewrite hc2].
+ move=> e c0 //= hi m.
  apply: eq_dlim => j.
  move: m; elim j => //= j2 hjj m.
  case: (esem e m) => //=.
  apply: eq_in_dlet.
  + by move=> o _; apply: eq_obind => m'; exact: hjj.
  + by rewrite hi.
+ move=> ? hc1 ? hc2 m //=.
  apply: eq_in_dlet.
  + by move=> o _; apply: eq_obind => m'; exact: hc2.
  + by rewrite hc1.
+ by move=> f m //=.
+ by move=> ?? m //=.
+ move=> c0 hc k x h0 hh m //=.
  apply: eq_in_dlet.
  + by move=> o _; apply: eq_ocatch => m'; exact: hh.
  + by rewrite hc.
Qed.

Lemma oubnf_osem c m :
  osem_aux (fun _ => onull) c m = osem_ false_ps c m.
Proof.
move: m; elim c.
1-5: by move=> * //=; rewrite !osemE.
+ by move=> ? ? hc ? m //=; rewrite osemE; apply: eq_in_dlet.
+ move=> e ? hc1 ? hc2 m //=.
  by rewrite osemE; case: (esem e m); [rewrite hc1 | rewrite hc2].
+ move=> e c0 //= hi m.
  rewrite osemE; apply: eq_dlim => j.
  move: m; elim j => //=.
  + by move=> m; rewrite osemE.
  move=> j2 hjj m; rewrite osemE.
  case: (esem e m) => //=.
  rewrite osemE.
  apply: eq_in_dlet.
  + by move=> o _; apply: eq_obind => m'; exact: hjj.
  + by rewrite hi.
  by rewrite osemE.
+ move=> ? hc1 ? hc2 m //=.
  rewrite osemE.
  apply: eq_in_dlet.
  + by move=> o _; apply: eq_obind => m'; exact: hc2.
  + by rewrite hc1.
+ move=> f m /=.
  rewrite osemE -(dlimC onull); apply: eq_dlim => n0.
  by rewrite oubnf_dnull.
+ by move=> ?? m //=; rewrite !osemE.
+ move=> c0 hc k x h0 hh m //=.
  rewrite osemE.
  apply: eq_in_dlet.
  + by move=> o _; apply: eq_ocatch => m'; exact: hh.
  + by rewrite hc.
Qed.

Lemma inliner_false_ps_osem (ps' : Y -> cmd) c (n : nat) m :
  forall ps0,
    osem_ false_ps (k_inliner2 n c ps') m =
    osem_ ps0 (k_inliner1 (S n) c ps') m.
Proof.
move=> ps0; move: c m.
elim: n => [|n ih] c m.
- move: m; elim: c.
  1-5: by move=> * /=; rewrite !osemE.
  + by move=> ? ? hc ? m /=; rewrite !osemE; apply: eq_in_dlet.
  + move=> e c1 hc1 c2 hc2 m /=.
    by rewrite !osemE; case: (esem e m); [exact: hc1 | exact: hc2].
  + move=> e c0 hc m /=.
    rewrite [LHS]osem_while_ubn [RHS]osem_while_ubn.
    apply: eq_dlim => j.
    move: m; elim: j => [|j ihj] m //=.
    case: (esem e m) => //.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: ihj | exact: hc].
  + move=> c1 hc1 c2 hc2 m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: hc2 | exact: hc1].
  + by move=> f m /=; rewrite osem_false_ps osem_loop_while.
  + by move=> ?? m /=; rewrite !osemE.
  + move=> c0 hc k x h0 hh m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_ocatch => m'; exact: hh | exact: hc].
- move: m; elim: c.
  1-5: by move=> * /=; rewrite !osemE.
  + by move=> ? ? hc ? m /=; rewrite !osemE; apply: eq_in_dlet.
  + move=> e c1 hc1 c2 hc2 m /=.
    by rewrite !osemE; case: (esem e m); [exact: hc1 | exact: hc2].
  + move=> e c0 hc m /=.
    rewrite [LHS]osem_while_ubn [RHS]osem_while_ubn.
    apply: eq_dlim => j.
    move: m; elim: j => [|j ihj] m //=.
    case: (esem e m) => //.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: ihj | exact: hc].
  + move=> c1 hc1 c2 hc2 m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: hc2 | exact: hc1].
  + by move=> f m /=; exact: ih.
  + by move=> ?? m /=; rewrite !osemE.
  + move=> c0 hc k x h0 hh m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_ocatch => m'; exact: hh | exact: hc].
Qed.

Lemma inliner_inliner_ps_osem (ps1 ps2 : Y -> cmd) c m (n : nat) :
  osem_ ps2 (k_inliner1 (S n) c ps1) m = osem_ (k_inliner_ps1 n ps1) c m.
Proof.
move: ps2 c m; elim: n => [|n ih] ps2 c m.
- move: m; elim: c.
  1-5: by move=> * /=; rewrite !osemE.
  + by move=> ? ? hc ? m /=; rewrite !osemE; apply: eq_in_dlet.
  + move=> e c1 hc1 c2 hc2 m /=.
    by rewrite !osemE; case: (esem e m); [exact: hc1 | exact: hc2].
  + move=> e c0 hc m /=.
    rewrite [LHS]osem_while_ubn [RHS]osem_while_ubn.
    apply: eq_dlim => j.
    move: m; elim: j => [|j ihj] m //=.
    case: (esem e m) => //.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: ihj | exact: hc].
  + move=> c1 hc1 c2 hc2 m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: hc2 | exact: hc1].
  + by move=> f m /=; rewrite osem_loop_while osem_false_ps.
  + by move=> ?? m /=; rewrite !osemE.
  + move=> c0 hc k x h0 hh m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_ocatch => m'; exact: hh | exact: hc].
- move: m; elim: c.
  1-5: by move=> * /=; rewrite !osemE.
  + by move=> ? ? hc ? m /=; rewrite !osemE; apply: eq_in_dlet.
  + move=> e c1 hc1 c2 hc2 m /=.
    by rewrite !osemE; case: (esem e m); [exact: hc1 | exact: hc2].
  + move=> e c0 hc m /=.
    rewrite [LHS]osem_while_ubn [RHS]osem_while_ubn.
    apply: eq_dlim => j.
    move: m; elim: j => [|j ihj] m //=.
    case: (esem e m) => //.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: ihj | exact: hc].
  + move=> c1 hc1 c2 hc2 m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_obind => m'; exact: hc2 | exact: hc1].
  + move=> f m /=.
    rewrite ih; symmetry; rewrite osem_call_eq /=.
    by rewrite ih.
  + by move=> ?? m /=; rewrite !osemE.
  + move=> c0 hc k x h0 hh m /=.
    rewrite !osemE.
    by apply: eq_in_dlet;
      [move=> o _; apply: eq_ocatch => m'; exact: hh | exact: hc].
Qed.

Lemma inline2_split (n p : nat) (ps1 : Y -> cmd) c m :
  osem_ (k_inliner_ps1 (p + n) ps1) c m =
  osem_ (k_inliner_ps1 n ps1) (k_inliner2 p c ps1) m.
Proof.
move: c m; elim: p => [|p ih] c m; first by [].
move: m; elim: c.
1-5: by move=> * /=; rewrite !osemE.
+ by move=> ? ? hc ? m /=; rewrite !osemE; apply: eq_in_dlet.
+ move=> e c1 hc1 c2 hc2 m /=.
  by rewrite !osemE; case: (esem e m); [exact: hc1 | exact: hc2].
+ move=> e c0 hc m /=.
  rewrite [LHS]osem_while_ubn [RHS]osem_while_ubn.
  apply: eq_dlim => j.
  move: m; elim: j => [|j ihj] m //=.
  case: (esem e m) => //.
  by apply: eq_in_dlet;
    [move=> o _; apply: eq_obind => m'; exact: ihj | exact: hc].
+ move=> c1 hc1 c2 hc2 m /=.
  rewrite !osemE.
  by apply: eq_in_dlet;
    [move=> o _; apply: eq_obind => m'; exact: hc2 | exact: hc1].
+ move=> f m /=.
  rewrite -ih osem_call_eq /= addSn.
  by rewrite inliner_inliner_ps_osem.
+ by move=> ?? m /=; rewrite !osemE.
+ move=> c0 hc k x h0 hh m /=.
  rewrite !osemE.
  by apply: eq_in_dlet;
    [move=> o _; apply: eq_ocatch => m'; exact: hh | exact: hc].
Qed.

Lemma osem_aux_osem_ ps (n : nat) c m :
  osem_aux (oubnf ps n) c m = osem_ (k_inliner_ps1 n ps) c m.
Proof.
by rewrite osem_oubnf_dnull oubnf_osem
     (inliner_false_ps_osem _ _ _ _ ps) inliner_inliner_ps_osem.
Qed.

Lemma dlim_inliner_osem (ps' : Y -> cmd) c m :
  \dlim_(n) osem_ (k_inliner_ps1 n ps') c m = osem_ ps' c m.
Proof.
rewrite [RHS]osem_dlim_oubnf; apply: eq_dlim => n.
by rewrite osem_aux_osem_.
Qed.

Lemma dlim_inliner_ssem (ps' : Y -> cmd) c m :
  \dlim_(n) ssem_ (k_inliner_ps1 n ps') c m = ssem_ ps' c m.
Proof.
rewrite ssem_osemE -dlim_inliner_osem.
rewrite (sproj_dlim (F := fun n => osem_ (k_inliner_ps1 n ps') c m)).
+ move=> n q le; rewrite -!osem_aux_osem_.
  by apply: mono_osem_aux => a; exact: homo_oubnf.
by apply: eq_dlim => n; rewrite ssem_osemE.
Qed.

(* -------------------------------------------------------------------- *)
(* [ubnf] is defined as a projection, so it has no fixpoint equation of   *)
(* its own.  These two give the approximation proofs of [hl2.v]/[ehl2.v]  *)
(* the handle they used to get from [ubnf]'s [Fixpoint].                  *)
(* -------------------------------------------------------------------- *)
Lemma ubnf0 ps a : ubnf ps 0 a = mnull.
Proof. by rewrite /ubnf /= sproj_dnull. Qed.

Lemma ubnfS ps (n : nat) a :
  ubnf ps n.+1 a = ssem_ (k_inliner_ps1 n ps) (ps a.1) a.2.
Proof. by rewrite /ubnf /= osem_aux_osem_ -ssem_osemE. Qed.

End Semantics.

(* -------------------------------------------------------------------- *)
Arguments esem A B X Xg M T e%_X m%_M.
Arguments exnv : clear implicits.
Arguments outcome : clear implicits.
Arguments osem_ {_ _ _ _ _ _ _ _ _} ps s%_S m%_M.
Arguments ssem_ {_ _ _ _ _ _ _ _ _} ps s%_S m%_M.
(* section discharge puts [k] back among the implicits; it is not
 * inferable from [x : vars (exnty k)], so make it explicit again *)
Arguments ocatch {_ _ _ _ _ _ _ _} k x h o.

Notation "e `_ m" := (@esem _ _ _ _ _ _ e%X m%M) : sem_scope.
Notation "`[{ e }]" := (@esem _ _ _ _ _ _ e%X) (at level 2, format "`[{ e }]").

(* -------------------------------------------------------------------- *)
(* Program equivalence (ported from [psemantic.v:541-678])               *)
(*                                                                       *)
(* There are now *two* notions, and the split is forced by the feature:   *)
(*                                                                       *)
(*  [c1 =O c2]  agreement on [osem_] -- exception-aware, the real notion; *)
(*  [c1 =C c2]  agreement on [ssem_] -- [psemantic.v]'s [eqcmd], implied  *)
(*              by [=O] ([oeqcmd_eqcmd]).                                 *)
(*                                                                       *)
(* [=C] is too weak for [normcP]: the projected semantics of [try_] is    *)
(* not determined by the projections of its sub-commands, so there is no  *)
(* [=C]-congruence for [try_] at all (hence no [Proper] instance for it   *)
(* below).  [=O] is too strong for [whilen_iterc]: [c ;; abort] keeps the *)
(* exceptional mass of [c] while [abort] has none, so that law only holds *)
(* after projection.  Both are therefore kept.                            *)
(* -------------------------------------------------------------------- *)
Section EqCmd.
Context {R : realType} {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg}
        {exn : eqType} {exnty : exn -> A}
        {ps : Y -> (@cmd_ R A B X Xg M exn exnty Y)}.
Local Notation Distr T := {distr T%type / R}.
Local Notation cmd := (cmd_ R A B X Xg M exn exnty Y).

Definition oeqcmd (c1 c2 : cmd) := forall m, osem_ ps c1 m = osem_ ps c2 m.

Definition eqcmd (c1 c2 : cmd) := forall m, ssem_ ps c1 m = ssem_ ps c2 m.

Global Instance oeqcmd_R : Equivalence oeqcmd.
Proof.
constructor=> //.
+ by move=> f1 f2 eq s; rewrite eq.
+ by move=> f1 f2 f3 eq1 eq2 s; rewrite eq1.
Qed.

Global Instance eqcmd_R : Equivalence eqcmd.
Proof.
constructor=> //.
+ by move=> f1 f2 eq s; rewrite eq.
+ by move=> f1 f2 f3 eq1 eq2 s; rewrite eq1.
Qed.

Notation "c1 '=O' c2" := (oeqcmd c1 c2) (at level 70, no associativity).
Notation "c1 '=C' c2" := (eqcmd c1 c2) (at level 70, no associativity).

Notation CLHS := (X in X =C _)%pattern.
Notation CRHS := (X in _ =C X)%pattern.

Lemma oeqcmd_eqcmd c1 c2 : c1 =O c2 -> c1 =C c2.
Proof. by move=> h m; rewrite !ssem_osemE h. Qed.

(* -------------------------------------------------------------------- *)
(* Congruences for [=O].  [try_] gets a plain lemma rather than a         *)
(* [Proper] instance: its type is dependent ([x : vars (exnty k)]), which *)
(* [respectful] cannot express.                                           *)
(* -------------------------------------------------------------------- *)
Lemma seq_mo c1 c1' c2 c2' : c1 =O c1' -> c2 =O c2' -> (c1 ;; c2) =O (c1' ;; c2').
Proof.
move=> h1 h2 m; rewrite !osem_seqE h1.
by apply: eq_in_dlet => // o _; apply: eq_obind; exact: h2.
Qed.

Lemma cond_mo e c1 c1' c2 c2' :
  c1 =O c1' -> c2 =O c2' -> (If e then c1 else c2) =O (If e then c1' else c2').
Proof. by move=> h1 h2 m; rewrite !osem_ifE; case: ifP. Qed.

Lemma while_mo e c c' : c =O c' -> (While e Do c) =O (While e Do c').
Proof.
move=> h m; rewrite !osem_while_ubn; apply/eq_dlim => n.
elim: n m => //= n ih m; case: (esem e m) => //.
by apply: eq_in_dlet; [move=> o _; apply: eq_obind; exact: ih | exact: h].
Qed.

Lemma block_mo bs c c' rs : c =O c' -> block bs c rs =O block bs c' rs.
Proof. by move=> h m; rewrite !osem_blockE h. Qed.

Lemma try_mo c c' k x h h' :
  c =O c' -> h =O h' -> (try_ c k x h) =O (try_ c' k x h').
Proof.
move=> hc hh m; rewrite !osem_tryE hc.
by apply: eq_in_dlet => // o _; apply: eq_ocatch; exact: hh.
Qed.

Global Instance oseq_m : Proper (oeqcmd ==> oeqcmd ==> oeqcmd) seqc.
Proof. by move=> ?? h1 ?? h2; apply: seq_mo. Qed.

Global Instance owhile_m : Proper (eq ==> oeqcmd ==> oeqcmd) while.
Proof. by move=> ?? <- ?? h; apply: while_mo. Qed.

Global Instance ocond_m : Proper (eq ==> oeqcmd ==> oeqcmd ==> oeqcmd) cond.
Proof. by move=> ?? <- ?? h1 ?? h2; apply: cond_mo. Qed.

Global Instance oblock_m :
  Proper (eq ==> oeqcmd ==> eq ==> oeqcmd) (@block R A B X Xg M exn exnty Y).
Proof. by move=> ?? <- ?? h ?? <-; apply: block_mo. Qed.

(* -------------------------------------------------------------------- *)
(* The monoid laws, all of which do hold exception-aware                 *)
(* -------------------------------------------------------------------- *)
Lemma oseq_skip_l (c : cmd) : (skip ;; c) =O c.
Proof. by move=> m; rewrite osem_seqE osem_skipE dlet_unit. Qed.

Lemma oseq_skip_r (c : cmd) : (c ;; skip) =O c.
Proof.
move=> m; rewrite osem_seqE -[X in _ = X]dlet_dunit_id.
by apply: eq_in_dlet => // -[m'|m' v] _ /=; rewrite ?osem_skipE.
Qed.

Lemma oseqA (c1 c2 c3 : cmd) : (c1 ;; (c2 ;; c3)) =O (c1 ;; c2 ;; c3).
Proof.
move=> m; rewrite !osem_seqE dlet_dlet.
apply: eq_in_dlet => // -[m'|m' v] _ /=; first by rewrite osem_seqE.
by rewrite dlet_unit.
Qed.

Lemma seq_skip_l (c : cmd) : (skip ;; c) =C c.
Proof. exact/oeqcmd_eqcmd/oseq_skip_l. Qed.

Lemma seq_skip_r (c : cmd) : (c ;; skip) =C c.
Proof. exact/oeqcmd_eqcmd/oseq_skip_r. Qed.

Lemma seqA (c1 c2 c3 : cmd) : (c1 ;; (c2 ;; c3)) =C (c1 ;; c2 ;; c3).
Proof. exact/oeqcmd_eqcmd/oseqA. Qed.

Lemma iter_seq_out n c c1 c2 :
  iter n (seqc c) (c1 ;; c2) =O (iter n (seqc c) c1 ;; c2).
Proof.
elim: n => //= n ih m; rewrite -oseqA !osem_seqE.
by apply: eq_in_dlet => // o _; apply: eq_obind; exact: ih.
Qed.

Lemma iter_seq_swap n c : iter n (seqc^~ c) c =O iter n (seqc c) c.
Proof.
elim: n => // n ih m; rewrite [in RHS]iterSr.
rewrite iter_seq_out !osem_seqE.
by apply: eq_in_dlet => // o _; apply: eq_obind; exact: ih.
Qed.

Lemma itercSl n c : iterc n.+1 c =O (c ;; iterc n c).
Proof. by move=> m; case: n => [|n] //=; rewrite oseq_skip_r. Qed.

Lemma itercSr n c : iterc n.+1 c =O (iterc n c ;; c).
Proof.
case: n => [|n]; first by rewrite iterc0 itercS /= => m; rewrite oseq_skip_l.
rewrite !itercS; transitivity (iter n (seqc^~ c) c ;; c).
  by symmetry; exact: (iter_seq_swap n.+1 c).
by apply: seq_mo; [exact: iter_seq_swap|].
Qed.

Global Instance seq_m : Proper (eqcmd ==> eqcmd ==> eqcmd) seqc.
Proof. by move=> ?? H1 ?? H2 m; rewrite !semE; apply: eq_in_dlet. Qed.

Global Instance while_m : Proper (eq ==> eqcmd ==> eqcmd) while.
Proof.
move=> ?? H1 ?? H2 m; rewrite !ssem_while_ubn H1; apply/eq_dlim=> n.
by elim: n m => //= n ih m; case: ifP => // _; apply: eq_in_dlet.
Qed.

Global Instance cond_m : Proper (eq ==> eqcmd ==> eqcmd ==> eqcmd) cond.
Proof. by move=> ?? H1 ?? H2 ?? H3 m; rewrite !semE H1; case: ifP. Qed.

Global Instance block_m :
  Proper (eq ==> eqcmd ==> eq ==> eqcmd) (@block R A B X Xg M exn exnty Y).
Proof. by move=> ?? <- c1 c2 hc ?? <- m; rewrite !ssem_blockE hc. Qed.

(* -------------------------------------------------------------------- *)
(* The sequence normaliser                                               *)
(* -------------------------------------------------------------------- *)
Fixpoint mk_seqr (c1 c2 : cmd) :=
  match c2 with
  | skip        => c1
  | seqc c2 c2' => mk_seqr (mk_seqr c1 c2) c2'
  | _           => seqc c1 c2
  end.

Definition mk_seq (c1 c2 : cmd) :=
  if c1 is skip then c2 else mk_seqr c1 c2.

Fixpoint normc (c : cmd) :=
  match c with
  | abort | skip | assign _ _ _ | gassign _ _ _
  | random _ _ _ | call _ | raise _ _ => c
  | block bs c rs => block bs (normc c) rs
  | cond e c1 c2  => cond e (normc c1) (normc c2)
  | while e c     => while e (normc c)
  | seqc c1 c2    => mk_seq (normc c1) (normc c2)
  | try_ c0 k x h => try_ (normc c0) k x (normc h)
  end.

Lemma mk_seqrP (c1 c2 : cmd) : mk_seqr c1 c2 =O seqc c1 c2.
Proof.
elim: c2 c1 => //= [|c2 H1 c3 H2] c1; first by rewrite oseq_skip_r.
by rewrite oseqA H2 H1.
Qed.

Lemma mk_seqP (c1 c2 : cmd) : mk_seq c1 c2 =O seqc c1 c2.
Proof. by case: c1 => //= *; rewrite ?mk_seqrP // oseq_skip_l. Qed.

Lemma normcP (c : cmd) : c =O normc c.
Proof.
elim: c => //=.
- by move=> bs c0 ih rs; apply: block_mo.
- by move=> e c1 ih1 c2 ih2; apply: cond_mo.
- by move=> e c0 ih; apply: while_mo.
- by move=> c1 ih1 c2 ih2; rewrite mk_seqP; apply: seq_mo.
- by move=> c0 ih k x h ihh; apply: try_mo.
Qed.

Lemma normcPC (c : cmd) : c =C normc c.
Proof. exact/oeqcmd_eqcmd/normcP. Qed.

(* -------------------------------------------------------------------- *)
Lemma ssem_iterop_iter n c : iterc n c =O iter n (seqc c) skip.
Proof.
case: n => // n; rewrite itercS /=; elim: n => [|n ih] /=.
  by rewrite oseq_skip_r. by rewrite ih.
Qed.

Lemma ssem_iterop_iterrev n c : iterc n c =O iter n (seqc^~ c) skip.
Proof.
rewrite ssem_iterop_iter; elim: n => // n ih.
rewrite iterSr iterS -{}ih; elim: n => /= [|n ih].
- by rewrite oseq_skip_l oseq_skip_r.
- by rewrite ih oseqA.
Qed.

(* This one is *not* exception-aware: [c ;; abort] keeps the exceptional
 * mass of [c], [abort] has none.  It holds only after projection. *)
Lemma whilen_iterc n b c :
  whilen b c n.+1 =C (iterc n (IfT b then c) ;; (IfT b then abort)).
Proof.
rewrite (oeqcmd_eqcmd (ssem_iterop_iter _ _)); elim: n => [|n ihn] /=.
  rewrite seq_skip_l => m; rewrite !semE; case: ifP=> // _.
  by rewrite bsemE; apply/distr_eqP=> m'; rewrite dletC dnullE mulr0.
rewrite -seqA -ihn /= => m; rewrite !semE; case: ifP => // bm.
by rewrite dlet_unit !semE bm.
Qed.

End EqCmd.

Arguments oeqcmd {_ _ _ _ _ _ _ _ _} _.
Arguments eqcmd  {_ _ _ _ _ _ _ _ _} _.

Notation "c1 '=O' c2 ';' ps" := (oeqcmd ps c1 c2) (at level 70, no associativity).
Notation "c1 '=C' c2 ';' ps" := (eqcmd ps c1 c2) (at level 70, no associativity).

(* -------------------------------------------------------------------- *)
Reserved Notation "m .[ x @ s <- v ]"
  (at level 1, x, s, v at level 200, format "m .[ x @ s  <-  v ]").

Reserved Notation "m .[~1 x <- v ]"
  (at level 1, x, v at level 200, format "m .[~1  x  <-  v ]").

Reserved Notation "m .[~2 x <- v ]"
  (at level 1, x, v at level 200, format "m .[~2  x  <-  v ]").

Notation "m .[ x @ s <- v ]" := m.[x # s <- v].
Notation "m .[~1 x <- v ]"   := m.[x @ '1 <- v].
Notation "m .[~2 x <- v ]"   := m.[x @ '2 <- v].

(* -------------------------------------------------------------------- *)
(* Ported from [psemantic.v:705-825].  All of these are at the projected  *)
(* level and go through unchanged.                                        *)
(* -------------------------------------------------------------------- *)
Section DSemantics.
Context {R : realType} {A B : codeType} {X Xg Y : eqType}
        {M : memType A B X Xg} {exn : eqType} {exnty : exn -> A}.

Local Notation Distr T := {distr T%type / R}.
Local Notation vars  := (vars_ X).
Local Notation gvars := (vars_ Xg).
Local Notation expr  := (@expr_ A B X Xg M).
Local Notation assn  := (pred M).
Local Notation dassn := (pred (Distr M)).
Local Notation cmd   := (cmd_ R A B X Xg M exn exnty Y).
Local Notation psi   := (Y -> cmd).
Local Notation ssem  := (@ssem_ R A B X Xg Y M exn exnty).

Local Notation mdistr := (Distr M).
Local Notation mnull  := (@dnull R M).

(* -------------------------------------------------------------------- *)
Lemma unrolln_while n (e : expr bool) c (ps : psi) :
  (While e Do c) =C (iterc n (IfT e then c) ;; While e Do c) ; ps.
Proof.
rewrite (oeqcmd_eqcmd (ssem_iterop_iter _ _)); elim: n => [|n ih] /=.
  by rewrite seq_skip_l.
by rewrite -seqA -ih => m; rewrite unroll_while.
Qed.

(* -------------------------------------------------------------------- *)
Lemma if_same (e : expr bool) c (ps : psi) :
  If e then c else c =C c ; ps.
Proof. by move=> m; rewrite !semE; case: (esem _ _). Qed.

(* -------------------------------------------------------------------- *)
Lemma if_seq (e : expr bool) c c1 c2 (ps : psi) :
  (If e then c1 else c2 ;; c) =C If e then (c1 ;; c) else (c2 ;; c) ; ps.
Proof. by move=> m; rewrite !semE; case: ifPn. Qed.

(* -------------------------------------------------------------------- *)
Lemma le_while (e : expr bool) c1 c2 m (ps : psi) :
     (forall m, esem e m -> ssem_ ps c1 m <=1 ssem_ ps c2 m)
  -> ssem_ ps (While e Do c1) m <=1 ssem_ ps (While e Do c2) m.
Proof.
move=> lec m'; rewrite !semE; apply/le_dlim => n.
elim: n m => //= n ihn m {}m'; rewrite !semE.
by case: ifP => // hem; apply/le_dlet => {} m' //; apply: lec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xsplit_while (e e1 e2 : expr bool) c (ps : psi) :
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
  by rewrite (unrolls_while_w _ _ _ h1) !ssem_seqE le_dlet.
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
  by apply: (le_trans (le_whilen _ _ _ _ _ _)) => /=.
rewrite seq_skip_l unroll_while_in ssem_ifE hem.
rewrite 2![in X in _ <= X]semE; case: ifPn => [he1m|]; last first.
  by move/(h2 _ hem); rewrite (negbTE he2m).
rewrite ssem_seqE le_dlet => // {m' hem he1m he2m} m _ m'.
by apply: (le_trans (le_whilen _ _ _ _ _ _)).
Qed.

(* -------------------------------------------------------------------- *)
Definition dssem (ps : psi) (c : cmd) (mu : mdistr) :=
  (\dlet_(m <- mu) (ssem ps c m)).

Global Instance dsem_m ps :
  Proper (@eqcmd _ _ _ _ _ _ _ _ _ ps ==> eq ==> eq) (dssem ps).
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

(* An uncaught exception is indistinguishable from [abort] here too. *)
Lemma dssem_raiseE ps k (e : expr (interp (exnty k))) mu :
  dssem ps (raise k e) mu = mnull.
Proof.
by apply/distr_eqP=> m; rewrite /dssem bsemE dletC dnullE mulr0.
Qed.

(* -------------------------------------------------------------------- *)
Definition lossless (P : assn) (c : cmd) :=
  forall ps m, m \in P -> dweight (ssem ps c m) = 1.

Definition dlossless (P : dassn) (c : cmd) :=
  forall ps mu, mu \in P -> dweight (dssem ps c mu) = 1.

End DSemantics.

(* -------------------------------------------------------------------- *)
(* Ported from [psemantic.v:827-918]                                     *)
(* -------------------------------------------------------------------- *)
Section RSemantics.
Context {R : realType} {A B : codeType} {X Xg Y : eqType}
        {M : memType A B X Xg} {exn : eqType} {exnty : exn -> A}.

Local Notation Distr T := {distr T%type / R}.

Local Notation rmem := (rmem A B X Xg M).
Local Notation vars  := (vars_ X).
Local Notation gvars := (vars_ Xg).
Local Notation expr  := (@expr_ A B X Xg M).

Lemma mselect_mset T s s' (m : rmem) (x : vars T) (v : T) :
  m.[x @ s <- v] # s' = if s == s' then (m#s).[x <- v] else m#s'.
Proof. by case: s s' x => [] [] []. Qed.

Lemma esem_iE T s (e : expr T) (m : rmem) : esem (e#s) m = esem e m#s.
Proof. by elim: e => {T} /= [ ?[?]| | | ??? -> ? ->| ?[?]]. Qed.

Lemma esem_1E T (e : expr T) (m : rmem) : esem (e#'1) m = esem e m.1.
Proof. by rewrite esem_iE. Qed.

Lemma esem_2E T (e : expr T) (m : rmem) : esem (e#'2) m = esem e m.2.
Proof. by rewrite esem_iE. Qed.

Definition esemE := (@esem_appE, @esem_cstE, esem_1E, esem_2E).

Definition ssemE := (esemE, @semE).

Definition osemEr := (esemE, @osemE).

Lemma mget_iE {T : A} (m : rmem) (x : vars T) s :
  m.[irvar s x] = (m#s).[x].
Proof. by case: s x => -[]. Qed.

Lemma mset_iE {T : A} (m : rmem) (x : vars T) (v : T) s :
  m.[x#s <- v] =
  (((m#'1).[x <- v], m.1)#s, (m.2, (m#'2).[x <- v])#s)%M.
Proof. by case: x m s => xid [m1 m2] []. Qed.

Lemma mgetg_iE {T : B} (m : rmem) (x : gvars T) s :
  m.{girvar s x} = (m#s).{x}.
Proof. by case: s x => -[]. Qed.

Lemma msetg_iE {T : B} (m : rmem) (x : gvars T) (v : T) s :
  m.{x#g s <- v} =
  (((m#'1).{x <- v}, m.1)#s, (m.2, (m#'2).{x <- v})#s)%M.
Proof. by case: x m s => xid [m1 m2] []. Qed.

Lemma mnew_iE (m : rmem) : m.[+] = ((m#'1).[+], (m#'2).[+]).
Proof. by case: m. Qed.

Lemma mrestore_iE (m0 m : rmem) :
  mrestore m0 m = (mrestore m0.1 m.1, mrestore m0.2 m.2).
Proof. by case: m0 m => a1 a2 [b1 b2]. Qed.

End RSemantics.

(* -------------------------------------------------------------------- *)
Ltac diff_v := try (right; (assumption || rewrite eq_sym; assumption)).

Notation SET := ((_.[_ <- _].[_])%pattern) (only parsing).

Ltac mem_t := rewrite ?mget_iE ![SET](mget_eq, mget_neq); diff_v.

(* -------------------------------------------------------------------- *)
(* Ported from [psemantic.v:931-956]: generic theory of [ubn], used by    *)
(* [ssem_while_ubn].                                                      *)
(* -------------------------------------------------------------------- *)
Section UbnTheory.
Context {R : realType}.
Local Notation Distr T := {distr T%type / R}.

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
End UbnTheory.

(* -------------------------------------------------------------------- *)
(* The empty exception alphabet                                          *)

(* -------------------------------------------------------------------- *)
(* The empty exception alphabet                                          *)
(*                                                                       *)
(* [exn] is only required to be an [eqType] -- the semantics needs        *)
(* decidable equality for the [k' =P k] test in [ocatch], and nothing     *)
(* more; [outcome]'s [Choice] instance is classical.  An [eqType] may be  *)
(* empty, so instantiating [exn := void] recovers the exception-free      *)
(* language: no [raise] can be built, and in any induction over [cmd_]    *)
(* the two new cases carry a [k : void] and are discharged by [case: k].  *)
(* A completeness proof with no rule for [try_] can therefore be stated   *)
(* at this instance and stay closed.                                     *)
(* -------------------------------------------------------------------- *)
Section VoidExn.
Context {R : realType} {A B : codeType} {X Xg Y : eqType} {M : memType A B X Xg}.

Definition vexnty : void -> A := fun k => match k with end.

Local Notation vcmd := (@cmd_ R A B X Xg M void vexnty Y).

Lemma noexc_void (c : vcmd) : noexc c.
Proof.
elim: c =>
  [||T x e|T gx ge|T x d|bs c0 ih rs|e c1 ih1 c2 ih2|e c0 ih|c1 ih1 c2 ih2|f
   |k e|c0 ih k x ch ihh] //=; by [split | case: k].
Qed.

(* hence at this instance the exception-aware semantics is literally the
 * original one, pushed along [ONorm] *)
Lemma osem_void (ps : Y -> vcmd) c m :
  osem_ ps c m = dmargin ONorm (ssem_ ps c m).
Proof. by apply: osem_noexc => [f|]; exact: noexc_void. Qed.

End VoidExn.
