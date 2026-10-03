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

End Semantics.

(* -------------------------------------------------------------------- *)
Arguments esem A B X Xg M T e%_X m%_M.
Arguments exnv : clear implicits.
Arguments outcome : clear implicits.
Arguments osem_ {_ _ _ _ _ _ _ _ _} ps s%_S m%_M.
Arguments ssem_ {_ _ _ _ _ _ _ _ _} ps s%_S m%_M.

Notation "e `_ m" := (@esem _ _ _ _ _ _ e%X m%M) : sem_scope.
Notation "`[{ e }]" := (@esem _ _ _ _ _ _ e%X) (at level 2, format "`[{ e }]").

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
