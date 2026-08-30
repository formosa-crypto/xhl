From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals     Require Import reals constructive_ereal.
From mathcomp.analysis Require Import esum ereal counting_distr.
From mathcomp    Require  finmap.
From xhl.pwhile Require Import notations inhabited pwhile psemantic range.

Import GRing.Theory Order.Theory Num.Theory.

Local Open Scope syn_scope.
Local Open Scope mem_scope.
Local Open Scope ereal_dual_scope.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

(* -------------------------------------------------------------------- *)

Section ehl.
Context {X Y : eqType} {mem : memType X}.

Definition cond := mem -> \bar pwhile.R.

Definition cond2 := mem -> \bar pwhile.R -> mem -> \bar pwhile.R.

Definition cmd  := (@cmd_ X mem Y).
Definition psi := Y -> cmd.

(* -------------------------------------------------------------------- *)
(* eHoare triple                                                        *)
(* -------------------------------------------------------------------- *)

Implicit Types  (f g h : cond).

Definition ehl_ (ps:psi) f c g :=
  forall m : mem, (espe (ssem_ ps c m) g <= f m)%E.

(* -------------------------------------------------------------------- *)
(* Generic eHoare triple                                                *)
(* -------------------------------------------------------------------- *)

Definition kehl_ (ps:psi) f c (g: cond2) :=
  forall m : mem, (espe (ssem_ ps c m) (fun m' => g m ((ssem_ ps c m m')%:E) m') <= f m)%E.

Definition bound {T : choiceType} (g : T -> \bar R) m0 m :=
  if (m == m0) then (g m) else +oo%E.

Lemma kehl_ehl ps P c Q :
  kehl_ ps P c Q <-> (forall s0, ehl_ ps (bound P s0) c (fun s => Q s0 ((ssem_ ps c s0 s)%:E) s)).
Proof.
rewrite /bound; split.
+ move=> h m0 m.
  case: ifP.
  - by move => /eqP <-.
  - move => _. exact : leey.
+ move => h m.
  have // := (h m m).
  by rewrite eq_refl.
Qed.

Lemma ehl_kehl ps P c Q :
  kehl_ ps P c (fun _ _ => Q) <-> ehl_ ps P c Q.
Proof.  by split; move => h m; apply h. Qed.

(* -------------------------------------------------------------------- *)
(* Collapsing a block's [dlet]/[dunit].  Shared by ehl.v and ehl2.v; it
 * is an equality, not an inequality, because the completeness proof in
 * ehl2.v reads it in the other direction. *)
Lemma espe_dlet_ret (mu : Distr mem) (g : cond) m rs :
  (forall m, (0 <= g m)%E) ->
  espe (\dlet_(m' <- mu) dunit (mret m m' rs)) g
    = espe mu (fun m'' => g (mret m m'' rs)).
Proof.
move=> Hg; rewrite eexp_dlet //.
by apply: eexp_eq => x; rewrite eexp_dunit.
Qed.

(* -------------------------------------------------------------------- *)
(* Procedire contract                                                   *)
(* -------------------------------------------------------------------- *)

Definition clause : Type := cond * cond2.

Definition get_pre (an:clause) :=
  let (pre,_) := an in
  pre.

Definition get_post (an:clause) :=
  let (_,post) := an in
  post.

Definition phi : Type := Y -> clause.

(** Empty procedure contract **)

Definition empty_precondition : cond := (fun _ => +oo)%E.

Definition empty_postcondition :  cond2 := (fun _ _ _ => 0)%E.

Definition empty_clause : clause := (empty_precondition, empty_postcondition).

Definition cl_empty: Y -> clause := fun _ => empty_clause.

(** Properties on procedure contract **)

Definition cond2_mono (P:  mem -> \bar pwhile.R -> mem -> \bar pwhile.R) :=
 forall (r r' : (\bar pwhile.R)), (r <= r')%E ->(forall x x' : mem, P x r x' <= P x r' x')%E.

Definition cl_post_mono (cl: phi) :=
  forall (f: Y),  cond2_mono (get_post (cl f)).

Definition cl_pre_pos (cl: phi) :=
  forall (f: Y), (forall x , 0 <= (get_pre (cl f)) x )%E.

Definition cl_post_pos (cl: phi) :=
  forall (f: Y), (forall x mu x', 0 <= (get_post (cl f)) x mu x')%E.

(* -------------------------------------------------------------------- *)
(* Lift boolean condition to extended reals                             *)
(* -------------------------------------------------------------------- *)

Definition lift (b: mem -> bool) f (m: mem) : \bar pwhile.R :=
  match (b m) with
  | true => (f m)
  | false => +oo
  end.

End ehl.

HB.mixin Record isPhi {X Y : eqType} {mem : memType X}
  (cl : Y -> (@clause X mem)) :=
  {
    post_mono : cl_post_mono cl;
    pre_pos : cl_pre_pos cl;
    post_pos : cl_post_pos cl;
  }.

HB.structure Definition Phi {X Y : eqType} {mem : memType X} :=
  {f of @isPhi X Y mem f}.

Lemma post_mono_cl_empty
  {X Y : eqType} {mem : memType X}: cl_post_mono (@cl_empty X Y mem).
Proof. by rewrite /cl_post_mono / cond2_mono. Qed.

Lemma pre_pos_cl_empty
  {X Y : eqType} {mem : memType X} : cl_pre_pos (@cl_empty X Y mem).
Proof. by move => f m //=; exact: leey. Qed.

Lemma post_pos_cl_empty
  {X Y : eqType} {mem : memType X} : cl_post_pos (@cl_empty X Y mem).
Proof.  by []. Qed.

HB.instance Definition _ {X Y: eqType} {mem : memType X} :=
  isPhi.Build X Y mem (@cl_empty X Y mem)  post_mono_cl_empty pre_pos_cl_empty post_pos_cl_empty.
