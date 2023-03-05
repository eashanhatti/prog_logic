Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
(* Import ListNotations. *)
Require Import Coq.Init.Nat.
Require Import Coq.Init.Specif.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.PropExtensionality.
Unset Printing Records.

Ltac exfalsoby e := exfalso; exact e.

Lemma sym {a} {x y : a} : x = y -> y = x.
auto.
Qed.

Arguments exist {A} {P}.
Open Scope program_scope.

Record poset := {
  carrier : Type;
  ord : relation carrier;
  ord_preorder : PreOrder ord;
  ord_antisym : Antisymmetric carrier eq ord
}.

Record downset (pset : poset) := mk_downset {
  has : carrier pset -> Prop;
  closed x y : ord pset x y -> has y -> has x
}.
Arguments has {pset}.
Arguments closed {pset}.

Axiom predicate_extensionality : forall {a} {P Q : a -> Prop}, (forall x, P x <-> Q x) -> P = Q.

Theorem downset_extensionality {pset} {dset1 dset2 : downset pset} : (forall x, has dset1 x <-> has dset2 x) -> dset1 = dset2.
intro.
assert (has dset1 = has dset2).
exact (predicate_extensionality H).
induction dset1. induction dset2.
simpl in H0.
generalize dependent closed0.
rewrite H0.
intros.
assert (closed0 = closed1).
extensionality x.
extensionality y.
extensionality ord.
extensionality h.
exact (proof_irrelevance (has1 x) _ _).
rewrite H1.
reflexivity.
Qed.

(* use Coq id instead of strat_id *)
Class monad (m : Type -> Type) : Type := {
  unit {a} : a -> m a;
  fmap {a b} : (a -> b) -> m a -> m b;
  mult {a} : m (m a) -> m a;
  mult_unit_id {a} : @mult a ∘ unit = id;
  mult_fmap_unit_id {a} : @mult a ∘ fmap unit = id;
  mult_assoc {a} : @mult a ∘ fmap mult = mult ∘ mult
}.

Class additive_monad (m : Type -> Type) : Type := {
  plus {a} : m a -> m a -> m a;
  bot {a} : m a;
  is_monad : monad m;
  plus_bot_l {a} {x : m a} : plus bot x = x;
  plus_bot_r {a} {x : m a} : plus x bot = x;
  plus_assoc {a} {x y z : m a} : plus x (plus y z) = plus (plus x y) z
}.

Record effect_sig := mk_effect_sig {
  label : Type;
  par : label -> Type;
  ar : label -> Type
}.

Inductive play (esig : effect_sig) (a : Type) :=
| Emp : play esig a
| Ret (x : a) : play esig a
| Inv (l : label esig) (x : par esig l) : play esig a
| InvRes (l : label esig) (x : par esig l) (v : ar esig l) (p : play esig a) : play esig a.
Arguments Emp {esig} {a}.
Arguments Ret {esig} {a}.
Arguments Inv {esig} {a}.
Arguments InvRes {esig} {a}.

(*
art <= arthur, not arte <= arthure
art <= arthur, eart <= earthur
InvRes p l x v -----> l(x) v p

p1 <= p2 ---> p1 <= l(x) v p2
*)
Inductive ord_play {esig a} : relation (play esig a) :=
| EmpPrefix {p} : ord_play Emp p
| RetPrefix {x} : ord_play (Ret x) (Ret x)
| InvPrefix {l x} : ord_play (Inv l x) (Inv l x)
| InvInvResPrefix {p l x v} : ord_play (Inv l x) (InvRes l x v p)
| InvResPrefix {p1 p2 l x v} (ord_p : ord_play p1 p2) : ord_play (InvRes l x v p1) (InvRes l x v p2).

Lemma pfx_nil_is_nil {esig a} {p : play esig a} : ord_play p Emp -> p = Emp.
Proof.
intro.
inversion H.
reflexivity.
Qed.

(* not true *)
Fixpoint rev_InvResPrefix {esig a} {p1 p2 : play esig a} {l x v} (H : ord_play (InvRes l x v p1) p2) {struct H} : ord_play p1 p2.
inversion H.
exact (InvResPrefix ReflPrefix).
subst.
assert (ord_play p1 p3).
exact (rev_InvResPrefix _ _ _ _ _ _ _ ord_p).
exact (InvResPrefix H0).
Qed.

Lemma ord_play_trans_prf {esig a} (p1 p2 p3 : play esig a) : ord_play p1 p2 -> ord_play p2 p3 -> ord_play p1 p3.
Proof.
intros.
induction H.
induction H0.
exact EmpPrefix.
exact EmpPrefix.
exact (InvResPrefix EmpPrefix).
exact H0.
exact (IHord_play (rev_InvResPrefix H0)).
Qed.

Local Instance ord_play_refl {esig a} : Reflexive (@ord_play esig a) := {
  reflexivity p := ReflPrefix (p:=p)
}.

Local Instance ord_play_trans {esig a} : Transitive (@ord_play esig a) := {
  transitivity := ord_play_trans_prf
}.

Local Instance ord_play_preorder {esig a} : PreOrder (@ord_play esig a) := {
  PreOrder_Reflexive := ord_play_refl;
  PreOrder_Transitive := ord_play_trans
}.

Lemma peel_ord_play {esig a l1 x1 v1 l2 x2 v2} {p1 p2 : play esig a} : ord_play (InvRes p1 l1 x1 v1) (InvRes p2 l2 x2 v2) -> ord_play p1 p2.
intro.
inversion H. subst.
reflexivity.
subst.
exact (rev_InvResPrefix ord_p).
Qed.

Lemma ord_play_antisym_prf {esig a} (p1 p2 : play esig a) : ord_play p1 p2 -> ord_play p2 p1 -> p1 = p2.
(* intros.
destruct p1, p2.
reflexivity.
inversion H.
inversion H.
inversion H0.
inversion H.
inversion H.
reflexivity.
inversion H.
inversion H0.
inversion H.
inversion H.
inversion H.
reflexivity.
inversion H0.
inversion H.
inversion H.
inversion H.
inversion H.
generalize dependent H5.
generalize dependent H6.
generalize dependent H1.
generalize dependent H0.
generalize dependent H.
generalize dependent x.
generalize dependent v.
rewrite H4.
intros.
assert (v = v0). *)
Admitted.

Local Instance ord_play_antisym {esig a} : Antisymmetric (play esig a) eq (@ord_play esig a) := {
  antisymmetry := ord_play_antisym_prf
}.

Definition play_poset (esig : effect_sig) (a : Type) : poset := {|
  carrier := play esig a;
  ord := ord_play;
  ord_preorder := ord_play_preorder;
  ord_antisym := ord_play_antisym
|}.

Definition strat (esig : effect_sig) (a : Type) : Type := downset (play_poset esig a).

Definition closed_strat (esig : effect_sig) (a : Type) (has : play esig a -> Prop) : Type :=
  forall p1 p2, ord_play p1 p2 -> has p2 -> has p1.

Definition downclose_has {pset : poset} (has : carrier pset -> Prop) : carrier pset -> Prop :=
  fun x => exists y, has y /\ ord pset x y.

Lemma downclose_has_is_downclosed {pset : poset} {has : carrier pset -> Prop} :
  forall x y, ord pset x y -> downclose_has has y -> downclose_has has x.

(* actually add constructors for prefix instead of downclose constructor, then prove are downclosed *)
Inductive strat_unit_fake_has {esig a} (x : a) : play esig a -> Prop :=
| StratUnitRet : strat_unit_fake_has x (Ret x).

Definition strat_unit_has {a} (x : a) := downclose_has (strat_unit_fake_has x).

Lemma strat_unit_closed {esig a} (x : a) : closed_strat esig a (strat_unit_has x).
cbv. intros.
induction H0.
inversion H.
exact (StratUnitEmp x).
exact (StratUnitRet x).
inversion H.
exact (StratUnitEmp x).
exact (StratUnitEmp x).
Qed.

Definition strat_unit {esig a} (x : a) : strat esig a :=
  mk_downset
    (play_poset esig a)
    (strat_unit_has x)
    (strat_unit_closed x).

Inductive strat_prod_has {esig a} : play esig (strat esig a) -> play esig a -> Prop :=
| StratProdRet {s p} (_ : has s p) : strat_prod_has (Ret s) p
| StratProdInvRes {l x v p1 p2} (_ : strat_prod_has p1 p2) : strat_prod_has (InvRes p1 l x v) (InvRes p2 l x v)
| StratProdDownclose {ps} : closed_strat esig a (strat_prod_has ps)
(*| StratProdEmp {p} : strat_prod_has p Emp
| StratProdInvResPrefix {p1 p2 l x v} (_ : strat_prod_has p1 (InvRes p2 l x v)) : strat_prod_has p1 p2 *).

(* Lemma strat_prod_closed {esig a} (p : play esig (strat esig a)) : closed_strat esig a (strat_prod_has p).
cbv. intros.
induction H.
exact StratProdEmp.
exact H0.
refine (IHord_play _).
exact (StratProdInvResPrefix H0).
Qed. *)



Inductive strat_mult_has {esig a} (ss : strat esig (strat esig a)) : play esig a -> Prop :=
| StratMult {p1 p2} (_ : has ss p1) (_ : strat_prod_has p1 p2) : strat_mult_has ss p2.

Lemma strat_mult_closed {esig a} (ss : strat esig (strat esig a)) : closed_strat esig a (strat_mult_has ss).
cbv. intros.
destruct H0.
exact (StratMult ss H0 (StratProdDownclose _ _ H H1)).
Qed.

Definition strat_mult {esig a} (ss : strat esig (strat esig a)) : strat esig a :=
  mk_downset
    (play_poset esig a)
    (strat_mult_has ss)
    (strat_mult_closed ss).

Fixpoint prod_has_ret {esig a} {s : strat esig a} {p} (H : strat_prod_has (Ret s) p) : has s p.
inversion H.
exact H1.
subst.
assert (has s p2).
exact (prod_has_ret _ _ _ _ H1).
exact (closed s _ _ H0 H2).
Qed.

Lemma help {esig a} {p0 p1 : play esig (strat esig a)} {p2} : ord_play p1 p0 -> strat_prod_has p1 p2 -> strat_prod_has p0 p2.
intros.
Admitted.

Lemma strat_mult_unit_id_help {esig a} {s : strat esig a} {p1 p2} : has (strat_unit s) p1 -> strat_prod_has p1 p2 -> has s p2.
intros.
induction H.
inversion H0.
exact H1.
exact (prod_has_ret H0).
refine (IHstrat_unit_has _).
Admitted.

Lemma strat_mult_unit_id {esig a} : @strat_mult esig a ∘ strat_unit = id.
extensionality s.
unfold compose.
assert (forall p, has (strat_mult (strat_unit s)) p <-> has s p).
intro.
split.
intro.
destruct H.
exact (strat_mult_unit_id_help H H0).
intro.
exact (StratMult (strat_unit s) (StratUnitRet s) (StratProdRet H)).
exact (downset_extensionality H).
Qed.

Inductive strat_fmap_help_has {esig a b} (f : a -> b) : play esig a -> play esig b -> Prop :=
| StratFmapHelpRet {x} : strat_fmap_help_has f (Ret x) (Ret (f x))
| StratFmapHelpCons {p1 p2 l x v} (_ : strat_fmap_help_has f p1 p2): strat_fmap_help_has f (InvRes p1 l x v) (InvRes p2 l x v)
| StratFmapHelpEmp {p} : strat_fmap_help_has f p Emp
| StratFmapHelpInvResPrefix {p1 p2 l x v} (_ : strat_fmap_help_has f p1 (InvRes p2 l x v)) : strat_fmap_help_has f p1 p2.

Lemma strat_fmap_help_closed {esig a b} (f : a -> b) (p : play esig a) : closed_strat esig b (strat_fmap_help_has f p).
cbv. intros.
induction H.
exact (StratFmapHelpEmp _).
exact H0.
refine (IHord_play _).
exact (StratFmapHelpInvResPrefix _ H0).
Qed.

Inductive strat_fmap_has {esig a b} (f : a -> b) (s : strat esig a) : play esig b -> Prop :=
| StratFmap {p1 p2} (_ : has s p1) (_ : strat_fmap_help_has f p1 p2) : strat_fmap_has f s p2.

Lemma strat_fmap_closed {esig a b} (f : a -> b) (s : strat esig a) : closed_strat esig b (strat_fmap_has f s).
cbv. intros.
destruct H0.
exact (StratFmap f s H0 (strat_fmap_help_closed _ _ _ _ H H1)).
Qed.

Definition strat_fmap {esig a b} (f : a -> b) (s : strat esig a) : strat esig b :=
  mk_downset
    (play_poset esig b)
    (strat_fmap_has f s)
    (strat_fmap_closed f s).

Lemma strat_mult_fmap_unit_id {esig a} : @strat_mult esig a ∘ strat_fmap strat_unit = id.
Admitted.

Lemma strat_mult_assoc {esig a} : @strat_mult esig a ∘ strat_fmap strat_mult = strat_mult ∘ strat_mult.
Admitted.

Local Instance strat_monad {esig} : monad (strat esig) := {
  unit _ := strat_unit;
  fmap _ _ := strat_fmap;
  mult _ := strat_mult;
  mult_unit_id _ := strat_mult_unit_id;
  mult_fmap_unit_id _ := strat_mult_fmap_unit_id;
  mult_assoc _ := strat_mult_assoc
}.

Inductive strat_plus_has {esig a} (s1 s2 : strat esig a) : play esig a -> Prop :=
| StratPlusInjLeft {p} (_ : has s1 p) : strat_plus_has s1 s2 p
| StratPlusInjRight {p} (_ : has s2 p) : strat_plus_has s1 s2 p
| StratPlusDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_plus_has s1 s2 p2) : strat_plus_has s1 s2 p1.
Arguments StratPlusInjLeft {esig} {a} {s1} {s2} {p}.
Arguments StratPlusInjRight {esig} {a} {s1} {s2} {p}.

Ltac elim_strat_plus h :=
  refine (match h with
          | StratPlusInjLeft _ => _
          | StratPlusInjRight _ => _
          | StratPlusDownclose _ _ _ _ _ _ => _
          end).

Definition strat_plus {esig a} (s1 s2 : strat esig a) : strat esig a :=
  mk_downset
    (play_poset esig a)
    (strat_plus_has s1 s2)
    (StratPlusDownclose s1 s2).

Inductive strat_bottom_has {esig a} : play esig a -> Prop :=
| StratBottomDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_bottom_has p2) : strat_bottom_has p1.

Definition strat_bottom {esig a} : strat esig a :=
  mk_downset
    (play_poset esig a)
    strat_bottom_has
    StratBottomDownclose.

Fixpoint strat_bot_impl_false {esig a} {p : play esig a} : strat_bottom_has p -> False.
intros h.
induction h.
exact IHh.
Qed.

Fixpoint strat_plus_has_bot_cancel_l {esig a} {s : strat esig a} {p} (h : strat_plus_has strat_bottom s p) {struct h} :
  has s p.
intros.
elim_strat_plus h.
exfalsoby (strat_bot_impl_false h0).
exact h0.
exact (closed s _ _ o (strat_plus_has_bot_cancel_l _ _ _ _ s0)).
Qed.

Fixpoint strat_plus_has_bot_cancel_r {esig a} {s : strat esig a} {p} (h : strat_plus_has s strat_bottom p) {struct h} :
  has s p.
intros.
elim_strat_plus h.
exact h0.
exfalsoby (strat_bot_impl_false h0).
exact (closed s _ _ o (strat_plus_has_bot_cancel_r _ _ _ _ s0)).
Qed.

Lemma strat_plus_bot_l {esig a} {s : strat esig a} : strat_plus strat_bottom s = s.
assert (forall p, has (strat_plus strat_bottom s) p <-> has s p).
intro.
split.
intro.
elim_strat_plus H.
exfalsoby (strat_bot_impl_false h).
exact h.
exact (closed s _ _ o (strat_plus_has_bot_cancel_l s0)).
intro.
exact (StratPlusInjRight H).
exact (downset_extensionality H).
Qed.

Lemma strat_plus_bot_r {esig a} {s : strat esig a} : strat_plus s strat_bottom = s.
assert (forall p, has (strat_plus s strat_bottom) p <-> has s p).
intro.
split.
intro.
exact (strat_plus_has_bot_cancel_r H).
intro.
exact (StratPlusInjLeft H).
exact (downset_extensionality H).
Qed.

Fixpoint strat_plus_has_assoc {esig a} {s1 s2 s3 : strat esig a} (p : play esig a) {struct p} :
  strat_plus_has s1 (strat_plus s2 s3) p = strat_plus_has (strat_plus s1 s2) s3 p.
assert (has (strat_plus s1 (strat_plus s2 s3)) p <-> has (strat_plus (strat_plus s1 s2) s3) p).
admit.
exact (propositional_extensionality _ _ H).
Admitted.

Fixpoint strat_plus_assoc {esig a} {s1 s2 s3 : strat esig a} : strat_plus s1 (strat_plus s2 s3) = strat_plus (strat_plus s1 s2) s3.
assert (forall p, has (strat_plus s1 (strat_plus s2 s3)) p <-> has (strat_plus (strat_plus s1 s2) s3) p).
intro.
split.
intro.
induction H.
refine (StratPlusInjLeft _).
exact (StratPlusInjLeft H).
simpl.
rewrite (sym (strat_plus_has_assoc p)).
exact (StratPlusInjRight H).
Admitted.

Local Instance strat_additive_monad {esig} : additive_monad (strat esig) := {
  plus _ := strat_plus;
  bot _ := strat_bottom;
  is_monad := strat_monad;
  plus_bot_l _ _ := strat_plus_bot_l;
  plus_bot_r _ _ := strat_plus_bot_r;
  plus_assoc _ _ _ _ := strat_plus_assoc
}.

Inductive unit_ty : Type :=
| tt : unit_ty.

Definition strat_bind {esig a b} (s : strat esig a) (k : a -> strat esig b) : strat esig b :=
  strat_mult (strat_fmap k s).

Notation "s1 + s2" := (strat_plus s1 s2) (at level 50, left associativity).
(* Notation "s *" := (strat_star s) (at level 49). *)
Notation "x <- s1 ;; s2" := (strat_bind s1 (fun x => s2)) (at level 61, s1 at next level, right associativity).
Notation "s1 ;; s2" := (strat_bind s1 (fun _ => s2)) (at level 61, right associativity).

(*
strat_star_n_has 0 a = mult . fmap unit

strat_star_n_has (S n) a = \exists a' . strat_star_n_has n a' /\ a = a';a

strat_star_has a =  \exists n . strat_star_n_has n a
*)
(* Fixpoint strat_star_n {esig a} (n : nat) (s : strat esig a) : strat esig a :=
  match n with
  | S m => s ;; strat_star_n m s
  | Z => s
  end.
Definition strat_star_has {esig a} (s : strat esig a) : play esig a -> Prop :=
  fun p => exists n, has (strat_star_n n s) p. *)

(* Fixpoint strat_star_n_has {esig a} (n : nat) (s : strat esig a) (p : play esig a) : Prop :=
  match n with
  | 0 => strat_mult_has (fmap unit s) p
  | S m => exists a0, 
  end. *)

Fixpoint strat_star_n {esig a} (n : nat) (s : strat esig a) : strat esig a :=
  match n with
  | 0 => s
  | S m => s ;; strat_star_n m s
  end.

Definition strat_star_has {esig a} (s : strat esig a) (p : play esig a) : Prop :=
  exists n, has (strat_star_n n s) p.

Lemma strat_star_closed {esig a} (s : strat esig a) : closed_strat esig a (strat_star_has s).
Admitted.

Definition strat_star {esig a} (s : strat esig a) : strat esig a :=
  mk_downset
    (play_poset esig a)
    (strat_star_has s)
    (strat_star_closed s).

Definition strat_star {esig a} (s : strat esig a) : strat esig a :=
  mk_downset
    (play_poset esig a)
    (strat_star_has s)
    (strat_star_closed s).

Inductive strat_emp_has {esig a} : play esig a -> Prop :=
| StratEmp : strat_emp_has []
| StratEmpDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_emp_has p2) : strat_emp_has p1.
Definition strat_emp {esig a} : strat esig a :=
  mk_downset
    (play_poset esig a)
    strat_emp_has
    StratEmpDownclose.

Definition assert {esig} (b : bool) : strat esig unit_ty :=
  if b then
    unit tt
  else
    strat_emp.
Definition ret {esig a} := @strat_unit esig a.
Definition skip {esig} : strat esig unit_ty := strat_unit tt.

Inductive strat_invoke_has {esig} (l : label esig) (x : par esig l) : play esig (ar esig l) -> Prop :=
| StratInvoke {v} : strat_invoke_has l x [Ret v; Res l v; Inv l x]
| StratInvokeDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_invoke_has l x p2) : strat_invoke_has l x p1.

Definition strat_invoke {esig} (l : label esig) (x : par esig l) : strat esig (ar esig l) :=
  mk_downset
    (play_poset esig (ar esig l))
    (strat_invoke_has l x)
    (StratInvokeDownclose l x).

Notation "l [ esig , x ]" := (@strat_invoke esig l x) (at level 2).

Definition sif {esig a} (b : bool) (s1 s2 : strat esig a) : strat esig a :=
  (assert b ;; s1) + (assert (negb b) ;; s2).
Definition while {esig a} (b : bool) (s : strat esig a) : strat esig a :=
  strat_star (assert b ;; s).

Definition nat_sig : effect_sig := {|
  label := unit_ty;
  par := const nat;
  ar := const nat
|}.

Example ex1 : strat nat_sig nat :=
  n <- tt [ nat_sig , 0 ] ;;
  sif (n <? 4)
    (while true (tt [ nat_sig , 14 ]))
    (ret (S n)).