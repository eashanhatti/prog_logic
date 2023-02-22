Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Coq.Init.Nat.
Require Import Coq.Init.Specif.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Init.Logic.
Require Import Coq.Logic.PropExtensionalityFacts.
Require Import Coq.Logic.ProofIrrelevance.
Set Allow StrictProp.
Set Primitive Projections.

Ltac exfalsoby e := exfalso; exact e.

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
Unset Printing Records.

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

Class monad (m : Type -> Type) : Type := {
  unit {a} : a -> m a;
  fmap {a b} : (a -> b) -> m a -> m b;
  mult {a} : m (m a) -> m a;
  id {a} : m a -> m a;
  id_idem {a} {x : m a} : id x = x;
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

Inductive event (esig : effect_sig) (a : Type) : Type :=
| Ret (v : a) : event esig a
| Inv (l : label esig) (x : par esig l) : event esig a
| Res (l : label esig) (v : ar esig l) : event esig a.
Arguments Ret {esig} {a}.
Arguments Inv {esig} {a}.
Arguments Res {esig} {a}.

Definition play esig a := list (event esig a).

Inductive wf_play {esig a} : play esig a -> Prop :=
| WfEmp : wf_play []
| WfRet {x} : wf_play [Ret x]
| WfInvRes {l x v p} : wf_play (Res l v :: Inv l x :: p)
| WfInv {l x} : wf_play [Inv l x].

Inductive ord_play {esig a} : relation (play esig a) :=
| EmpPrefix {p} : ord_play [] p
| ConsPrefix {p1 p2 e} (ord_p : ord_play p1 p2) : ord_play (e :: p1) (e :: p2).

Lemma pfx_nil_is_nil {esig a} {p : play esig a} : ord_play p [] -> p = [].
Proof.
intro.
inversion H.
reflexivity.
Qed.

Lemma ord_play_refl_prf {esig a} : forall p : play esig a, ord_play p p.
Proof.
intro.
induction p.
exact EmpPrefix.
exact (ConsPrefix IHp).
Qed.

Lemma heads_eq {a} {x y : a} {xs ys}: x :: xs = y :: ys -> x = y.
intro.
congruence.
Qed.

Lemma tails_eq {a} {x y : a} {xs ys}: x :: xs = y :: ys -> xs = ys.
intro.
congruence.
Qed.

Fixpoint ord_play_trans_prf {esig a} (p1 p2 p3 : play esig a) {struct p1} : ord_play p1 p2 -> ord_play p2 p3 -> ord_play p1 p3.
Proof.
intros.
destruct p1.
exact EmpPrefix.
destruct p3.
inversion H0. subst.
exact H.
inversion H.
inversion H0.
subst.
discriminate.
subst.
rewrite (heads_eq H4).
refine (ConsPrefix _).
rewrite (tails_eq H4) in ord_p0.
exact (ord_play_trans_prf _ _ _ _ _ ord_p ord_p0).
Qed.

Local Instance ord_play_refl {esig a} : Reflexive (@ord_play esig a) := {
  reflexivity := ord_play_refl_prf
}.

Local Instance ord_play_trans {esig a} : Transitive (@ord_play esig a) := {
  transitivity := ord_play_trans_prf
}.

Local Instance ord_play_preorder {esig a} : PreOrder (@ord_play esig a) := {
  PreOrder_Reflexive := ord_play_refl;
  PreOrder_Transitive := ord_play_trans
}.

Lemma peel_ord_play {esig a} {e1 e2 : event esig a} {p1 p2 : play esig a} : ord_play (e1 :: p1) (e2 :: p2) -> ord_play p1 p2.
intros.
inversion H.
subst.
exact ord_p.
Qed.

Fixpoint ord_play_antisym_prf {esig a} (p1 p2 : play esig a) {struct p1} : ord_play p1 p2 -> ord_play p2 p1 -> p1 = p2.
Proof.
intros.
inversion H.
inversion H0.
reflexivity.
subst.
discriminate.
subst.
f_equal.
refine (ord_play_antisym_prf _ _ _ _ _ _).
exact (peel_ord_play H).
exact (peel_ord_play H0).
Qed.

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

Inductive strat_unit_has {esig a} (x : a) : play esig a -> Prop :=
| StratUnitRet : strat_unit_has x [Ret x]
| StratUnitDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_unit_has x p2) : strat_unit_has x p1.

Definition strat_unit {esig a} (x : a) : strat esig a :=
  mk_downset
    (play_poset esig a)
    (strat_unit_has x)
    (StratUnitDownclose x).

Inductive flat {esig a b} : event esig a -> event esig b -> Prop :=
| FlatInv {l x} : flat (Inv l x) (Inv l x)
| FlatRes {l v} : flat (Res l v) (Res l v).

Inductive strat_prod_has {esig a} : play esig (strat esig a) -> play esig a -> Prop :=
| StratProdRet {s p} (_ : has s p) : strat_prod_has [Ret s] p
| StratProdCons {e1 e2 p1 p2} (is_flat : flat e1 e2) (_ : strat_prod_has p1 p2) : strat_prod_has (e1 :: p1) (e2 :: p2).

Inductive strat_mult_has {esig a} (ss : strat esig (strat esig a)) : play esig a -> Prop :=
| StratMult {p1 p2} (_ : has ss p1) (_ : strat_prod_has p1 p2) : strat_mult_has ss p2
| StratMultDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_mult_has ss p2) : strat_mult_has ss p1.

Definition strat_mult {esig a} (ss : strat esig (strat esig a)) : strat esig a :=
  mk_downset
    (play_poset esig a)
    (strat_mult_has ss)
    (StratMultDownclose ss).

Inductive strat_fmap_help_has {esig a b} (f : a -> b) : play esig a -> play esig b -> Prop :=
| StratFmapHelpRet {x} : strat_fmap_help_has f [Ret x] [Ret (f x)]
| StratFmapHelpCons {e1 e2 p1 p2} (is_flat : flat e1 e2) (_ : strat_fmap_help_has f p1 p2): strat_fmap_help_has f (e1 :: p1) (e2 :: p2).

Inductive strat_fmap_has {esig a b} (f : a -> b) (s : strat esig a) : play esig b -> Prop :=
| StratFmap {p1 p2} (_ : has s p1) (_ : strat_fmap_help_has f p1 p2) : strat_fmap_has f s p2
| StratFmapDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_fmap_has f s p2) : strat_fmap_has f s p1.

Definition strat_fmap {esig a b} (f : a -> b) (s : strat esig a) : strat esig b :=
  mk_downset
    (play_poset esig b)
    (strat_fmap_has f s)
    (StratFmapDownclose f s).

(* Definition strat_compose {esig a b c} (f : a -> strat esig b) (g : b -> strat esig c) (x : a) : strat esig c :=
  strat_mult (strat_fmap g (f x)). *)

Inductive strat_id_has {esig a} (s : strat esig a) : play esig a -> Prop :=
| StratId {p} (_ : has s p) : strat_id_has s p
| StratIdDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_id_has s p2) : strat_id_has s p1.

Definition strat_id {esig a} (s : strat esig a) : strat esig a :=
    mk_downset
      (play_poset esig a)
      (strat_id_has s)
      (StratIdDownclose s).

Fixpoint id_get_has {esig a} {s : strat esig a} {p} (h : strat_id_has s p) : has s p :=
  match h with
  | StratId _ h1 => h1
  | StratIdDownclose _ p1 p2 ord h1 => closed s p1 p2 ord (id_get_has h1)
  end.

Lemma strat_id_idem {esig a} {s : strat esig a} : strat_id s = s.
Proof.
assert (H : forall x, has (strat_id s) x <-> has s x).
intros.
split.
simpl.
intro.
exact (id_get_has H).
intro.
simpl.
exact (StratId s H).
exact (downset_extensionality H).
Qed.

Lemma sym {a} {x y : a} : x = y -> y = x.
auto.
Qed.

Lemma strat_mult_unit_id {esig a} : @strat_mult esig a ∘ strat_unit = strat_id.
Proof.
extensionality s.
assert (forall p, has ((@strat_mult esig a ∘ strat_unit) s) p <-> has (strat_id s) p).
intro.
split.
intro.
rewrite strat_id_idem.
destruct H.
destruct H0.
inversion H.
exact H0.
induction h.
inversion ord0. subst.
exact H0. subst.
exact (IHh (ord_play_trans_prf _ _ _ ord0 ord1)).
Admitted.

Lemma strat_mult_fmap_unit_id {esig a} : @strat_mult esig a ∘ strat_fmap strat_unit = strat_id.
Admitted.

Lemma strat_mult_assoc {esig a} : @strat_mult esig a ∘ strat_fmap strat_mult = strat_mult ∘ strat_mult.
Admitted.

Local Instance strat_monad {esig} : monad (strat esig) := {
  unit _ := strat_unit;
  fmap _ _ := strat_fmap;
  mult _ := strat_mult;
  id _ := strat_id;
  id_idem _ _ := strat_id_idem;
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

Axiom strat_star : forall {esig a}, strat esig a -> strat esig a.
Inductive strat_star_has {esig a} (s : strat esig a) : play esig a -> Prop :=
| StratStarBot {p} (_ : has strat_bottom p) : strat_star_has s p
| StratStarOne {p} (_ : has s p) : strat_star_has s p
| StratStarMany {p} (_ : has (strat_bind s (fun _ => strat_star s)) p) : strat_star_has s p
| StratStarDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_star_has s p2) : strat_star_has s p1.
Axiom DEFINE_strat_star :
  forall {esig a} {s : strat esig a},
    strat_star s =
      mk_downset
        (play_poset esig a)
        (strat_star_has s)
        (StratStarDownclose s).

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

Notation "s1 + s2" := (strat_plus s1 s2) (at level 50, left associativity).
(* Notation "s *" := (strat_star s) (at level 49). *)
Notation "x <- s1 ;; s2" := (strat_bind s1 (fun x => s2)) (at level 61, s1 at next level, right associativity).
Notation "s1 ;; s2" := (strat_bind s1 (fun _ => s2)) (at level 61, right associativity).
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

Definition state_sig (a : Type) : effect_sig := {|
  label := bool;
  par := fun b =>
    if b then (* get *)
      unit_ty
    else (* set *)
      a;
  ar := fun b =>
    if b then
      a
    else
      unit_ty
|}.
