Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
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
Set Allow StrictProp.

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

Class monad (m : Type -> Type) : Type := {
  unit {a} : a -> m a;
  fmap {a b} : (a -> b) -> m a -> m b;
  mult {a} : m (m a) -> m a;
  id {a} : m a -> m a;
  mult_unit_id {a} : @mult a ∘ unit = id;
  mult_fmap_unit_id {a} : @mult a ∘ fmap unit = id;
  mult_assoc {a} : @mult a ∘ fmap mult = mult ∘ mult
}.

Class additive_monad (m : Type -> Type) : Type := {
  plus {a} : m a -> m a -> m a;
  neu {a} : m a;
  is_monad : monad m;
  plus_neu_l {a} {x : m a} : plus neu x = x;
  plus_neu_r {a} {x : m a} : plus x neu = x;
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

Lemma ord_play_trans_prf {esig a} : forall p1 p2 p3 : play esig a, ord_play p1 p2 -> ord_play p2 p3 -> ord_play p1 p3.
Proof.
Admitted.

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

Lemma ord_play_antisym_prf {esig a} : forall p1 p2 : play esig a, ord_play p1 p2 -> ord_play p2 p1 -> p1 = p2.
Proof.
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

Inductive strat_id_has {esig a} : play esig a -> Prop :=
| StratId {p} : strat_id_has p
| StratIdDownclose (p1 p2 : _) (ord : ord_play p1 p2) (h : strat_id_has p2) : strat_id_has p1.

Definition strat_id {esig a} (s : strat esig a) : strat esig a :=
  mk_downset
    (play_poset esig a)
    strat_id_has
    StratIdDownclose.

Lemma strat_mult_unit_id {esig a} : @strat_mult esig a ∘ strat_unit = strat_id.
Proof.
extensionality s.
unfold compose.
