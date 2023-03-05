Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Program.Basics.
Load "Monad.v".

Axiom predicate_extensionality : forall {a} {P Q : a -> Prop}, (forall x, P x <-> Q x) -> P = Q.

Class poset (a : Type) := {
  ord : relation a;
  ord_refl {x} : ord x x;
  ord_trans {x y z} : ord x y -> ord y z -> ord x z;
  ord_antisym {x y} : ord x y -> ord y x -> x = y
}.
Arguments ord {a} {poset}.
Arguments ord_refl {a} {poset} {x}.
Arguments ord_trans {a} {poset} {x y z}.
Arguments ord_antisym {a} {poset} {x y}.

Record downset (a : Type) {pset : poset a} := mk_downset {
  has : a -> Prop;
  downclosed {x y : a} : ord x y -> has y -> has x
}.
Arguments has {a} {pset}.
Arguments downclosed {a} {pset} _ {x} {y}.

Theorem downset_extensionality {a} `{poset a} {dset0 dset1 : downset a} : (forall x, has dset0 x <-> has dset1 x) -> dset0 = dset1.
rename H into pset.
intro.
assert (has dset0 = has dset1).
exact (predicate_extensionality H).
induction dset0. induction dset1.
simpl in H0.
generalize dependent downclosed0.
rewrite H0.
intros.
assert (@downclosed0 = @downclosed1).
extensionality x.
extensionality y.
extensionality ord.
extensionality h.
exact (proof_irrelevance (has1 x) _ _).
rewrite H1.
reflexivity.
Qed.

Inductive ord_downset {a} `{poset a} : relation (downset a) :=
| OrdDownset {dset0 dset1} (incl : forall x, has dset0 x -> has dset1 x) : ord_downset dset0 dset1.

Global Instance downset_poset {a} `{poset a} : poset (downset a).
refine {|
  ord := ord_downset;
  ord_refl := _;
  ord_trans := _;
  ord_antisym := _
|}.
intro.
exact (OrdDownset (fun _ h => h)).
intros.
induction H0, H1.
refine (OrdDownset _).
intros.
exact (incl0 x (incl x H0)).
intros.
induction H0, H1.
refine (downset_extensionality _).
intro.
split.
exact (incl x).
exact (incl0 x).
Defined.

Lemma downset_inclusion {a} `{poset a} {dset0 dset1} : forall {x}, ord_downset dset0 dset1 -> has dset0 x -> has dset1 x.
intros.
induction H0.
exact (incl x H1).
Qed.

Definition downclose_has {a} `{poset a} (has : a -> Prop) : a -> Prop :=
  fun x => exists y, has y /\ ord x y.

Lemma downclose_has_is_downclosed {a} `{poset a} {has : a -> Prop} :
  forall x y, ord x y -> downclose_has has y -> downclose_has has x.
rename H into pset.
intros.
destruct H0.
destruct H0.
exists x0.
split.
auto.
exact (ord_trans H H1).
Qed.

Inductive downset_unit_has {a} (x : a) : a -> Prop :=
| DsetUnitHas : downset_unit_has x x.

Definition downset_unit {a} `{poset a} (x : a) : downset a := {|
  has := downclose_has (downset_unit_has x);
  downclosed := downclose_has_is_downclosed
|}.

Inductive downset_fmap_has {a b} `{poset a} (f : a -> b) (dset : downset a) : b -> Prop :=
| DsetFmapHas {x} (h : has dset x): downset_fmap_has f dset (f x).

Definition downset_fmap {a b} `{poset a} `{poset b} (f : a -> b) (dset : downset a) : downset b := {|
  has := downclose_has (downset_fmap_has f dset);
  downclosed := downclose_has_is_downclosed
|}.

Inductive downset_mult_has {a} `{poset a} (dset0 : downset (downset a)) : a -> Prop :=
| DsetMultHas {dset1} {x} (h0 : has dset0 dset1) (h1 : has dset1 x) : downset_mult_has dset0 x.


Definition downset_mult {a} `{poset a} (dset : downset (downset a)) : downset a := {|
  has := downclose_has (downset_mult_has dset);
  downclosed := downclose_has_is_downclosed
|}.

Lemma downset_mult_unit_id {a} `{poset a} : downset_mult (a:=a) ∘ downset_unit = id.
unfold compose.
extensionality dset.
refine (downset_extensionality _).
intro.
split.
intro.
destruct H0.
destruct H0.
destruct H0.
assert (has dset1 x).
exact (downclosed dset1 H1 h1).
assert (ord dset1 dset).
destruct h0.
destruct H2.
inversion H2.
exact H3.
exact (downset_inclusion H2 H0).
intro.
exists x.
split.
exists dset.
exists dset.
split.
exact (DsetUnitHas dset).
exact ord_refl.
exact H0.
exact ord_refl.
Qed.

Lemma downset_mult_fmap_unit_id {a} `{poset a} : downset_mult (a:=a) ∘ downset_fmap downset_unit = id.
unfold compose.
extensionality dset.
refine (downset_extensionality _).
intro.
split.
intro.
destruct H0.
destruct H0.
destruct H0.
assert (has dset1 x).
exact (downclosed dset1 H1 h1).
assert (ord dset1 dset).
destruct h0.
destruct H2.
destruct H2.
assert (ord (downset_unit x1) dset).
refine (OrdDownset _).
intros.
induction H2.
destruct H2.
inversion H2.
rewrite H5 in h.
exact (downclosed dset H4 h).
exact (ord_trans H3 H2).
exact (downset_inclusion H2 H0).
intro.
exists x.
split.
refine (DsetMultHas _ (dset1:= downset_unit x) _ _).
exists (downset_unit x).
split.
refine (DsetFmapHas _ _ _).
exact H0.
exact ord_refl.
exists x.
split.
exact (DsetUnitHas x).
exact ord_refl.
exact ord_refl.
Qed.

Lemma downset_mult_assoc {a} `{poset a} : downset_mult (a:=a) ∘ downset_fmap downset_mult = downset_mult ∘ downset_mult.
unfold compose.
extensionality dddset.
refine (downset_extensionality _).
intro.
split.
intro.
admit.
intro.
