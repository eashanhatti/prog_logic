Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Program.Basics.
Open Scope program_scope.
Load "theories/Monad.v".
Load "theories/Poset.v".

Axiom predicate_extensionality : forall {a} {P Q : a -> Prop}, (forall x, P x <-> Q x) -> P = Q.

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
apply (mk_poset ord_downset).
intro.
exact (OrdDownset (fun _ h => h)).
intros.
induction H0, H1.
apply OrdDownset.
intros.
exact (incl0 x (incl x H0)).
intros.
induction H0, H1.
apply downset_extensionality.
intro.
split.
exact (incl x).
exact (incl0 x).
Defined.

Theorem downset_inclusion {a} `{poset a} {dset0 dset1} : forall {x}, ord_downset dset0 dset1 -> has dset0 x -> has dset1 x.
intros.
induction H0.
exact (incl x H1).
Qed.

Definition downclose_has {a} `{poset a} (has : a -> Prop) : a -> Prop :=
  fun x => exists y, has y /\ ord x y.

Theorem downclose_has_is_downclosed {a} `{poset a} {has : a -> Prop} :
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
Arguments DsetUnitHas {a} {x}.

Definition downset_unit {a} `{poset a} (x : a) : downset a := {|
  has := downclose_has (downset_unit_has x);
  downclosed := downclose_has_is_downclosed
|}.

Inductive downset_fmap_has {a b} `{poset a} (f : a -> b) (dset : downset a) : b -> Prop :=
| DsetFmapHas {x} (h : has dset x): downset_fmap_has f dset (f x).
Arguments DsetFmapHas {a} {b} {H} {f} {dset} {x}.

Definition downset_fmap {a b} `{poset a} `{poset b} (f : a -> b) (dset : downset a) : downset b := {|
  has := downclose_has (downset_fmap_has f dset);
  downclosed := downclose_has_is_downclosed
|}.

Inductive downset_mult_has {a} `{poset a} (dset0 : downset (downset a)) : a -> Prop :=
| DsetMultHas (dset1 : downset a) {x} (h0 : has dset0 dset1) (h1 : has dset1 x) : downset_mult_has dset0 x.
Arguments DsetMultHas {a} {H} {dset0}.

Definition downset_mult {a} `{poset a} (dset : downset (downset a)) : downset a := {|
  has := downclose_has (downset_mult_has dset);
  downclosed := downclose_has_is_downclosed
|}.

Lemma downset_mult_unit_id {a} `{poset a} : downset_mult (a:=a) ??? downset_unit = id.
unfold compose.
extensionality dset.
apply downset_extensionality.
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
exact DsetUnitHas.
exact ord_refl.
exact H0.
exact ord_refl.
Qed.

Lemma downset_mult_fmap_unit_id {a} `{poset a} : downset_mult (a:=a) ??? downset_fmap downset_unit = id.
unfold compose.
extensionality dset.
apply downset_extensionality.
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
apply OrdDownset.
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
apply (DsetMultHas (downset_unit x)).
exists (downset_unit x).
split.
apply DsetFmapHas.
exact H0.
exact ord_refl.
exists x.
split.
exact DsetUnitHas.
exact ord_refl.
exact ord_refl.
Qed.

Lemma downset_mult_orig_set {a} `{poset a} {ddset : downset (downset a)} {dset : downset a} {x : a} :
  ord dset (downset_mult ddset) -> has dset x -> exists dset1, has ddset dset1 /\ has dset1 x.
intros.
assert (has (downset_mult ddset) x).
exact (downset_inclusion H0 H1).
destruct H2.
destruct H2.
destruct H2.
exists dset1.
split.
exact h0.
exact (downclosed dset1 H3 h1).
Qed.

Lemma mult_subset {a} `{poset a} {ddset : downset (downset a)} {dset : downset a} :
  has ddset dset -> ord dset (downset_mult ddset).
intro.
apply OrdDownset.
intros.
exists x.
split.
apply (DsetMultHas dset).
exact H0.
exact H1.
exact ord_refl.
Qed.

Lemma downset_mult_assoc {a} `{poset a} : downset_mult (a:=a) ??? downset_fmap downset_mult = downset_mult ??? downset_mult.
extensionality dddset.
apply downset_extensionality.
intro.
split.
intro.
exists x.
split.
destruct H0.
destruct H0.
destruct H0.
destruct h0.
destruct H0.
destruct H0.
assert (exists dset2, has x1 dset2 /\ has dset2 x0).
exact (downset_mult_orig_set H2 h1).
destruct H0.
destruct H0.
apply (DsetMultHas x2).
exists x2.
split.
apply (DsetMultHas x1).
exact h.
exact H0.
exact ord_refl.
exact (downclosed x2 H1 H3).
exact ord_refl.
intro.
exists x.
split.
destruct H0.
destruct H0.
destruct H0.
destruct h0.
destruct H0.
destruct H0.
apply (DsetMultHas dset1).
exists (downset_mult dset0).
split.
constructor.
exact h0.
assert (has dset0 dset1).
exact (downclosed dset0 H2 h2).
exact (mult_subset H0).
exact (downclosed dset1 H1 h1).
exact ord_refl.
Qed.