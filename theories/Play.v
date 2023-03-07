Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Basics.
Open Scope program_scope.
Load "theories/Poset.v".

Record effect_sig := mk_effect_sig {
  label : Type;
  par : label -> Type;
  ar : label -> Type
}.

Lemma cong (a : Type) (b : a -> Type) : forall (x y : a) (f : forall (z : a), b z), x = y -> JMeq (f x) (f y).
intros.
rewrite H.
reflexivity.
Qed.

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
InvRes l x v p -----> l(x) v p
*)
Inductive ord_play {esig a} : relation (play esig a) :=
| EmpPrefix {p} : ord_play Emp p
| RetPrefix {x} : ord_play (Ret x) (Ret x)
| InvPrefix {l x} : ord_play (Inv l x) (Inv l x)
| InvInvResPrefix {p l x v} : ord_play (Inv l x) (InvRes l x v p)
| InvResPrefix {p0 p1 l x v} (ord_p : ord_play p0 p1) : ord_play (InvRes l x v p0) (InvRes l x v p1).

Lemma peel_InvResPrefix {esig a} {l x v} {p0 p1 : play esig a} : ord_play (InvRes l x v p0) (InvRes l x v p1) -> ord_play p0 p1.
intro.
inversion H.
exact ord_p.
Qed.

Lemma pfx_nil_is_nil {esig a} {p : play esig a} : ord_play p Emp -> p = Emp.
Proof.
intro.
inversion H.
reflexivity.
Qed.

Lemma ord_play_refl {esig a} : forall {p : play esig a}, ord_play p p.
fix rec 1.
intro.
destruct p.
exact EmpPrefix.
exact RetPrefix.
exact InvPrefix.
apply InvResPrefix.
exact (rec p).
Qed.

Lemma projT2_eq {A} {F : A -> Type} {x y z} : existT F x y = existT F x z -> y = z.
intro.
assert (JMeq (projT2 (existT F x y)) (projT2 (existT F x z))).
apply (cong {w : A & F w} (F ∘ @projT1 _ _) (existT F x y) (existT F x z) (@projT2 _ _) H).
exact (JMeq_eq H0).
Qed.

Lemma peel_res {esig a l x v} : forall {p0 p1 : play esig a}, ord_play (InvRes l x v p0) p1 -> ord_play (Inv l x) p1.
intros.
inversion H. subst.
assert (x1 = x).
exact (projT2_eq H2).
rewrite H0.
exact InvInvResPrefix.
Qed.

Lemma ord_play_trans {esig a} : forall {p0 p1 p2 : play esig a}, ord_play p0 p1 -> ord_play p1 p2 -> ord_play p0 p2.
fix rec 4.
intros.
induction H.
exact EmpPrefix.
exact H0.
exact H0.
exact (peel_res H0).
inversion H0.
assert (x1 = x).
exact (projT2_eq H3).
assert (v1 = v).
exact (projT2_eq H4).
rewrite H6. rewrite H7.
apply InvResPrefix.
exact (rec _ _ _ H ord_p).
Qed.

Lemma ord_play_antisym {esig a} : forall {p0 p1 : play esig a}, ord_play p0 p1 -> ord_play p1 p0 -> p0 = p1.
fix rec 4.
intros.
destruct p0, p1.
reflexivity.
inversion H0.
inversion H0.
inversion H0.
inversion H.
inversion H.
reflexivity.
inversion H0.
inversion H.
inversion H.
inversion H.
inversion H.
rewrite (projT2_eq H3).
reflexivity.
inversion H0.
inversion H.
inversion H.
inversion H.
inversion H0.
generalize dependent x. generalize dependent x2.
generalize dependent v. generalize dependent v2.
rewrite (eq_sym H6).
intros.
assert (v = v0).
transitivity v2.
exact (eq_sym (projT2_eq H8)).
exact (projT2_eq H4).
assert (x = x0).
transitivity x2.
exact (eq_sym (projT2_eq H7)).
exact (projT2_eq H3).
rewrite H1.
rewrite H10.
f_equal.
rewrite (eq_sym H9).
rewrite H1 in H.
rewrite H10 in H.
assert (ord_play p0 p1).
exact (peel_InvResPrefix H).
assert (p1 = p0).
inversion H.
exact (rec _ _ ord_p ord_p0).
exact (eq_trans H9 (eq_sym H12)).
Qed.

Global Instance play_poset {esig a} : poset (play esig a) := {|
  ord := ord_play;
  ord_refl _ := ord_play_refl;
  ord_trans _ _ _ := ord_play_trans;
  ord_antisym _ _ := ord_play_antisym
|}.