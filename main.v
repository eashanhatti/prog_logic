Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Even.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Coq.Init.Nat.
Require Import String.

Open Scope program_scope.

Set Implicit Arguments.

Structure effect_sig : Type := mk_effect_sig {
  label : Type;
  par : label -> Type;
  ar : label -> Type
}.

Definition handler (esig : effect_sig) : Type :=
  forall l : label esig, forall x : par esig l, ar esig l.

Inductive play (esig : effect_sig) (a : Type) : Type :=
| Emp : play esig a
| Ret (x : a) : play esig a
| InvRes (l : label esig) (x : par esig l) (v : ar esig l) (p : play esig a) : play esig a.

Class monad (m : Type -> Type) : Type := {
  funit {a} : a -> m a;
  fmap {a b} : (a -> b) -> m a -> m b;
  mult {a} : m (m a) -> m a;
  mult_funit_id {a} : @mult a ∘ funit = id;
  mult_fmap_funit_id {a} : @mult a ∘ fmap funit = id;
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

Definition play_funit {esig a} (x : a) : play esig a := Ret _ x.
Fixpoint play_mult {a esig} (pp : play esig (play esig a)) : play esig a :=
  match pp with
    | Ret _ p => p
    | Emp _ _ => Emp _ _
    | InvRes l x v p => InvRes l x v (play_mult p)
  end.
Fixpoint play_fmap {a b esig} (f : a -> b) (p : play esig a) : play esig b :=
  match p with
  | Ret _ x => Ret _ (f x)
  | Emp _ _ => Emp _ _
  | InvRes l x v p1 => InvRes l x v (play_fmap f p1)
  end.

Definition strat (esig : effect_sig) (a : Type) : Type := handler esig -> list (play esig a).

Definition strat_funit {esig a} (x : a) : strat esig a := fun _ => [ play_funit x ].
Definition strat_fmap {esig a b} (f : a -> b) (s : strat esig a) : strat esig b := fun h => map (play_fmap f) (s h).
Fixpoint prod {esig a} (p : play esig (strat esig a)) : strat esig a :=
  fun h => match p with
  | Ret _ s => s h
  | Emp _ _ => [ Emp _ _ ]
  | InvRes l x v p1 =>
      let s1 := prod p1
      in map (fun p2 => InvRes l x v p2) (s1 h)
  end.
Definition strat_mult {esig a} (s : strat esig (strat esig a)) : strat esig a :=
  fun h => flat_map (fun l => prod l h) (s h).

Theorem strat_mult_funit_id {esig a} : @strat_mult esig a ∘ strat_funit = id.
Proof.
extensionality s.
extensionality h.
cbv.
change (fix app (l m : list (play esig a)) {struct l} : list (play esig a) :=
          match l with
          | [] => m
          | a0 :: l1 => a0 :: app l1 m
          end) with (@app (play esig a)).
rewrite app_nil_r.
reflexivity.
Qed.

Lemma prod_fmap_funit_funit {esig a} {p : play esig a} : prod (play_fmap strat_funit p) = fun _ => [p].
Proof.
extensionality h.
induction p.
trivial.
simpl.
trivial.
simpl.
rewrite IHp.
trivial.
Qed.


Theorem strat_mult_fmap_funit_id {esig a} : @strat_mult esig a ∘ strat_fmap strat_funit = id.
Proof.
extensionality s.
extensionality h.
unfold compose.
Admitted.

Lemma strat_mult_assoc {esig a} : @strat_mult esig a ∘ strat_fmap strat_mult = strat_mult ∘ strat_mult.
Proof.
Admitted.

Local Instance monad_strat {esig} : monad (strat esig) := {
  funit _ := strat_funit;
  fmap _ _ := strat_fmap;
  mult _ := strat_mult;
  mult_funit_id _ := strat_mult_funit_id;
  mult_fmap_funit_id _ := strat_mult_fmap_funit_id;
  mult_assoc _ := strat_mult_assoc
}.

Definition strat_plus {esig a} (s1 s2 : strat esig a) (h : handler esig) := s1 h ++ s2 h.
Notation "s1 + s2" := (fun h => strat_plus s1 s2 h)
  (at level 50, left associativity).

Definition strat_neu {esig a} : strat esig a := const [].

Theorem strat_plus_neu_l {esig a} {s : strat esig a} : strat_neu + s = s.
Proof.
extensionality h.
cbv.
reflexivity.
Qed.

Theorem strat_plus_neu_r {esig a} {s : strat esig a} : s + strat_neu = s.
Proof.
extensionality h.
cbv.
change (fix app (l m : list (play esig a)) {struct l} : list (play esig a) :=
          match l with
          | [] => m
          | a0 :: l1 => a0 :: app l1 m
          end) with (@app (play esig a)).
rewrite app_nil_r.
reflexivity.
Qed.

Theorem strat_assoc {esig a} {s1 s2 s3 : strat esig a} : s1 + (s2 + s3) = (s1 + s2) + s3.
Proof.
extensionality h.
cbv.
change (fix app (l m : list (play esig a)) {struct l} : list (play esig a) :=
          match l with
          | [] => m
          | a0 :: l1 => a0 :: app l1 m
          end) with (@app (play esig a)).
rewrite app_assoc.
reflexivity.
Qed.

Local Instance additive_monad_strat {esig} : additive_monad (strat esig) := {
  plus a := strat_plus;
  neu a := strat_neu;
  plus_neu_l _ _ := strat_plus_neu_l;
  plus_neu_r _ _ := strat_plus_neu_r;
  plus_assoc a s1 s2 s3 := strat_assoc
}.

Definition strat_bind {esig a b} (act : strat esig a) (k : a -> strat esig b) : strat esig b :=
  strat_mult (strat_fmap k act).
Notation "x <- act ;; k" := (strat_bind act (fun x => k))
  (at level 61, act at next level, right associativity).
Notation "act ;; k" := (strat_bind act (fun _ => k))
  (at level 61, right associativity).

Definition strat_compose {esig a b c} (f : a -> strat esig b) (g : b -> strat esig c) : (a -> strat esig c) :=
    fun x => y <- f x ;; g y.
Notation "f >=> g" := (strat_compose f g)
  (at level 40, left associativity).

Fixpoint strat_star {esig a} (act : strat esig a) (n : nat) : strat esig a :=
  match n with
  | S m => act ;; strat_star act m
  | Z => strat_neu
  end.
(* Notation "act * n" := (strat_star act n)
  (at level 40, left associativity). *)

Definition ret {esig a} := @strat_funit esig a.

Definition skip {esig} : strat esig unit := strat_funit tt.

Definition assert {esig} (b : bool) : strat esig unit :=
  if b then
    strat_funit tt
  else
    strat_neu.

Definition invoke {esig} (l : label esig) (x : par esig l) : strat esig (ar esig l) :=
  fun h =>
  let v := h l x
  in [InvRes l x v (Ret _ v)].

Definition strat_if {esig a} (b : bool) (act1 act2 : strat esig a) : strat esig a :=
  (assert b ;; act1) + (assert (negb b) ;; act2).

Definition run_strat {esig a} (h : handler esig) (s : strat esig a) : list (play esig a) := s h.

Record pair (a : Type) := {
  fst : a;
  snd : a
}.

Definition unit_sig : effect_sig := {|
  label := unit;
  par := const unit;
  ar := const unit;
|}.

Definition nat_sig : effect_sig := {|
  label := unit;
  par := const (pair nat);
  ar := const bool
|}.

Definition nat_handler : handler nat_sig :=
  fun _ p => fst p <? snd p.

Eval compute in
  run_strat
    nat_handler
    (b <- @invoke nat_sig tt {|fst := 33; snd := 22 |} ;;
     strat_if b
      (strat_funit "foo"%string)
      (strat_funit "bar"%string)).

Eval compute in strat_funit "foo"%string + strat_funit "bar"%string.

Eval compute in ret 2.