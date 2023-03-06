Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Class poset (a : Type) := mk_poset {
  ord : relation a;
  ord_refl {x} : ord x x;
  ord_trans {x y z} : ord x y -> ord y z -> ord x z;
  ord_antisym {x y} : ord x y -> ord y x -> x = y
}.
Arguments mk_poset {a}.
Arguments ord {a} {poset}.
Arguments ord_refl {a} {poset} {x}.
Arguments ord_trans {a} {poset} {x y z}.
Arguments ord_antisym {a} {poset} {x y}.