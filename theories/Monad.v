Class monad (m : Type -> Type) : Type := {
  unit {a} : a -> m a;
  fmap {a b} : (a -> b) -> m a -> m b;
  mult {a} : m (m a) -> m a;
  mult_unit_id {a} : mult (a:=a) ∘ unit = id;
  mult_fmap_unit_id {a} : mult (a:=a) ∘ fmap unit = id;
  mult_assoc {a} : mult (a:=a) ∘ fmap mult = mult ∘ mult
}.