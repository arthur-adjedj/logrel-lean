class PER (R : A → A → Sort _) where
  sym : ∀ x y, R x y → R y x
  trans : ∀ x y z, R x y → R y z → R x z
