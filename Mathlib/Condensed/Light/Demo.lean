import Mathlib

example (x y z : ℝ) : (x + y + z) * (x + y - z) * (x - y + z) * (-x + y + z) =
    2 * x ^ 2 * y ^ 2 + 2 * x ^ 2 * z ^ 2 + 2 * y ^ 2 * z ^ 2 - x ^ 4  - y ^ 4 - z ^ 4 := by
  sorry

example (A B : Prop) : ¬ A ∨ ¬ (¬ B ∧ (¬ A ∨ B)) := by
  sorry

open CategoryTheory

example (C D : Type) [Category C] [Category D]
    (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) (F : C ⥤ D) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  sorry
