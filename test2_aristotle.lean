/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma two : IsDiscrete ((LightCondensed.discrete _).obj (ModuleCat.of ℤ ℤ) : LightCondAb)
-/

import Mathlib

open LightCondensed

lemma two : IsDiscrete ((LightCondensed.discrete _).obj (ModuleCat.of ℤ ℤ) : LightCondAb) := by
  -- The constant sheaf with value ℤ is in the essential image of the constant sheaf functor.
  use (ModuleCat.of ℤ ℤ);
  refine' ⟨ _ ⟩;
  -- The constant sheaf is already a sheaf, so its sheafification is itself.
  apply CategoryTheory.Iso.refl
