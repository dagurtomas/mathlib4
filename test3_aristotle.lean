/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)
-/

import Mathlib

universe u

open CategoryTheory LightProfinite

/-
Aristotle failed to find a proof.
-/
lemma lightProfinite_injective (S : LightProfinite.{u}) [Nonempty S] : Injective S := by
  sorry