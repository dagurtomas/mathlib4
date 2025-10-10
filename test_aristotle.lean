/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma one (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
-/

import Mathlib

lemma one (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  -- By expanding $(a + b)^2$ using the distributive property, we get $a^2 + 2ab + b^2$.
  ring
