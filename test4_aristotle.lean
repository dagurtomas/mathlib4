/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma prime_sum_squares (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    (∃ x y, p = x ^ 2 + y ^ 2) ↔ p ≡ 1 [MOD 4]
-/

import Mathlib

lemma prime_sum_squares (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    (∃ x y, p = x ^ 2 + y ^ 2) ↔ p ≡ 1 [MOD 4] := by
  -- By Fermat's theorem on sums of two squares, an odd prime $p$ can be written as $x^2 + y^2$ if and only if $p \equiv 1 \pmod{4}$.
  apply Iff.intro;
  · -- If $p = x^2 + y^2$, then considering the equation modulo 4, we can analyze the possible values of $x^2$ and $y^2$.
    intro h
    obtain ⟨x, y, hxy⟩ := h
    have h_mod : (x^2 + y^2) % 4 = p % 4 := by
      -- Since $p = x^2 + y^2$, we have $(x^2 + y^2) \mod 4 = p \mod 4$.
      rw [hxy];
    rcases Nat.even_or_odd' x with ⟨ x, rfl | rfl ⟩ <;>
    rcases Nat.even_or_odd' y with ⟨ y, rfl | rfl ⟩ <;>
    ring_nf <;>
    norm_num [ Nat.ModEq, Nat.add_mod, Nat.mul_mod ] at * ;
    aesop;
    · exact absurd ho ( by simp +decide [ parity_simps ] );
    · -- Simplify the expression in h_mod to get the result.
      ring_nf at h_mod; norm_num at h_mod; exact h_mod.symm;
    · -- Expanding the squares and simplifying modulo 4, we get:
      have h_expand : p = 4 * (x^2 + x + y^2) + 1 := by
        -- Expanding the right-hand side of the equation $p = (2x + 1)^2 + (2y)^2$ gives $p = 4x^2 + 4x + 1 + 4y^2$.
        rw [hxy]
        ring;
      norm_num [ h_expand, Nat.add_mod, Nat.mul_mod ];
    · -- Expanding the squares, we get $p = 4(x^2 + x + y^2 + y) + 2$, which is even. But $p$ is odd, leading to a contradiction.
      have h_even : p % 2 = 0 := by
        rw [ hxy ] ; ring_nf; norm_num [ Nat.add_mod, Nat.mul_mod ] ;
      -- Since p is both even and odd, this is a contradiction.
      exfalso; exact absurd h_even (by rw [Nat.odd_iff] at ho; aesop);
  · -- By Fermat's theorem on sums of two squares, if $p \equiv 1 \pmod{4}$, then $p$ can be written as $x^2 + y^2$ for some integers $x$ and $y$.
    have h_fermat : Nat.Prime p → p % 4 = 1 → ∃ x y : ℕ, p = x^2 + y^2 := by
      intro hp h; have := Fact.mk hp; have := @Nat.Prime.sq_add_sq p; aesop;
    exact h_fermat hp
