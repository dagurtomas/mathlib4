import Mathlib

lemma prime_sum_squares (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    (∃ x y, p = x ^ 2 + y ^ 2) ↔ p ≡ 1 [MOD 4] := by
  sorry
