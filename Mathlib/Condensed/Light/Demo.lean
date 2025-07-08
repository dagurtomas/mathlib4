import Mathlib

namespace Demo

def Odd (n : ℕ) : Prop := ∃ k : ℕ, n = 2 * k + 1

theorem odd_one : Odd 1 := by
  unfold Odd
  use 0

theorem odd_mul_odd (n m : ℕ) (hn : Odd n) (hm : Odd m) : Odd (n * m) := by
  unfold Odd at *
  obtain ⟨k, hk⟩ := hn
  obtain ⟨l, hl⟩ := hm
  rw [hk, hl]
  use k + l + 2 * k * l
  ring

end Demo
