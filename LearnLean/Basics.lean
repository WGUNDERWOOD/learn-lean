import Mathlib

example : 1 + 1 = 2 := by
  rfl

example (a b : ℕ) (h : a = b) : a = b := by
  exact h

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a + a = 2 * c  := by
  rw [h1]
  rw [← h2]
  rw [Nat.two_mul]

example (x y : ℝ) : x ≤ |x| ∧ x + y ≤ |x| + |y| := by
  have hx : x ≤ |x| := le_abs_self x
  have hy : y ≤ |y| := le_abs_self y
  constructor
  · exact hx
  · exact add_le_add hx hy
