import Mathlib

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a + c = b + b := by
   rw [h1]
   rw [← h2]

example (a b : Nat) (h1 : a = b) : a = b ∧ a ≤ b := by
  constructor
  · exact h1
  · rw [h1]
    exact Nat.le_refl b

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a + a = 2 * c := by
  rw [h1]
  rw [← h2]
  rw [Nat.two_mul]

example (x y : Real) : x + y ≤ (abs x) + (abs y) := by
  --have hx : x ≤ |x| := le_abs_self x
  --have hy : y ≤ |y| := le_abs_self y
  --exact add_le_add hx hy
