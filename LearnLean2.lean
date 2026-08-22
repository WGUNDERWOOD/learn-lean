import Mathlib

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a + c = b + b := by
   rw [h1]
   rw [← h2]

example (a b : ℕ) (h1 : a = b) : a = b ∧ a ≤ b := by
  constructor
  · exact h1
  · rw [h1]

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a + a = 2 * c := by
  rw [h1]
  rw [← h2]
  rw [Nat.two_mul]

example (x y : Real) : x + y ≤ |x| + |y| := by
  have hx : x ≤ |x| := le_abs_self x
  have hy : y ≤ |y| := le_abs_self y
  exact add_le_add hx hy

theorem infinitude_of_primes : ∀ n : ℕ, ∃ p : ℕ, n < p ∧ Nat.Prime p := by
  intro n
  let m := Nat.factorial n + 1
  let p := Nat.minFac m
  use p
  constructor
  · by_contra h1
    have h2 := Nat.minFac_dvd m
    have h3 : p ∣ Nat.factorial n := by
      have h4 := Nat.le_of_not_lt h1
      exact Nat.dvd_factorial (Nat.minFac_pos m) h4
    have h5 : p ∣ 1 := by
      rw [Nat.dvd_add_iff_right h3]
      exact h2
    have h6 := Nat.eq_one_of_dvd_one h5
    have h7 : Nat.Prime p := by
      have hh : m ≠ 1 := by
        simp [m]
        exact Nat.factorial_ne_zero n
      exact Nat.minFac_prime hh
    rw [h6] at h7
    exact Nat.prime_one_false h7
  · have h8 : m ≠ 1 := by
      rw [add_ne_right]
      exact Nat.factorial_ne_zero n
    exact Nat.minFac_prime_iff.mpr h8
