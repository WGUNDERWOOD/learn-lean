import Mathlib

example : 1 + 1 = 2 := by
  rfl

example (a b : ℕ) (h : a = b) : a = b := by
  exact h

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
  let n_fac := Nat.factorial n
  let m := n_fac + 1
  let p := Nat.minFac m
  use p
  have m_neq_one : m ≠ 1 := by
    dsimp [m, n_fac]
    simp
    exact Nat.factorial_ne_zero n
  constructor
  · by_contra not_n_le_p
    have p_dvd_m : p ∣ m := by
      exact Nat.minFac_dvd m
    have p_leq_n : p ≤ n := by
      exact Nat.le_of_not_lt not_n_le_p
    have p_ge_zero : p > 0 := by
      exact Nat.minFac_pos m
    have p_dvd_n_fac : p ∣ n_fac := by
      dsimp [n_fac]
      exact Nat.dvd_factorial p_ge_zero p_leq_n
    have p_dvd_one : p ∣ 1 := by
      exact (Nat.dvd_add_iff_right p_dvd_n_fac).mpr p_dvd_m
    have p_eq_1 : p = 1 := by
      exact Nat.eq_one_of_dvd_one p_dvd_one
    have m_eq_one : m = 1 := by
      exact Nat.minFac_eq_one_iff.mp p_eq_1
    exact Ne.elim m_neq_one m_eq_one
  · exact Nat.minFac_prime_iff.mpr m_neq_one

theorem one_over_x_to_zero : ∀ ε > (0 : ℝ), ∃ x > (0 : ℝ), ∀ y ≥ x, |1/y| ≤ ε := by
  intro ε h_eps
  let x := 1 / ε
  use x
  constructor
  · exact one_div_pos.mpr h_eps
  · intro y y_geq_x
    have x_ge_zero : x > 0 := by
      exact one_div_pos.mpr h_eps
    have y_ge_zero : y > 0 := by
      exact lt_of_lt_of_le x_ge_zero y_geq_x
    have abs_y_eq_y : |y| = y := by
      exact abs_of_pos y_ge_zero
    calc
      |1 / y| = 1 / |y| := by exact abs_one_div y
      _ = 1 / y := by rw [abs_y_eq_y]
    exact (one_div_le h_eps y_ge_zero).mp y_geq_x

-- #find
-- #check
-- K
-- Show some Mathlib theorems, dominated convergence
-- Statlib
-- Curry-Howard
-- Making life easier: aesop, omega, linarith
-- Getting help: leansearch
