import Mathlib

theorem infinitude_of_primes :
    ∀ n : ℕ, ∃ p : ℕ, p > n ∧ Nat.Prime p := by
  intro n
  let n_fac := Nat.factorial n
  let m := n_fac + 1
  let p := Nat.minFac m
  use p
  have m_neq_one : m ≠ 1 := by
    dsimp [m, n_fac]
    simp
    exact Nat.factorial_ne_zero n
  have p_prime : Nat.Prime p := by
    exact Nat.minFac_prime_iff.mpr m_neq_one
  constructor
  · by_contra not_p_ge_n
    have p_leq_n : p ≤ n := by
      exact Nat.le_of_not_lt not_p_ge_n
    have p_ge_zero : p > 0 := by
      exact Nat.minFac_pos m
    have p_dvd_m : p ∣ m := by
      exact Nat.minFac_dvd m
    have p_dvd_n_fac : p ∣ n_fac := by
      dsimp [n_fac]
      exact Nat.dvd_factorial p_ge_zero p_leq_n
    have p_dvd_one : p ∣ 1 := by
      exact (Nat.dvd_add_iff_right p_dvd_n_fac).mpr p_dvd_m
    have p_eq_1 : p = 1 := by
      exact Nat.eq_one_of_dvd_one p_dvd_one
    exact p_prime.ne_one p_eq_1
  · exact p_prime
