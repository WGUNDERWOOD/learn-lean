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
    have p_dvd_m : p ∣ m := by
      exact Nat.minFac_dvd m
    have p_ge_zero : p > 0 := by
      exact Nat.minFac_pos m
    have p_dvd_n_fac : p ∣ n_fac := by
      dsimp [n_fac]
      exact Nat.dvd_factorial p_ge_zero p_leq_n
    have p_dvd_one : p ∣ 1 := by
      exact (Nat.dvd_add_iff_right p_dvd_n_fac).mpr p_dvd_m
    have p_eq_1 : p = 1 := by
      exact Nat.eq_one_of_dvd_one p_dvd_one
    exact p_prime.ne_one p_eq_1
  · exact p_prime

theorem one_over_x_to_zero :
    ∀ ε > (0 : ℝ), ∃ x > (0 : ℝ), ∀ y ≥ x, |1/y| ≤ ε := by
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

open MeasureTheory

theorem dct (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ)
  (μ : Measure ℝ)
  (F_measurable : ∀ (n : ℕ), AEStronglyMeasurable (F n) μ)
  (g_integrable : Integrable g μ)
  (g_dominates : ∀ (n : ℕ), ∀ᵐ (x : ℝ) ∂μ, |F n x| ≤ g x)
  (F_converges : ∀ᵐ (x : ℝ) ∂μ, Filter.Tendsto (fun (n : ℕ) => F n x) Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun (n : ℕ) => ∫ (x : ℝ), F n x ∂μ) Filter.atTop (nhds (∫ (x : ℝ), f x ∂μ)) := by
      exact
        tendsto_integral_of_dominated_convergence g F_measurable g_integrable
        g_dominates F_converges

noncomputable def F (n : ℕ) (x : ℝ) : ℝ :=
  if (0 ≤ x) ∧ (x ≤ 1) then x^n else 0

noncomputable def f (x : ℝ) : ℝ :=
  if (x = 1) then 1 else 0

noncomputable def g (x : ℝ) : ℝ :=
  if (0 ≤ x) ∧ (x ≤ 1) then 1 else 0

noncomputable def μ : Measure ℝ := MeasureTheory.volume

example : Filter.Tendsto (fun (n : ℕ) => ∫ (x : ℝ), F n x ∂μ) Filter.atTop (nhds 0) := by
  have F_measurable : ∀ (n : ℕ), AEStronglyMeasurable (F n) μ := by
    intro n
    apply Measurable.aestronglyMeasurable
    have eq_Fn : F n = (fun x => if x ∈ Set.Icc 0 1 then x^n else 0) := by
      funext x
      exact Real.ext_cauchy rfl
    rw [eq_Fn]
    exact Measurable.ite measurableSet_Icc (by fun_prop) (by fun_prop)
  have g_integrable : Integrable g μ := by
    have eq_g : g = (Set.indicator (Set.Icc 0 1) (fun _ : ℝ => (1 : ℝ))) := by
      unfold g
      funext x
      split
      · rename_i x_in_zero_one
        exact Eq.symm (Set.indicator_of_mem x_in_zero_one fun x => 1)
      · rename_i x_not_in_zero_one
        exact Eq.symm (Set.indicator_of_notMem x_not_in_zero_one fun x => 1)
    rw [eq_g]
    apply IntegrableOn.integrable_indicator
    · refine (integrableOn_const_iff ?_).mpr ?_
      · exact enorm_ne_top
      · right
        dsimp [μ]
        exact measure_Icc_lt_top
    · exact measurableSet_Icc
  have g_dominates : ∀ (n : ℕ), ∀ᵐ (x : ℝ) ∂μ, |F n x| ≤ g x := by
    intro n
    apply Filter.Eventually.of_forall
    intro x
    rw [F]
    dsimp [g, f]
    split
    · rename_i x_in_zero_one
      simp only [abs_pow]
      have abs_x_leq_one : |x| ≤ 1 := by
        rw [abs_of_nonneg x_in_zero_one.1]
        exact x_in_zero_one.2
      have abs_x_geq_zero : |x| ≥ 0 := by
        exact abs_nonneg x
      refine pow_le_one₀ abs_x_geq_zero abs_x_leq_one
    · exact abs_nonpos_iff.mpr rfl
  have F_converges : ∀ᵐ (x : ℝ) ∂μ, Filter.Tendsto (fun (n : ℕ) => F n x) Filter.atTop (nhds (f x)) := by
    apply Filter.Eventually.of_forall
    intro x
    unfold F
    unfold f
    split
    · rename_i x_in_zero_one
      split
      · rename_i x_eq_one
        rw [x_eq_one]
        aesop
      · rename_i not_x_eq_one
        have abs_x_eq_x : |x| = x := by
          apply abs_of_nonneg
          have x_geq_zero : x ≥ 0 := x_in_zero_one.1
          exact RCLike.ofReal_nonneg.mp x_geq_zero
        have x_neq_one : x ≠ 1 := by
          exact Ne.symm (Ne.intro fun a => not_x_eq_one (id (Eq.symm a)))
        have x_leq_1 : x ≤ 1 := x_in_zero_one.2
        have abs_x_le_1 : |x| < 1 := by
          rw [abs_x_eq_x]
          exact Std.lt_of_le_of_ne x_leq_1 not_x_eq_one
        apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        exact abs_x_le_1
    · rename_i not_x_in_zero_one
      aesop
  have int_f_zero : (∫ (x : ℝ), f x ∂μ) = 0 := by
    sorry
  rw [← int_f_zero]
  exact dct F f g μ F_measurable g_integrable g_dominates F_converges
