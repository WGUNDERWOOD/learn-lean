import Mathlib
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
    apply integral_eq_zero_of_ae
    dsimp [μ]
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx
    simp [f, hx]
  rw [← int_f_zero]
  exact dct F f g μ F_measurable g_integrable g_dominates F_converges
