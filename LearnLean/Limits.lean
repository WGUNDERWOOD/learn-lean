import Mathlib

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
