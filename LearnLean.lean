import Mathlib

noncomputable def mean {n : Nat} (x : Fin n -> Real) : Real :=
  (1 : Real) / n * Finset.sum Finset.univ x

theorem variance_nonneg (n : Nat) (hn : 0 < n)
    (x : Fin n -> Real) :
    mean (fun i => (x i - mean x)^2) >= 0 := by
  apply mul_nonneg
  {
    exact Nat.one_div_cast_nonneg n
  }
  {
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg (x i - mean x)
  }
