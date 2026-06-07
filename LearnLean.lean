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

noncomputable def indicator_above (x : Real) (a : Real) : Real :=
  if x >= a then 1 else 0

theorem markov_ineq (n : Nat) (hn: 0 < n)
  (x : Fin n -> Real) (a: Real) (hx: forall i, x i >= 0) (ha: a > 0) :
    mean (fun i => indicator_above (x i) a) <= mean x / a := by
  sorry
