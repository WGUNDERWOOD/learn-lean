import Mathlib

noncomputable def mean {n : Nat} (x : Fin n -> Real) : Real :=
  (1 : Real) / n * Finset.sum Finset.univ x

theorem variance_nonneg (n : Nat)
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

theorem mean_order (n: Nat) (x: Fin n -> Real) (y: Fin n -> Real) (h1: forall i, x i <= y i):
  mean x <= mean y := by
    sorry

theorem markov_ineq (n : Nat) (hn: 0 < n)
  (x : Fin n -> Real) (a: Real) (hx: forall i, x i >= 0) (ha: a > 0) :
    mean (fun i => indicator_above (x i) a) <= mean x / a := by
      let y := (fun i => indicator_above (x i) a)
      have h1: (forall i, a * y i <= x i) := by
        intro i
        by_cases h2: x i >= a
        {
          have h3: y i = 1 := by
            dsimp [y, indicator_above]
            simp [h2]
          have h4: a * y i = a := by
            rw [h3]
            simp
          rw [h4]
          exact h2
        }
        {
          have h5: y i = 0 := by
            dsimp [y, indicator_above]
            simp [h2]
          rw [h5]
          simp
          exact hx i
        }
      have h6: (forall i, y i <= x i / a) := by
        intro i
        have h7: a * y i <= x i := by
          exact h1 i
        exact (le_div_iff₀' ha).mpr (h1 i)
      sorry

