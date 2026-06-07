--import Aesop

--def cirno : String := "Cirno's Perfect Arithmetics Class has begun!"

--example : α → α :=
  --by aesop

import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib

open Nat

theorem infinite_primes : ∀ N : ℕ ,∃ p ≥ N , Nat.Prime p  := by
  intro N
  let M := N.factorial + 1
  let p := Nat.minFac M

  have h0 : Nat.Prime p := by
    refine minFac_prime ?n1
    have : N.factorial > 0 := by exact factorial_pos N
    linarith

  use p
  apply And.intro
  {
    by_contra h
    have h1 : p ∣ Nat.factorial N + 1 := by exact minFac_dvd M
    have h2 : p ∣ Nat.factorial N := by
      refine h0.dvd_factorial.mpr ?_
      exact Nat.le_of_not_ge h

    have h3 : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
    exact Nat.Prime.not_dvd_one h0 h3
  }

  {
    exact h0
  }
