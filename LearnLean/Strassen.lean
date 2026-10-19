import LearnLean.StrassenPolish

open MeasureTheory

namespace Strassen

/-- A coupling with a distance tail bound satisfies the enlargement inequality. -/
theorem enlargement_inequality_of_coupling
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) (π : Measure (E × E)) (ε δ : ℝ)
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = ν)
    (hbound : π {p | ε < dist p.1 p.2} ≤ ENNReal.ofReal δ)
    (B : Set E) (hB : MeasurableSet B) :
    μ B ≤ ν (Metric.cthickening ε B) + ENNReal.ofReal δ := by
  have hsubset : Prod.fst ⁻¹' B ⊆
      Prod.snd ⁻¹' Metric.cthickening ε B ∪ {p : E × E | ε < dist p.1 p.2} := by
    intro p hp
    by_cases hdist : ε < dist p.1 p.2
    · exact Or.inr hdist
    · exact Or.inl (Metric.mem_cthickening_of_dist_le p.2 p.1 ε B hp
        (by simpa only [dist_comm] using le_of_not_gt hdist))
  calc
    μ B = π (Prod.fst ⁻¹' B) := by rw [← hfst, Measure.map_apply measurable_fst hB]
    _ ≤ π (Prod.snd ⁻¹' Metric.cthickening ε B ∪ {p | ε < dist p.1 p.2}) :=
      measure_mono hsubset
    _ ≤ π (Prod.snd ⁻¹' Metric.cthickening ε B) + π {p | ε < dist p.1 p.2} :=
      measure_union_le _ _
    _ ≤ ν (Metric.cthickening ε B) + ENNReal.ofReal δ := by
      rw [← hsnd, Measure.map_apply measurable_snd Metric.isClosed_cthickening.measurableSet]
      exact add_le_add le_rfl hbound

end Strassen

/-- Strassen's coupling theorem for probability measures on a Polish metric space.

If `μ B ≤ ν (B^ε) + δ` for every Borel set `B`, there is a coupling of `μ`
and `ν` under which the coordinates are more than `ε` apart with probability
at most `δ`.

Here `B^ε` is the closed enlargement `Metric.cthickening ε B`: the set of
points whose distance from `B` is at most `ε`. The assumption `BorelSpace E`
means that `MeasurableSet B` expresses that `B` is Borel.

The proof embeds the space in the Hilbert cube and applies the compact
closed-relation coupling theorem, then pulls the resulting measure back.
-/
theorem strassen_coupling
    {E : Type*} [MetricSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hclose : ∀ B : Set E, MeasurableSet B →
      μ B ≤ ν (Metric.cthickening ε B) + ENNReal.ofReal δ) :
    ∃ π : Measure (E × E), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧
      Measure.map Prod.snd π = ν ∧
      π {p | ε < dist p.1 p.2} ≤ ENNReal.ofReal δ := by
  by_cases hlarge : 1 ≤ δ
  · refine ⟨μ.prod ν, inferInstance, by simp, by simp, ?_⟩
    exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal hlarge)
  let K := ℕ → unitInterval
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, he⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := E)
  exact Strassen.metric_coupling_of_compact_embedding (K := K) e he
    μ ν ε δ hε hδ (le_of_not_ge hlarge) hclose
