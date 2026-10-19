import LearnLean.StrassenCompact

open MeasureTheory Topology

namespace Strassen

/-- Transfer the compact coupling construction along a topological embedding. -/
theorem metric_coupling_of_compact_embedding
    {E K : Type*} [MetricSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (e : E → K) (he : IsEmbedding e)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hclose : ∀ B : Set E, MeasurableSet B →
      μ B ≤ ν (Metric.cthickening ε B) + ENNReal.ofReal δ) :
    ∃ π : Measure (E × E), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      π {p | ε < dist p.1 p.2} ≤ ENNReal.ofReal δ := by
  classical
  haveI : Nonempty E := nonempty_of_isProbabilityMeasure μ
  have heM : MeasurableEmbedding e := he.continuous.measurableEmbedding he.injective
  letI : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map heM.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map heM.measurable.aemeasurable
  let ep : E × E → K × K := Prod.map e e
  have hep : IsEmbedding ep := he.prodMap he
  let S : Set (E × E) := {p | dist p.1 p.2 ≤ ε}
  have hS : IsClosed S := isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  let R : Set (K × K) := closure (ep '' S)
  have hR : IsClosed R := isClosed_closure
  have hpre : ep ⁻¹' R = S := by
    rw [← hep.closure_eq_preimage_closure_image, hS.closure_eq]
  have hhall : ∀ A : Set K, IsClosed A →
      μ.map e A ≤ ν.map e (Prod.snd '' (R ∩ Prod.fst ⁻¹' A)) + ENNReal.ofReal δ := by
    intro A hA
    let N := Prod.snd '' (R ∩ Prod.fst ⁻¹' A)
    have hN : IsCompact N := (hR.inter (hA.preimage continuous_fst)).isCompact.image continuous_snd
    rw [Measure.map_apply heM.measurable hA.measurableSet,
      Measure.map_apply heM.measurable hN.measurableSet]
    rw [(hA.measurableSet.preimage heM.measurable).measure_eq_iSup_isCompact μ]
    refine iSup_le fun C => iSup_le fun hCA => iSup_le fun hC => ?_
    refine (hclose C hC.measurableSet).trans (add_le_add (measure_mono ?_) le_rfl)
    intro y hy
    rw [hC.cthickening_eq_biUnion_closedBall hε] at hy
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp hy
    refine ⟨(e x, e y), ⟨?_, hCA hx⟩, rfl⟩
    apply subset_closure
    refine ⟨(x, y), ?_, rfl⟩
    change dist x y ≤ ε
    simpa only [Metric.mem_closedBall, dist_comm] using hxy
  obtain ⟨ρ, hρ, hρfst, hρsnd, hρbad⟩ :=
    coupling_of_closed_set_inequalities_with_error (μ.map e) (ν.map e) R hR δ hδ hδ1 hhall
  letI : IsProbabilityMeasure ρ := hρ
  let r : K → E := heM.invFun
  have hr : Measurable r := heM.measurable_invFun
  have hre : Function.LeftInverse r e := heM.leftInverse_invFun
  let rp : K × K → E × E := Prod.map r r
  have hrp : Measurable rp := hr.prodMap hr
  let π := ρ.map rp
  have hfst : π.map Prod.fst = μ := by
    change (ρ.map rp).map Prod.fst = μ
    rw [Measure.map_map measurable_fst hrp]
    have hcomp : Prod.fst ∘ rp = r ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map hr measurable_fst, hρfst,
      Measure.map_map hr heM.measurable]
    simpa only [Function.LeftInverse.id hre] using (Measure.map_id (μ := μ))
  have hsnd : π.map Prod.snd = ν := by
    change (ρ.map rp).map Prod.snd = ν
    rw [Measure.map_map measurable_snd hrp]
    have hcomp : Prod.snd ∘ rp = r ∘ Prod.snd := rfl
    rw [hcomp, ← Measure.map_map hr measurable_snd, hρsnd,
      Measure.map_map hr heM.measurable]
    simpa only [Function.LeftInverse.id hre] using (Measure.map_id (μ := ν))
  refine ⟨π, Measure.isProbabilityMeasure_map hrp.aemeasurable, hfst, hsnd, ?_⟩
  have hfst_range : ∀ᵐ p ∂ρ, p.1 ∈ Set.range e := by
    have h := ae_map_mem_range e heM.measurableSet_range μ
    rw [← hρfst] at h
    exact (ae_map_iff measurable_fst.aemeasurable heM.measurableSet_range).mp h
  have hsnd_range : ∀ᵐ p ∂ρ, p.2 ∈ Set.range e := by
    have h := ae_map_mem_range e heM.measurableSet_range ν
    rw [← hρsnd] at h
    exact (ae_map_iff measurable_snd.aemeasurable heM.measurableSet_range).mp h
  change ρ.map rp {p | ε < dist p.1 p.2} ≤ ENNReal.ofReal δ
  rw [Measure.map_apply hrp (measurableSet_lt measurable_const (measurable_fst.dist measurable_snd))]
  refine (measure_mono_ae ?_).trans hρbad
  filter_upwards [hfst_range, hsnd_range] with p hp₁ hp₂
  intro hbad hpR
  obtain ⟨x, hx⟩ := hp₁
  obtain ⟨y, hy⟩ := hp₂
  have hepR : ep (x, y) ∈ R := by simpa only [ep, Prod.map, hx, hy] using hpR
  have hxy : dist x y ≤ ε := by
    have : (x, y) ∈ ep ⁻¹' R := hepR
    rwa [hpre] at this
  have hrx : r p.1 = x := hx ▸ hre x
  have hry : r p.2 = y := hy ▸ hre y
  change ε < dist (r p.1) (r p.2) at hbad
  rw [hrx, hry] at hbad
  exact (not_lt_of_ge hxy) hbad

end Strassen
