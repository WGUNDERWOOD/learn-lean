import Mathlib

/-!
The compact part of Strassen's theorem.

We first turn approximate Hall inequalities into inequalities for integrals,
using the layer-cake formula. Riesz extension and Riesz representation then
produce a measure with the required marginals.

To track the error, we use the disjoint union of the closed relation and the
whole product: mass on the first component is good, and the second component
has mass exactly `δ`. Projecting both components to the product gives the
desired coupling.
-/

open MeasureTheory
open scoped CompactlySupported

namespace Strassen

/-- A positive functional on the image of a linear map extends positively when
that image majorizes the ambient ordered vector space. -/
theorem positive_extension
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [PartialOrder W] [IsOrderedAddMonoid W]
    [Module ℝ W] [PosSMulMono ℝ W]
    (T : V →ₗ[ℝ] W) (F : V →ₗ[ℝ] ℝ)
    (hpos : ∀ v, 0 ≤ T v → 0 ≤ F v)
    (hmajor : ∀ w, ∃ v, 0 ≤ T v + w) :
    ∃ G : W →ₗ[ℝ] ℝ, G.comp T = F ∧ ∀ w, 0 ≤ w → 0 ≤ G w := by
  have hk : T.ker ≤ F.ker := by
    intro v hv
    have hv0 : T v = 0 := hv
    have hp := hpos v (by rw [hv0])
    have hn := hpos (-v) (by simp [hv0])
    simpa using le_antisymm (by simpa using hn) hp
  let F' : T.range →ₗ[ℝ] ℝ :=
    (T.ker.liftQ F hk).comp T.quotKerEquivRange.symm.toLinearMap
  have hF' (v : V) (hv : T v ∈ T.range) : F' ⟨T v, hv⟩ = F v := by
    simp [F']
  let p : W →ₗ.[ℝ] ℝ := ⟨T.range, F'⟩
  obtain ⟨G, hG, hGpos⟩ := riesz_extension (ConvexCone.positive ℝ W) p
    (by
      rintro ⟨w, v, rfl⟩ hw
      change 0 ≤ F' ⟨T v, _⟩
      rw [hF']
      exact hpos v hw)
    (by
      intro w
      obtain ⟨v, hv⟩ := hmajor w
      exact ⟨⟨T v, v, rfl⟩, hv⟩)
  refine ⟨G, ?_, hGpos⟩
  ext v
  exact (hG ⟨T v, v, rfl⟩).trans (hF' v _)

/-- Integrating a uniform error in tail probabilities costs at most the error
times the length of the range where the first function can be positive. -/
theorem integral_le_add_of_tails
    {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : C(X, ℝ)) (v : C(Y, ℝ)) (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hu : ∀ x, u x ≤ a) (hv : ∀ y, 0 ≤ v y)
    (htails : ∀ t : ℝ, μ {x | t ≤ u x} ≤ ν {y | t ≤ v y} + ENNReal.ofReal δ) :
    ∫ x, u x ∂μ ≤ ∫ y, v y ∂ν + δ * a := by
  classical
  let u' : C(X, ℝ) := ⟨fun x => max (u x) 0, u.continuous.max continuous_const⟩
  have hiu : Integrable u' μ :=
    u'.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiv : Integrable v ν :=
    v.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hu0 : 0 ≤ᵐ[μ] u' := Filter.Eventually.of_forall fun x => le_max_right _ _
  have hv0 : 0 ≤ᵐ[ν] v := Filter.Eventually.of_forall hv
  have hlin : (∫⁻ x, ENNReal.ofReal (u' x) ∂μ) ≤
      (∫⁻ y, ENNReal.ofReal (v y) ∂ν) + ENNReal.ofReal (δ * a) := by
    rw [lintegral_eq_lintegral_meas_le μ hu0 hiu.aemeasurable,
      lintegral_eq_lintegral_meas_le ν hv0 hiv.aemeasurable]
    calc
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ν {y | t ≤ v y} +
          (Set.Ioc 0 a).indicator (fun _ => ENNReal.ofReal δ) t := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := ht
        by_cases hta : t ≤ a
        · have hsets : {x | t ≤ u' x} = {x | t ≤ u x} := by
            ext x
            change (t ≤ max (u x) 0) ↔ t ≤ u x
            simp [not_le_of_gt ht0]
          simp only [hsets, Set.indicator_of_mem (show t ∈ Set.Ioc 0 a from ⟨ht, hta⟩)]
          exact htails t
        · have hsets : {x | t ≤ u' x} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            have hux : u' x ≤ a := max_le (hu x) ha
            exact hta (hx.trans hux)
          rw [hsets, measure_empty]
          exact bot_le
      _ = (∫⁻ t in Set.Ioi (0 : ℝ), ν {y | t ≤ v y}) + ENNReal.ofReal (δ * a) := by
        rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Ioc),
          lintegral_indicator_const measurableSet_Ioc,
          Measure.restrict_apply measurableSet_Ioc]
        have hsub : Set.Ioc (0 : ℝ) a ⊆ Set.Ioi 0 := fun _ h => h.1
        rw [Set.inter_eq_left.mpr hsub, Real.volume_Ioc, sub_zero,
          ENNReal.ofReal_mul hδ]
  have hreal : (∫ x, u' x ∂μ) ≤ ∫ y, v y ∂ν + δ * a := by
    have ht := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hiv.lintegral_lt_top.ne, ENNReal.ofReal_ne_top⟩) hlin
    rw [ENNReal.toReal_add hiv.lintegral_lt_top.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (mul_nonneg hδ ha)] at ht
    rw [integral_eq_lintegral_of_nonneg_ae hu0 hiu.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae hv0 hiv.aestronglyMeasurable]
    exact ht
  refine le_trans (integral_mono ?_ hiu (fun x => le_max_left _ _)) hreal
  exact u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The dual criterion allowing mass `δ` outside a closed relation. -/
theorem coupling_of_dual_with_error
    {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (R : Set (X × Y)) (hR : IsClosed R) (δ : ℝ)
    (hdual : ∀ (f : C(X, ℝ)) (g : C(Y, ℝ)) (a : ℝ),
      (∀ p ∈ R, 0 ≤ f p.1 + g p.2) →
      (∀ p : X × Y, 0 ≤ f p.1 + g p.2 + a) →
      0 ≤ ∫ x, f x ∂μ + ∫ y, g y ∂ν + δ * a) :
    ∃ π : Measure (X × Y), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧ π Rᶜ ≤ ENNReal.ofReal δ := by
  classical
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hR.isCompact
  let Z := R ⊕ (X × Y)
  letI : MeasurableSpace Z := borel Z
  letI : BorelSpace Z := ⟨rfl⟩
  let q : Z → X × Y := Sum.elim Subtype.val id
  have hq : Continuous q := continuous_sum_dom.mpr ⟨continuous_subtype_val, continuous_id⟩
  let b : C(Z, ℝ) := ⟨Sum.elim (fun _ => 0) (fun _ => 1),
    continuous_sum_dom.mpr ⟨continuous_const, continuous_const⟩⟩
  let T : ((C(X, ℝ) × C(Y, ℝ)) × ℝ) →ₗ[ℝ] C(Z, ℝ) :=
    { toFun := fun fga =>
        ⟨fun z => fga.1.1 (q z).1 + fga.1.2 (q z).2 + fga.2 * b z,
          ((fga.1.1.continuous.comp (continuous_fst.comp hq)).add
            (fga.1.2.continuous.comp (continuous_snd.comp hq))).add
              (continuous_const.mul b.continuous)⟩
      map_add' := by intros; ext; simp; ring
      map_smul' := by intros; ext; simp; ring }
  have integrableX (f : C(X, ℝ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have integrableY (g : C(Y, ℝ)) : Integrable g ν :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let F : ((C(X, ℝ) × C(Y, ℝ)) × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun fga => ∫ x, fga.1.1 x ∂μ + ∫ y, fga.1.2 y ∂ν + δ * fga.2
      map_add' := by
        intro a b
        simp only [Prod.fst_add, Prod.snd_add, ContinuousMap.coe_add, Pi.add_apply]
        rw [integral_add (integrableX _) (integrableX _),
          integral_add (integrableY _) (integrableY _)]
        ring
      map_smul' := by intros; simp [integral_const_mul]; ring }
  obtain ⟨G, hG, hGpos⟩ := positive_extension T F
    (by
      intro fga hfga
      apply hdual fga.1.1 fga.1.2 fga.2
      · intro p hp
        simpa [T, q, b] using hfga (Sum.inl ⟨p, hp⟩)
      · intro p
        simpa [T, q, b] using hfga (Sum.inr p))
    (by
      intro w
      refine ⟨((ContinuousMap.const X ‖w‖, 0), 0), ?_⟩
      intro z
      change 0 ≤ ‖w‖ + 0 + 0 * b z + w z
      have := w.neg_norm_le_apply z
      linarith)
  let Λ : C_c(Z, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => G f.toContinuousMap
      map_add' := by intros; exact G.map_add _ _
      map_smul' := by intros; exact G.map_smul _ _
      monotone' := by
        intro f g hfg
        have := hGpos (g.toContinuousMap - f.toContinuousMap) (sub_nonneg.mpr hfg)
        simpa only [map_sub, sub_nonneg] using this }
  let ρ : Measure Z := RealRMK.rieszMeasure Λ
  let π : Measure (X × Y) := ρ.map q
  have hi (fga : (C(X, ℝ) × C(Y, ℝ)) × ℝ) :
      ∫ z, T fga z ∂ρ = F fga := by
    let f : C_c(Z, ℝ) := ⟨T fga, HasCompactSupport.of_compactSpace _⟩
    calc
      _ = Λ f := RealRMK.integral_rieszMeasure Λ f
      _ = G (T fga) := rfl
      _ = F fga := LinearMap.congr_fun hG fga
  have hfst : π.map Prod.fst = μ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (f := fun x => f x) measurable_fst.aemeasurable
      f.continuous.aestronglyMeasurable]
    change ∫ p, f p.1 ∂(ρ.map q) = _
    rw [integral_map (μ := ρ) (φ := q) (f := fun p : X × Y => f p.1)
      hq.measurable.aemeasurable (f.continuous.comp continuous_fst).aestronglyMeasurable]
    simpa [T, F] using hi ((f.toContinuousMap, 0), 0)
  have hsnd : π.map Prod.snd = ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (f := fun y => f y) measurable_snd.aemeasurable
      f.continuous.aestronglyMeasurable]
    change ∫ p, f p.2 ∂(ρ.map q) = _
    rw [integral_map (μ := ρ) (φ := q) (f := fun p : X × Y => f p.2)
      hq.measurable.aemeasurable (f.continuous.comp continuous_snd).aestronglyMeasurable]
    simpa [T, F] using hi ((0, f.toContinuousMap), 0)
  haveI : IsProbabilityMeasure (π.map Prod.fst) := hfst.symm ▸ inferInstance
  refine ⟨π, Measure.isProbabilityMeasure_of_map Prod.fst, hfst, hsnd, ?_⟩
  let B : Set Z := Set.range Sum.inr
  have hB : MeasurableSet B := isOpen_range_inr.measurableSet
  have hb : ∫ z, b z ∂ρ = δ := by simpa [T, F] using hi ((0, 0), 1)
  have hbfun : (fun z => b z) = B.indicator (1 : Z → ℝ) := by
    funext z
    cases z <;> simp [B, b]
  rw [hbfun] at hb
  change (∫ z, B.indicator (1 : Z → ℝ) z ∂ρ) = δ at hb
  rw [integral_indicator_one hB] at hb
  have hρB : ρ B = ENNReal.ofReal δ := by
    rw [← hb, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change ρ.map q Rᶜ ≤ ENNReal.ofReal δ
  rw [Measure.map_apply hq.measurable hR.measurableSet.compl, ← hρB]
  apply measure_mono
  intro z hz
  cases z with
  | inl p => exact False.elim (hz p.property)
  | inr p => exact ⟨p, rfl⟩

/-- Approximate Hall inequalities on a compact space give a coupling with at
most `δ` mass outside the specified closed relation. -/
theorem coupling_of_closed_set_inequalities_with_error
    {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (R : Set (X × Y)) (hR : IsClosed R) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hhall : ∀ A : Set X, IsClosed A →
      μ A ≤ ν (Prod.snd '' (R ∩ Prod.fst ⁻¹' A)) + ENNReal.ofReal δ) :
    ∃ π : Measure (X × Y), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧ π Rᶜ ≤ ENNReal.ofReal δ := by
  classical
  apply coupling_of_dual_with_error μ ν R hR δ
  intro f g a hfg hglobal
  haveI : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  obtain ⟨y₀, _, hy₀⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set Y).Nonempty) g.continuous.continuousOn
  let c := g y₀
  let u : C(X, ℝ) := ⟨fun x => -f x - c, f.continuous.neg.sub continuous_const⟩
  let v : C(Y, ℝ) := ⟨fun y => g y - c, g.continuous.sub continuous_const⟩
  have hu : ∀ x, u x ≤ a := by
    intro x
    have := hglobal (x, y₀)
    change -f x - c ≤ a
    dsimp [c]
    linarith
  have hv : ∀ y, 0 ≤ v y := by
    intro y
    exact sub_nonneg.mpr (hy₀ (Set.mem_univ y))
  have htails : ∀ t : ℝ, μ {x | t ≤ u x} ≤ ν {y | t ≤ v y} + ENNReal.ofReal δ := by
    intro t
    refine (hhall {x | t ≤ u x} (isClosed_le continuous_const u.continuous)).trans ?_
    refine add_le_add ?_ le_rfl
    apply measure_mono
    rintro y ⟨⟨x, y⟩, ⟨hxy, hx⟩, rfl⟩
    have := hfg (x, y) hxy
    change t ≤ -f x - c at hx
    change t ≤ g y - c
    linarith
  have iu : Integrable u μ :=
    u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have iv : Integrable v ν :=
    v.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : (∫ x, u x ∂μ) ≤ ∫ y, v y ∂ν + δ * a := by
    by_cases ha : 0 ≤ a
    · exact integral_le_add_of_tails μ ν u v a δ ha hδ hu hv htails
    · have hiu : (∫ x, u x ∂μ) ≤ a := by
        simpa using integral_mono iu (integrable_const a) hu
      have hiv : 0 ≤ ∫ y, v y ∂ν := integral_nonneg hv
      nlinarith
  have if' : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ig : Integrable g ν :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x, -f x - c ∂μ) ≤ ∫ y, g y - c ∂ν + δ * a at hi
  rw [integral_sub (f := fun x => -f x) (g := fun _ => c) if'.neg (integrable_const c),
    integral_sub (f := fun y => g y) (g := fun _ => c) ig (integrable_const c),
    integral_neg] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  linarith

end Strassen
