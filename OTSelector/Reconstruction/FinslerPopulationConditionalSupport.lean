import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Probability.ConditionalClockSupport
import OTSelector.Geometry.Finsler.CalibratedSeedRecovery
import OTSelector.Geometry.Finsler.SeedSupportEndpoints

/-!
# Actual compact atomless conditional laws on the complete seed

The compact physical carriers and the original physical conditional density give
compact atomless probability laws in every fixed potential clock. Exact geometric
label fibers place both original populations on any selected complete seed curve.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- Translating a real atomless probability with compact support retains all three properties. -/
theorem compact_atomless_probability_clockShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (hcompact : IsCompact μ.support) (u₀ : ℝ) :
    let μ₀ := μ.map (fun s : ℝ ↦ s - u₀)
    IsProbabilityMeasure μ₀ ∧ NullSingletonClass μ₀ ∧ IsCompact μ₀.support ∧
      μ₀.support ⊆ (fun s : ℝ ↦ s - u₀) '' μ.support := by
  have hshift : Measurable (fun s : ℝ ↦ s - u₀) := measurable_id.sub_const u₀
  have hcontinuous : Continuous (fun s : ℝ ↦ s - u₀) := continuous_id.sub continuous_const
  have hprob := Measure.isProbabilityMeasure_map (μ := μ) hshift.aemeasurable
  have hnull : NullSingletonClass (μ.map (fun s : ℝ ↦ s - u₀)) := by
    constructor
    intro x
    rw [Measure.map_apply hshift (measurableSet_singleton x)]
    have hpre : (fun s : ℝ ↦ s - u₀) ⁻¹' {x} = {x + u₀} := by
      ext s
      simp only [mem_preimage, mem_singleton_iff, sub_eq_iff_eq_add]
    rw [hpre, measure_singleton]
  have hsub : (μ.map (fun s : ℝ ↦ s - u₀)).support ⊆
      (fun s : ℝ ↦ s - u₀) '' μ.support := by
    apply Measure.support_subset_of_isClosed (hcompact.image hcontinuous).isClosed
    apply (ae_map_iff hshift.aemeasurable (hcompact.image hcontinuous).measurableSet).mpr
    have hae : ∀ᵐ s ∂μ, s ∈ μ.support := μ.support_mem_ae
    exact hae.mono (fun s hs ↦ mem_image_of_mem _ hs)
  exact ⟨hprob, hnull, (hcompact.image hcontinuous).of_isClosed_subset
    Measure.isClosed_support hsub, hsub⟩

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [TopologicalSpace M] [BorelSpace M] [MeasurableEq Z] in
/-- The scalar conditional distribution is the clock image of the original spatial
conditional distribution on the same geometric label. -/
theorem ae_condDistrib_clock_eq_map_id (η : Measure M) [IsFiniteMeasure η]
    (a : M → Z) {u : M → ℝ} (hu : Measurable u) :
    ∀ᵐ z ∂η.map a, condDistrib u a η z = (condDistrib id a η z).map u := by
  filter_upwards [condDistrib_comp (μ := η) a aemeasurable_id hu] with z hz
  exact hz.trans (Kernel.map_apply _ hu z)

omit [BorelSpace E] in
/-- The actual physical conditional density and compact carrier produce atomless
compact probability laws; every fixed clock shift uses the same almost-everywhere set. -/
theorem PopulationConditionalWindowLaw.ae_compact_atomless_clock
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (ha : Measurable a)
    (hu : let _instCompactClockMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {A : Set M} (hA : IsCompact A) (hηA : ∀ᵐ x ∂η, x ∈ A) :
    ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a η z) ∧
      IsCompact (condDistrib u a η z).support ∧ (condDistrib u a η z).support ⊆ u '' A ∧
      ∀ u₀ : ℝ,
        let μ₀ := (condDistrib u a η z).map (fun s : ℝ ↦ s - u₀)
        IsProbabilityMeasure μ₀ ∧ NullSingletonClass μ₀ ∧ IsCompact μ₀.support ∧
          μ₀.support ⊆ (fun x ↦ u x - u₀) '' A := by
  let _instCompactClockMetric : MetricSpace M := F.metricSpace
  have himage := ae_support_map_condDistrib_subset_compact_image η ha hA hηA hu.continuous
  have hmap := ae_condDistrib_clock_eq_map_id η a hu.continuous.measurable
  rw [hlaw.label_law] at himage hmap
  filter_upwards [hlaw.conditional_law, himage, hmap] with z hden himage hmap
  have hnull : NullSingletonClass (condDistrib u a η z) := by
    rw [← hden]
    infer_instance
  have hsub : (condDistrib u a η z).support ⊆ u '' A := hmap ▸ himage
  have hcompact := (hA.image hu.continuous).of_isClosed_subset Measure.isClosed_support hsub
  refine ⟨hnull, hcompact, hsub, ?_⟩
  intro u₀
  obtain ⟨hprob, hatom, hc, hs⟩ := compact_atomless_probability_clockShift
    (condDistrib u a η z) hcompact u₀
  refine ⟨hprob, hatom, hc, ?_⟩
  intro q hq
  obtain ⟨s, hs, rfl⟩ := hs hq
  obtain ⟨x, hx, rfl⟩ := hsub hs
  exact ⟨x, hx, rfl⟩

omit [BorelSpace E] in
/-- The actual common geometric label fiber gives the original complete seed
clock, simultaneously for every retained seed representing that label. -/
theorem ae_conditional_clock_calibrated_same_seed
    (η : Measure M) [IsFiniteMeasure η] {a : M → Z} (ha : Measurable a)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instConditionalSeedMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (horder : let _instConditionalSeedOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hinterior : let _instConditionalSeedInterior : MetricSpace M := F.metricSpace
      ∀ᵐ x ∂η, x ∈ calibratedInterior u) :
    ∀ᵐ z ∂η.map a, ∀ (S : F.CalibratedLevelSeedPatch u) (w : S.covector.ker),
      w ∈ S.labels → a (S.curve w 0) = z →
        (∀ᵐ s : ℝ ∂condDistrib u a η z, s - S.level ∈ S.calibrationTimes w) ∧
        ∀ u₀ : ℝ, ∀ᵐ q ∂(condDistrib u a η z).map (fun s : ℝ ↦ s - u₀),
          q + u₀ - S.level ∈ S.calibrationTimes w := by
  let _instConditionalSeedMetric : MetricSpace M := F.metricSpace
  have hfiber := ae_condDistrib_mem_carrier_fiber η ha
    (F.measurableSet_calibratedInterior hcomplete hu) hinterior
  have hmap := ae_condDistrib_clock_eq_map_id η a hu.continuous.measurable
  filter_upwards [hfiber, hmap] with z hz hmap
  intro S w hw hwz
  have hclosed : IsClosed {s : ℝ | s - S.level ∈ S.calibrationTimes w} :=
    (S.isClosed_calibrationTimes hF hu hw).preimage (continuous_id.sub continuous_const)
  have hclock : ∀ᵐ s : ℝ ∂condDistrib u a η z, s - S.level ∈ S.calibrationTimes w := by
    rw [hmap]
    apply (ae_map_iff hu.continuous.measurable.aemeasurable hclosed.measurableSet).mpr
    filter_upwards [hz] with x hx
    have heq := S.curve_eq_point_of_same_geometricLabel hF hcomplete hu horder hw hx.1
      (hx.2.trans hwz.symm)
    change u (S.curve w (u x - S.level)) = (S.level : ℝ) + (u x - S.level)
    rw [heq]
    ring
  refine ⟨hclock, ?_⟩
  intro u₀
  have hshift : Measurable (fun s : ℝ ↦ s - u₀) := measurable_id.sub_const u₀
  have hmeas : MeasurableSet {q : ℝ | q + u₀ - S.level ∈ S.calibrationTimes w} :=
    ((S.isClosed_calibrationTimes hF hu hw).preimage
      ((continuous_id.add continuous_const).sub continuous_const)).measurableSet
  apply (ae_map_iff hshift.aemeasurable hmeas).mpr
  simpa only [sub_add_cancel] using hclock

end OTSelector.Reconstruction
