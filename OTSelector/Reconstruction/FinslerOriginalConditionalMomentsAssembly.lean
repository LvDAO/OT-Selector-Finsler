import OTSelector.Reconstruction.FinslerOriginalClockSupportBounds
import OTSelector.Reconstruction.FinslerOriginalConditionalMoments

/-!
# Embedding conditional clock support bounds into a full conditional-moment datum

`FinslerOriginalClockSupportBounds` derived `ConditionalClockSupportBounds` for the
conditional clock laws from the raw Poisson input data.  This file embeds those bounds
into the full `OriginalSeedConditionalMoments` datum, so that the clock support stops
being an external hypothesis of the legal input construction.

* `ae_clock_mem_Ioo_of_support_bounds_of_atomless`: the a.e. interior membership
  required by a compact atomless clock support follows from the support bounds and
  atomlessness of the clock law.
* `compactAtomlessClockSupport_of_conditionalSupportBounds`: a compact atomless clock
  support is assembled from the compact support bound, probability, atomlessness and
  the support bound of one conditional clock law.
* `commonSeedSupportSpan_of_conditionalSupportBounds`: the common seed support span
  of `OriginalSeedConditionalMoments` is assembled from the two clock supports and
  the span/calibration data of the calibrated seed patch.
* `nonempty_originalSeedConditionalMoments_of_clockSupportBounds`: composing with
  `originalSeedConditionalMoments_of_supported_comparison`, a full conditional-moment
  datum exists as soon as the phase-jet comparison and the physical density data are
  supplied; the clock support itself is derived from the conditional support bounds.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
  Matrix Module Manifold OTSelector.PointProcess OTSelector.Geometry
  ContinuousFinslerNorm OTSelector.Probability
open scoped Topology ContDiff BigOperators Matrix.Norms.Operator ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace OTSelector.Reconstruction

/-! ## A.e. interior membership from support bounds and atomlessness -/

/-- If a clock law has no atoms and its support lies in the closed clock interval
`[offset + lo, offset + hi]`, then almost every clock lies in the open interval. -/
theorem ae_clock_mem_Ioo_of_support_bounds_of_atomless
    {μ : Measure ℝ} [NullSingletonClass μ] {offset lo hi : ℝ}
    (hbounds : ∀ x ∈ μ.support, x - offset ∈ Set.Icc lo hi) :
    ∀ᵐ x ∂μ, x - offset ∈ Set.Ioo lo hi := by
  rw [ae_iff]
  have hsub : {x : ℝ | ¬ (x - offset ∈ Set.Ioo lo hi)} ⊆
      μ.supportᶜ ∪ ({offset + lo} ∪ {offset + hi}) := by
    intro x hx
    by_cases hxs : x ∈ μ.support
    · have hb := hbounds x hxs
      rw [Set.mem_Icc] at hb
      simp only [Set.mem_ofPred_eq, Set.mem_Ioo, not_and_or] at hx
      rcases hx with hx | hx
      · right; left
        simp only [Set.mem_singleton_iff]
        linarith
      · right; right
        simp only [Set.mem_singleton_iff]
        linarith
    · exact Or.inl hxs
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff]
  refine ⟨measure_compl_support_eq_zero μ, ?_⟩
  rw [measure_union_null_iff]
  exact ⟨by simp, by simp⟩

/-! ## Compact atomless clock supports from the conditional support bounds -/

/-- A compact atomless clock support of one original conditional clock law, from its
compact support, probability, atomlessness and clock support bound. -/
theorem compactAtomlessClockSupport_of_conditionalSupportBounds
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {offset lo hi : ℝ} (hcompact : IsCompact μ.support)
    (hbounds : ∀ x ∈ μ.support, x - offset ∈ Set.Icc lo hi) :
    CompactAtomlessClockSupport μ offset lo hi where
  probability := inferInstance
  atomless := inferInstance
  compact := hcompact
  support_bounds := hbounds
  ae_open := ae_clock_mem_Ioo_of_support_bounds_of_atomless hbounds

/-! ## The common seed support span from the two clock supports -/

section SpanAssembly

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [NullSingletonClass μ] [NullSingletonClass ν]
  {lo hi : ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The common seed support span of the conditional-moment datum assembled from the
two original conditional clock supports and the calibrated span data. -/
theorem commonSeedSupportSpan_of_conditionalSupportBounds
    (hlt : lo < hi)
    (hcompactμ : IsCompact μ.support) (hcompactν : IsCompact ν.support)
    (hsource_bounds : ∀ x ∈ μ.support, x - (S.level : ℝ) ∈ Set.Icc lo hi)
    (htarget_bounds : ∀ x ∈ ν.support, x - (S.level : ℝ) ∈ Set.Icc lo hi)
    (hleft : (S.level : ℝ) + lo ∈ μ.support ∪ ν.support)
    (hright : (S.level : ℝ) + hi ∈ μ.support ∪ ν.support)
    (hcalibrated : Set.Icc lo hi ⊆ S.calibrationTimes w)
    (hcurve : Continuous (S.curve w)) :
    CommonSeedSupportSpan S w μ ν lo hi where
  lt := hlt
  left_mem_support := hleft
  right_mem_support := hright
  source := compactAtomlessClockSupport_of_conditionalSupportBounds hcompactμ
    hsource_bounds
  target := compactAtomlessClockSupport_of_conditionalSupportBounds hcompactν
    htarget_bounds
  calibrated := hcalibrated
  curve_continuous := hcurve

end SpanAssembly

/-! ## The full conditional-moment datum -/

section DatumAssembly

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [NullSingletonClass μ] [NullSingletonClass ν]
  {lo hi : ℝ} {ρ₀ ρ₁ : M → ℝ} {v : M → E → ℝ} {c : ℝ≥0∞}

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] in
/-- A full `OriginalSeedConditionalMoments` datum exists from the conditional clock
support bounds and the remaining physical seed data.  The phase-jet comparison and the
physical density data are still supplied as hypotheses; the clock support itself is
derived from the compact conditional clock supports. -/
theorem nonempty_originalSeedConditionalMoments_of_clockSupportBounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hcomparison : HasActiveSeedComparison S w)
    (hlt : lo < hi)
    (hcompactμ : IsCompact μ.support) (hcompactν : IsCompact ν.support)
    (hsource_bounds : ∀ x ∈ μ.support, x - (S.level : ℝ) ∈ Set.Icc lo hi)
    (htarget_bounds : ∀ x ∈ ν.support, x - (S.level : ℝ) ∈ Set.Icc lo hi)
    (hleft : (S.level : ℝ) + lo ∈ μ.support ∪ ν.support)
    (hright : (S.level : ℝ) + hi ∈ μ.support ∪ ν.support)
    (hcalibrated : Set.Icc lo hi ⊆ S.calibrationTimes w)
    (hcurve : Continuous (S.curve w))
    (hρ₀ : Continuous ρ₀) (hρ₁ : Continuous ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x)
    (hdensity₀ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) ρ₀ v c.toReal)
    (hdensity₁ : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x - S.level)) ρ₁ v c.toReal) :
    Nonempty (OriginalSeedConditionalMoments S w μ ν) :=
  originalSeedConditionalMoments_of_supported_comparison hF hw hcomparison
    (commonSeedSupportSpan_of_conditionalSupportBounds hlt hcompactμ hcompactν
      hsource_bounds htarget_bounds hleft hright hcalibrated hcurve)
    hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg hv hv0 hdensity₀ hdensity₁

end DatumAssembly

end OTSelector.Reconstruction

end
