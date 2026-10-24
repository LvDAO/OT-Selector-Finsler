import OTSelector.Reconstruction.FinslerOriginalScalarRangeClockModel

/-! The actual original Finsler coefficient and physical probe produce all
continuous-clock versus finite-class resampling bounds on their original range. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- Bounds produced from the original coefficient at one original retained root.
All fields refer to its actual scalar clocks and original class mask. -/
structure OriginalRangeClockResamplingData
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ) (ε η : ℝ) where
  kineticConstant : ℝ
  kineticConstant_nonneg : 0 ≤ kineticConstant
  kinetic_nonneg : ∀ x y v, 0 ≤ C.originalMaskedClockKinetic Q z₀ x y v
  kinetic_bound : ∀ x y v,
    |C.originalMaskedClockKinetic Q z₀ x y v| ≤ kineticConstant * ∑ l, v l ^ 2
  relative : ∀ x y, C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y) → ∀ v,
    |C.originalMaskedClockKinetic Q z₀ x y v -
      C.clockClassKinetic Q z₀ (Q.rangeClassify x) (Q.rangeClassify y) v| ≤
      ε * C.clockClassKinetic Q z₀ (Q.rangeClassify x) (Q.rangeClassify y) v
  probe_error : ∀ x y, C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y) →
    |C.originalRangeClockProbe z₀ hz₀ f x y -
      C.clockClassProbe Q z₀ hz₀ f (Q.rangeClassify x) (Q.rangeClassify y)| ≤ η

/-- Arbitrarily accurate continuous-clock resampling data are produced from the
actual original Finsler coefficient and bounded continuous physical probe.
No additional clock-law or geometric hypothesis is introduced. -/
theorem OriginalPopulationCoefficientCore.exists_original_range_clock_resampling_data
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    {range : Set ℝ} (hrange : IsCompact range) {width : ℝ} (hwidth : 0 < width)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ Q : FiniteScalarBins range width, Nonempty (OriginalRangeClockResamplingData C Q z₀ hz₀ f ε η) := by
  obtain ⟨Q,hmodel⟩ := C.exists_full_clockClass_model_with_endpoints
    hF hcomplete hu ha hinj z₀ hz₀ f f.continuous hrange hwidth hε hη
  obtain ⟨K,hK,hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  have hrel (x y : range) (hxy : C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y))
      (v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) :
      |C.originalMaskedClockKinetic Q z₀ x y v -
        C.clockClassKinetic Q z₀ (Q.rangeClassify x) (Q.rangeClassify y) v| ≤
        ε * C.clockClassKinetic Q z₀ (Q.rangeClassify x) (Q.rangeClassify y) v := by
    simp only [OriginalPopulationCoefficientCore.originalMaskedClockKinetic,hxy,↓reduceIte]
    exact (hmodel _ _ hxy x.val (Q.rangeClassify_mem x) y.val (Q.rangeClassify_mem y)).2.2.2.2.1 v
  have hnonneg (x y : range) (v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) :
      0 ≤ C.originalMaskedClockKinetic Q z₀ x y v := by
    by_cases hxy : C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y)
    · have hr := (abs_le.mp (hrel x y hxy v)).1
      have href := C.clockClassKinetic_nonneg Q z₀ hz₀ (Q.rangeClassify x) (Q.rangeClassify y) v
      nlinarith [mul_nonneg (sub_nonneg.mpr hε1) href]
    · simp only [OriginalPopulationCoefficientCore.originalMaskedClockKinetic,hxy,↓reduceIte,le_refl]
  refine ⟨Q,⟨{
    kineticConstant := (1 + ε) * K
    kineticConstant_nonneg := mul_nonneg (by linarith) hK
    kinetic_nonneg := hnonneg
    kinetic_bound := ?_
    relative := hrel
    probe_error := ?_ }⟩⟩
  · intro x y v
    by_cases hxy : C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y)
    · rw [abs_of_nonneg (hnonneg x y v)]
      have hr := (abs_le.mp (hrel x y hxy v)).2
      have hupper : C.originalMaskedClockKinetic Q z₀ x y v ≤
          (1 + ε) * C.clockClassKinetic Q z₀ (Q.rangeClassify x) (Q.rangeClassify y) v := by
        nlinarith only [hr]
      have hb := mul_le_mul_of_nonneg_left (hbound (Q.rangeClassify x) (Q.rangeClassify y) v)
        (by linarith : 0 ≤ 1 + ε)
      have href := C.clockClassKinetic_nonneg Q z₀ hz₀ (Q.rangeClassify x) (Q.rangeClassify y) v
      rw [abs_of_nonneg href] at hb
      exact (hupper.trans hb).trans_eq (by ring)
    · simp only [OriginalPopulationCoefficientCore.originalMaskedClockKinetic,hxy,↓reduceIte,abs_zero]
      exact mul_nonneg (mul_nonneg (by linarith) hK) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  · intro x y hxy
    simpa only [OriginalPopulationCoefficientCore.originalRangeClockProbe] using
      (hmodel _ _ hxy x.val (Q.rangeClassify_mem x) y.val (Q.rangeClassify_mem y)).2.2.2.2.2


/-- Each produced original retained clock mask has a positive quadratic lower
bound when the chosen approximation error is below one. The bound is a
consequence of original compact-core geometry, rather than an imposed global
rank or density hypothesis. -/
theorem OriginalRangeClockResamplingData.exists_legal_kinetic_lower_bound
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ) {ε η : ℝ}
    (Rdata : OriginalRangeClockResamplingData C Q z₀ hz₀ f ε η) (hε1 : ε < 1) :
    ∃ m > 0, ∀ x y, C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y) → ∀ v,
      m * ‖v‖ ^ 2 ≤ C.originalMaskedClockKinetic Q z₀ x y v := by
  obtain ⟨m,hm,hlower⟩ := C.exists_clockClassKinetic_lower_bound Q z₀ hz₀
  refine ⟨(1 - ε) * m,mul_pos (sub_pos.mpr hε1) hm,?_⟩
  intro x y hxy v
  have hrel := (abs_le.mp (Rdata.relative x y hxy v)).1
  have hlo := mul_le_mul_of_nonneg_left
    (hlower (Q.rangeClassify x) (Q.rangeClassify y) hxy v) (sub_pos.mpr hε1).le
  nlinarith only [hrel,hlo]

/-- Finite original weighted kinetic energy on a produced retained mask gives
the actual displacement second moment on the same measure. No second-moment
assumption is added to the matching or the original clock law. -/
theorem OriginalRangeClockResamplingData.integrable_displacement_sq_of_kinetic
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ) {ε η : ℝ}
    (Rdata : OriginalRangeClockResamplingData C Q z₀ hz₀ f ε η) (hε1 : ε < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → range) (v : Ω → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (hv : Measurable v)
    (hlegal : ∀ᵐ w ∂μ, C.clockClassAllowed Q (Q.rangeClassify (x w)) (Q.rangeClassify (y w)))
    (hkin : Integrable (fun w ↦ C.originalMaskedClockKinetic Q z₀ (x w) (y w) (v w)) μ) :
    Integrable (fun w ↦ ‖v w‖ ^ 2) μ := by
  obtain ⟨m,hm,hlower⟩ := Rdata.exists_legal_kinetic_lower_bound C Q z₀ hz₀ f hε1
  apply (hkin.const_mul m⁻¹).mono' (hv.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [hlegal] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change ‖v w‖ ^ 2 ≤ m⁻¹ * C.originalMaskedClockKinetic Q z₀ (x w) (y w) (v w)
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hm).mpr
  simpa only [mul_comm] using hlower (x w) (y w) hw (v w)

end OTSelector.Reconstruction
