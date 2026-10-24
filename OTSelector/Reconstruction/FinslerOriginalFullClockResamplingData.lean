import OTSelector.Reconstruction.FinslerOriginalRangeClockResamplingData

/-! Actual full original clock resampling retains its endpoint and legality
certificate together with the pressure data, so uniform coarse repair and
true continuous-mark pressure limits use the same fine partition. -/
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

/-- The same actual original fine partition carries all pressure bounds and
its full original endpoint/scalar legality certificate. No second independently
chosen partition is substituted in the coarse-repair argument. -/
theorem OriginalPopulationCoefficientCore.exists_original_full_clock_resampling_data
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    {range : Set ℝ} (hrange : IsCompact range) {width : ℝ} (hwidth : 0 < width)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ Q : FiniteScalarBins range width,
      Nonempty (OriginalRangeClockResamplingData C Q z₀ hz₀ f ε η) ∧
      ∀ i j, C.clockClassAllowed Q i j → ∀ x ∈ Q.cell i, ∀ y ∈ Q.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y := by
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
    probe_error := ?_ }⟩,?_⟩
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


  · intro i j hij x hx y hy
    have h := hmodel i j hij x hx y hy
    exact ⟨h.1,h.2.1,h.2.2.2.1⟩

end OTSelector.Reconstruction
