import OTSelector.Reconstruction.FinslerOriginalClockPressureScreen
import OTSelector.Reconstruction.FinslerOriginalRangeClockResamplingData
import OTSelector.Reconstruction.MarkedStationaryValueLegalBlockSubadditivity

/-! The actual original iid pressure hierarchy has one coarse repair constant
and one compact coefficient bound, fixed before all finer coefficient bins
and all original conditional clock laws. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
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


/-- An original coefficient bound chosen before the fine bins bounds every
produced continuous original resampling kernel by twice that same constant. -/
theorem OriginalRangeClockResamplingData.kinetic_bound_of_class_bound
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (fine : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ) {ε η K : ℝ}
    (Rdata : OriginalRangeClockResamplingData C fine z₀ hz₀ f ε η)
    (hε1 : ε ≤ 1) (hK : 0 ≤ K)
    (hbound : ∀ i j v, |C.clockClassKinetic fine z₀ i j v| ≤ K * ∑ l, v l ^ 2) :
    ∀ x y v, |C.originalMaskedClockKinetic fine z₀ x y v| ≤ (2 * K) * ∑ l, v l ^ 2 := by
  intro x y v
  by_cases hxy : C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y)
  · rw [abs_of_nonneg (Rdata.kinetic_nonneg x y v)]
    have hrel := (abs_le.mp (Rdata.relative x y hxy v)).2
    have href := C.clockClassKinetic_nonneg fine z₀ hz₀ (fine.rangeClassify x) (fine.rangeClassify y) v
    have hb := hbound (fine.rangeClassify x) (fine.rangeClassify y) v
    rw [abs_of_nonneg href] at hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hε1) href]
  · simp only [OriginalPopulationCoefficientCore.originalMaskedClockKinetic,hxy,↓reduceIte,abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hK) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Fixed coarse bins supply the complete original iid parent/leaf pressure
comparison. Its constant is uniform in the fine coefficient partition and in
all feasible original supported conditional clock laws. -/
theorem OriginalPopulationCoefficientCore.exists_original_coarse_pressure_grid_bound
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots)
    {range : Set ℝ} (hrange : MeasurableSet range) {gap : ℝ}
    (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap) :
    ∃ K ≥ 0,
    ∀ {width : ℝ} (fine : FiniteScalarBins range width)
      (_hfull : ∀ i j, C.clockClassAllowed fine i j →
        ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
          x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
      (f : M × M →ᵇ ℝ) {ε η : ℝ}
      (_Rdata : OriginalRangeClockResamplingData C fine z₀ hz₀ f ε η) (_hε1 : ε ≤ 1)
      (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
      (_hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
      (_hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
      (π : Measure (range × range)) [IsFiniteMeasure π] (_hπ : Vlasov.IsCoupling π α β)
      (_hgapLaw : ∀ᵐ p ∂π, gap ≤ p.2.val - p.1.val)
      (_hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|)
      (_hq : 4 < finrank ℝ (P C.seedIndex).seed.covector.ker)
      (m : ℕ) (_hm : 0 < m) (r : ℝ≥0) (t : ℝ),
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let mask := fun x y ↦ C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y)
    finiteClassLegalPressure q mask α β r (C.originalMaskedClockKinetic fine z₀)
        (C.originalRangeClockProbe z₀ hz₀ f) t ≤
      ((m ^ q : ℕ) : ℝ) * finiteClassLegalPressure q mask α β (r / (m ^ q : ℝ≥0))
        (C.originalMaskedClockKinetic fine z₀) (C.originalRangeClockProbe z₀ hz₀ f) t +
      legalGridRepairConstant q coarse.count (legalClockTypeCount coarse.count) *
        (2 * K + |t| * ‖f‖) * (r : ℝ) *
        (Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (-(1 / 2))) := by
  obtain ⟨K,hK,hbound⟩ := C.exists_all_clockClassKinetic_bound z₀ hz₀
  refine ⟨K,hK,?_⟩
  intro width fine hfull f ε η Rdata hε1 α β _ _ hα hβ π _ hπ hgapLaw hsep hq m hm r t
  dsimp only
  have heq r := C.fine_clock_pressure_eq_original_scalar fine hwindowGap hfull α β hα hβ hsep
    (finrank ℝ (P C.seedIndex).seed.covector.ker) r
    (C.originalMaskedClockKinetic fine z₀) (C.originalRangeClockProbe z₀ hz₀ f) t
  rw [heq r,heq (r / (m ^ finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ≥0))]
  apply legalMarkedPressure_le_blockScale_add_repair coarse hgap hrange Subtype.val Subtype.val
    measurable_subtype_coe measurable_subtype_coe π α β hπ
    (Filter.Eventually.of_forall fun p ↦ ⟨p.1.property,p.2.property⟩) hgapLaw hsep
    (finrank ℝ (P C.seedIndex).seed.covector.ker) hq m hm r
    (mul_nonneg (by norm_num) hK) (norm_nonneg f)
    (C.measurable_originalMaskedClockKinetic hF hcomplete hu ha hinj fine z₀)
    (Rdata.kinetic_bound_of_class_bound C fine z₀ hz₀ f hε1 hK (hbound fine))
    (fun x y c _ v ↦ ?_)
    (C.measurable_originalRangeClockProbe hF z₀ hz₀ f)
    (C.originalRangeClockProbe_abs_le z₀ hz₀ f)
  change C.originalMaskedClockKinetic fine z₀ x y (c • v) =
    c ^ 2 * C.originalMaskedClockKinetic fine z₀ x y v
  exact C.originalMaskedClockKinetic_homogeneous fine z₀ x y c v

end OTSelector.Reconstruction
