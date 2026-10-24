import OTSelector.Reconstruction.FinslerOriginalRangeClockResamplingData

/-! The actual original continuous scalar-clock model and its finite observed
class approximation both have true pressure limits, with an explicit error. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- Produced original Finsler resampling data give both genuine pressure
limits on the same original continuous scalar-clock laws and an explicit
comparison with their exact finite class observations. -/
theorem OriginalRangeClockResamplingData.exists_pressure_limits
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    {ε η : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (Rdata : OriginalRangeClockResamplingData C Q z₀ hz₀ f ε η)
    (hq : 4 < finrank ℝ (P C.seedIndex).seed.covector.ker)
    (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (π : Measure (range × range)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π α β)
    (hlegal : ∀ᵐ p ∂π, C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2)) :
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let γ := α.map Q.rangeClassify
    let τ := β.map Q.rangeClassify
    let _instγ : IsProbabilityMeasure γ := Measure.isProbabilityMeasure_map Q.measurable_rangeClassify.aemeasurable
    let _instτ : IsProbabilityMeasure τ := Measure.isProbabilityMeasure_map Q.measurable_rangeClassify.aemeasurable
    ∃ p pref : ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q
        (fun x y ↦ C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y)) α β
        (C.originalMaskedClockKinetic Q z₀) (C.originalRangeClockProbe z₀ hz₀ f) L t)
          atTop (𝓝 (p t))) ∧
      (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q) γ τ
        (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) L t) atTop (𝓝 (pref t))) ∧
      ∀ t, |p t - pref t| ≤ ε * (pref t + |t| * ‖f‖) + |t| * η := by
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let γ := α.map Q.rangeClassify
  let τ := β.map Q.rangeClassify
  letI : IsProbabilityMeasure γ := Measure.isProbabilityMeasure_map Q.measurable_rangeClassify.aemeasurable
  letI : IsProbabilityMeasure τ := Measure.isProbabilityMeasure_map Q.measurable_rangeClassify.aemeasurable
  let πclass := π.map (Prod.map Q.rangeClassify Q.rangeClassify)
  have hπclass : Vlasov.IsCoupling πclass γ τ :=
    hπ.map _ _ Q.measurable_rangeClassify Q.measurable_rangeClassify
  have hlegalClass : ∀ᵐ p ∂πclass, C.clockClassAllowed Q p.1 p.2 := by
    exact (ae_map_iff (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify).aemeasurable
      (Set.to_countable {p : Fin Q.count × Fin Q.count | C.clockClassAllowed Q p.1 p.2}).measurableSet).mpr hlegal
  have hnested : ∀ j j', (∀ k, C.clockClassAllowed Q j k → C.clockClassAllowed Q j' k) ∨
      (∀ k, C.clockClassAllowed Q j' k → C.clockClassAllowed Q j k) := C.clockClassAllowed_rows_nested Q
  have hk := C.measurable_originalMaskedClockKinetic hF hcomplete hu ha hinj Q z₀
  have hprobe := C.measurable_originalRangeClockProbe (range := range) hF z₀ hz₀ f
  obtain ⟨p,hp,_,_⟩ := exists_finiteClassLegalScalePressure_pullback_limit_of_nested q hq
    (C.clockClassAllowed Q) hnested α β Q.measurable_rangeClassify Q.measurable_rangeClassify π hπ hlegal
    Rdata.kineticConstant_nonneg (norm_nonneg f) hk Rdata.kinetic_nonneg Rdata.kinetic_bound
    (fun x y c _ v ↦ C.originalMaskedClockKinetic_homogeneous Q z₀ x y c v)
    hprobe (C.originalRangeClockProbe_abs_le z₀ hz₀ f)
  obtain ⟨Kref,hKref,hrefbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  obtain ⟨pref,hpref,_,_⟩ := exists_finiteClassLegalScalePressure_limit_of_nested
    (C.clockClassAllowed Q) hnested γ τ πclass hπclass hlegalClass q hq
    (kin := C.clockClassKinetic Q z₀) hKref (norm_nonneg f)
    (C.measurable_clockClassKinetic Q z₀) (C.clockClassKinetic_nonneg Q z₀ hz₀) hrefbound
    (fun j k c _ v ↦ C.clockClassKinetic_homogeneous Q z₀ j k c v)
    (C.clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f)
  refine ⟨p,pref,hp,hpref,?_⟩
  intro t
  have hbound (L : ℝ) (hL : 0 < L) :
      |finiteClassLegalScalePressure q
          (fun x y ↦ C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y)) α β
          (C.originalMaskedClockKinetic Q z₀) (C.originalRangeClockProbe z₀ hz₀ f) L t -
        finiteClassLegalScalePressure q (C.clockClassAllowed Q) γ τ
          (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) L t| ≤
      ε * (finiteClassLegalScalePressure q (C.clockClassAllowed Q) γ τ
        (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) L t + |t| * ‖f‖) + |t| * η := by
    have hV : 0 < L ^ q := pow_pos hL q
    have hb := finiteClassLegalPressure_resampling_abs_sub_le q (C.clockClassAllowed Q) hnested
      α β γ τ Q.measurable_rangeClassify Q.measurable_rangeClassify rfl rfl (Real.toNNReal (L ^ q))
      (kin := C.originalMaskedClockKinetic Q z₀) (reference := C.clockClassKinetic Q z₀)
      Rdata.kineticConstant_nonneg hKref (norm_nonneg f) (norm_nonneg f) hε0 hε1 hη hk
      (C.measurable_clockClassKinetic Q z₀) (fun x y _ ↦ Rdata.kinetic_bound x y)
      (fun j k _ ↦ hrefbound j k) (C.originalRangeClockProbe z₀ hz₀ f) (C.clockClassProbe Q z₀ hz₀ f)
      hprobe (fun x y _ ↦ C.originalRangeClockProbe_abs_le z₀ hz₀ f x y)
      (fun j k _ ↦ C.clockClassProbe_abs_le Q z₀ hz₀ f j k) Rdata.relative Rdata.probe_error t
    rw [Real.coe_toNNReal _ hV.le] at hb
    simp only [finiteClassLegalScalePressure,hL,↓reduceIte]
    rw [← sub_div,abs_div,abs_of_pos hV]
    apply (div_le_iff₀ hV).mpr
    apply hb.trans_eq
    field_simp [hV.ne']
  apply le_of_tendsto_of_tendsto (((hp t).sub (hpref t)).abs)
    ((((hpref t).add_const (|t| * ‖f‖)).const_mul ε).add_const (|t| * η))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact hbound L hL


/-- Actual original Finsler geometry produces an arbitrarily accurate scalar
clock resampling before the original clock laws are chosen. For every actual
feasible original law supported by its retained mask, both pressure limits and
their quantitative comparison follow without analytic callbacks. -/
theorem OriginalPopulationCoefficientCore.exists_original_clock_resampling_pressures
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    {range : Set ℝ} (hrange : IsCompact range) {width : ℝ} (hwidth : 0 < width)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η)
    (hq : 4 < finrank ℝ (P C.seedIndex).seed.covector.ker) :
    ∃ Q : FiniteScalarBins range width,
      ∀ (α β : ProbabilityMeasure range) (π : ProbabilityMeasure (range × range))
        (_hπ : Vlasov.IsCoupling (π : Measure (range × range)) (α : Measure range) (β : Measure range))
        (_hlegal : ∀ᵐ p ∂(π : Measure (range × range)), C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2)),
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let γ := (α : Measure range).map Q.rangeClassify
    let τ := (β : Measure range).map Q.rangeClassify
    let _instγ : IsProbabilityMeasure γ := Measure.isProbabilityMeasure_map Q.measurable_rangeClassify.aemeasurable
    let _instτ : IsProbabilityMeasure τ := Measure.isProbabilityMeasure_map Q.measurable_rangeClassify.aemeasurable
    ∃ p pref : ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q
        (fun x y ↦ C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y)) (α : Measure range) (β : Measure range)
        (C.originalMaskedClockKinetic Q z₀) (C.originalRangeClockProbe z₀ hz₀ f) L t)
          atTop (𝓝 (p t))) ∧
      (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q) γ τ
        (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) L t) atTop (𝓝 (pref t))) ∧
      ∀ t, |p t - pref t| ≤ ε * (pref t + |t| * ‖f‖) + |t| * η := by
  obtain ⟨Q,⟨Rdata⟩⟩ := C.exists_original_range_clock_resampling_data
    hF hcomplete hu ha hinj z₀ hz₀ f hrange hwidth hε hε1 hη
  refine ⟨Q,?_⟩
  intro α β π hπ hlegal
  exact OriginalRangeClockResamplingData.exists_pressure_limits C hF hcomplete hu ha hinj Q z₀ hz₀ f
    hε.le hε1 hη.le Rdata hq (α : Measure _) (β : Measure _) (π : Measure _) hπ hlegal

end OTSelector.Reconstruction
