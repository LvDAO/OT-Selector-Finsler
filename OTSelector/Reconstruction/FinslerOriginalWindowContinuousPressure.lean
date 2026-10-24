import OTSelector.Reconstruction.FinslerOriginalWindowContinuousClockLaw
import OTSelector.Reconstruction.FinslerOriginalRangeClockResamplingPressure

/-! The actual original conditional pair law, rather than an assumed auxiliary
clock coupling, supplies both continuous and finite-observation pressures. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The continuous law comes from the original conditional coupling on the
stored window. Its finite observation is exactly the physical reference class
law; all pressure limits and comparison bounds are then produced internally. -/
theorem PopulationLocalPressureCore.exists_original_window_continuous_pressure
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width) (f : M × M →ᵇ ℝ)
    {ε probeError : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hprobe : 0 ≤ probeError)
    (Rdata : OriginalRangeClockResamplingData (D.haar.continuous.coefficient i) Q
      ref.val ref.property f ε probeError)
    (hq : 4 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    {η : ℝ} (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    ∃ π : Measure (range × range), IsProbabilityMeasure π ∧
      π.map (Prod.map Subtype.val Subtype.val) = γ ref.val ∧
      let C := D.haar.continuous.coefficient i
      let q := finrank ℝ (P C.seedIndex).seed.covector.ker
      let retained := π.restrict
        {p | C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2)}
      let law := normalizedFiniteLaw retained
      let P₀ := D.originalWindowReferenceWeights γ gap range i ref Q η
      ∃ originalLaw : ProbabilityMeasure (range × range), (originalLaw : Measure _) = law ∧
      let weightsData := D.originalWindowReferenceWeights_mass γ gap range i ref Q hη hgap hδ hδ1
      let classLaw := clockClassJointProbability P₀ weightsData.1 weightsData.2.2.2
      let α := originalLaw.map measurable_fst.aemeasurable
      let β := originalLaw.map measurable_snd.aemeasurable
      let αclass := classLaw.map measurable_fst.aemeasurable
      let βclass := classLaw.map measurable_snd.aemeasurable
      1 - δ.toReal ≤ retained.real univ ∧
      (∑ j, ∑ k, P₀ j k) = ((1 - η) * D.rootIntensity i ref.val) * retained.real univ ∧
      ∃ p pref : ℝ → ℝ,
        (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q
          (fun x y ↦ C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y)) (α : Measure _) (β : Measure _)
          (C.originalMaskedClockKinetic Q ref.val) (C.originalRangeClockProbe ref.val ref.property f) L t)
            atTop (𝓝 (p t))) ∧
        (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q) (αclass : Measure _) (βclass : Measure _)
          (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) L t)
            atTop (𝓝 (pref t))) ∧
        ∀ t, |p t - pref t| ≤ ε * (pref t + |t| * ‖f‖) + |t| * probeError := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨π,hπ,hmap,hlower,hlaw,hobserve,hmass⟩ :=
    D.exists_original_window_continuous_clock_law hrange γ gap i ref Q hη hgap hδ hδ1
  let C := D.haar.continuous.coefficient i
  let retained := π.restrict
    {p | C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2)}
  let law := normalizedFiniteLaw retained
  let P₀ := D.originalWindowReferenceWeights γ gap range i ref Q η
  haveI : IsProbabilityMeasure law := hlaw
  haveI : IsProbabilityMeasure (law.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (law.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hlegal : ∀ᵐ p ∂law, C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2) := by
    apply ae_normalizedFiniteLaw
    exact ae_restrict_mem ((Set.to_countable
      {p : Fin Q.count × Fin Q.count | C.clockClassAllowed Q p.1 p.2}).measurableSet.preimage
        (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify))
  have hα : (law.map Prod.fst).map Q.rangeClassify =
      (normalizedClockClassPairMeasure P₀).map Prod.fst := by
    rw [← hobserve,Measure.map_map measurable_fst
      (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify),
      Measure.map_map Q.measurable_rangeClassify measurable_fst]
    rfl
  have hβ : (law.map Prod.snd).map Q.rangeClassify =
      (normalizedClockClassPairMeasure P₀).map Prod.snd := by
    rw [← hobserve,Measure.map_map measurable_snd
      (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify),
      Measure.map_map Q.measurable_rangeClassify measurable_snd]
    rfl
  refine ⟨π,hπ,hmap,⟨law,hlaw⟩,rfl,hlower,hmass,?_⟩
  have hp := OriginalRangeClockResamplingData.exists_pressure_limits C hF hcomplete hu ha hinj Q
    ref.val ref.property f hε0 hε1 hprobe Rdata hq
    (law.map Prod.fst) (law.map Prod.snd) law ⟨rfl,rfl⟩ hlegal
  simpa only [hα,hβ,ProbabilityMeasure.toMeasure_map,
    clockClassJointProbability,ProbabilityMeasure.coe_mk] using hp


/-- All finite clock bins, the actual retained original law, its precise mass
and class observation, and both pressure limits are produced from the stored
original Finsler population data and the physical continuous probe. -/
theorem PopulationLocalPressureCore.exists_original_window_continuous_pressure_resampling
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    (f : M × M →ᵇ ℝ) {width : ℝ} (hwidth : 0 < width)
    {ε probeError : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hprobe : 0 < probeError)
    (hq : 4 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    {η : ℝ} (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    ∃ Q : FiniteScalarBins range width,
    ∃ π : Measure (range × range), IsProbabilityMeasure π ∧
      π.map (Prod.map Subtype.val Subtype.val) = γ ref.val ∧
      let C := D.haar.continuous.coefficient i
      let q := finrank ℝ (P C.seedIndex).seed.covector.ker
      let retained := π.restrict
        {p | C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2)}
      let law := normalizedFiniteLaw retained
      let P₀ := D.originalWindowReferenceWeights γ gap range i ref Q η
      ∃ originalLaw : ProbabilityMeasure (range × range), (originalLaw : Measure _) = law ∧
      let weightsData := D.originalWindowReferenceWeights_mass γ gap range i ref Q hη hgap hδ hδ1
      let classLaw := clockClassJointProbability P₀ weightsData.1 weightsData.2.2.2
      let α := originalLaw.map measurable_fst.aemeasurable
      let β := originalLaw.map measurable_snd.aemeasurable
      let αclass := classLaw.map measurable_fst.aemeasurable
      let βclass := classLaw.map measurable_snd.aemeasurable
      1 - δ.toReal ≤ retained.real univ ∧
      (∑ j, ∑ k, P₀ j k) = ((1 - η) * D.rootIntensity i ref.val) * retained.real univ ∧
      ∃ p pref : ℝ → ℝ,
        (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q
          (fun x y ↦ C.clockClassAllowed Q (Q.rangeClassify x) (Q.rangeClassify y)) (α : Measure _) (β : Measure _)
          (C.originalMaskedClockKinetic Q ref.val) (C.originalRangeClockProbe ref.val ref.property f) L t)
            atTop (𝓝 (p t))) ∧
        (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q) (αclass : Measure _) (βclass : Measure _)
          (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) L t)
            atTop (𝓝 (pref t))) ∧
        ∀ t, |p t - pref t| ≤ ε * (pref t + |t| * ‖f‖) + |t| * probeError := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨Q,⟨Rdata⟩⟩ := (D.haar.continuous.coefficient i).exists_original_range_clock_resampling_data
    hF hcomplete hu ha hinj ref.val ref.property f hrange hwidth hε hε1 hprobe
  exact ⟨Q,D.exists_original_window_continuous_pressure hrange.measurableSet γ gap
    hF hcomplete hu ha hinj i ref Q f hε.le hε1 hprobe.le Rdata hq hη hgap hδ hδ1⟩

end OTSelector.Reconstruction
