import OTSelector.Reconstruction.FinslerOriginalCoarsePressureGrid
import OTSelector.Reconstruction.FinslerOriginalRangeClockResamplingPressure
import OTSelector.Reconstruction.OriginalLegalPressureBlockEnvelope

/-! The actual original continuous-clock thermodynamic pressure is bounded by
each fixed box and one vanishing coarse repair error, uniformly over fine
coefficient bins and original supported conditional clock laws. -/
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


/-- Geometry chooses one coarse repair bound before all fine bins and clock
laws. Every resulting actual continuous original pressure limit then has the
same explicit fixed-box upper envelope. -/
theorem OriginalPopulationCoefficientCore.exists_original_coarse_pressure_box_envelope
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
      (_Rdata : OriginalRangeClockResamplingData C fine z₀ hz₀ f ε η) (_hε0 : 0 ≤ ε) (_hε1 : ε ≤ 1) (_hη0 : 0 ≤ η)
      (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
      (_hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
      (_hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
      (π : Measure (range × range)) [IsFiniteMeasure π] (_hπ : Vlasov.IsCoupling π α β)
      (_hgapLaw : ∀ᵐ p ∂π, gap ≤ p.2.val - p.1.val)
      (_hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|)
      (_hq : 4 < finrank ℝ (P C.seedIndex).seed.covector.ker),
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let mask := fun x y ↦ C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y)
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q mask α β
        (C.originalMaskedClockKinetic fine z₀) (C.originalRangeClockProbe z₀ hz₀ f) L t)
          atTop (𝓝 (p t))) ∧
      ∀ (t L : ℝ), 0 < L →
        p t ≤ finiteClassLegalScalePressure q mask α β (C.originalMaskedClockKinetic fine z₀)
          (C.originalRangeClockProbe z₀ hz₀ f) L t +
          gridRepairError q (legalGridRepairConstant q coarse.count (legalClockTypeCount coarse.count))
            (2 * K) ‖f‖ t L := by
  obtain ⟨K,hK,hgrid⟩ := C.exists_original_coarse_pressure_grid_bound hF hcomplete hu ha hinj
    z₀ hz₀ hrange coarse hgap hwindowGap
  refine ⟨K,hK,?_⟩
  intro width fine hfull f ε η Rdata hε0 hε1 hη0 α β _ _ hα hβ π _ hπ hgapLaw hsep hq
  dsimp only
  have hsource : ∀ᵐ p ∂π, p.1.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_Icc.preimage measurable_subtype_coe)).mp
    simpa only [hπ.1] using hα
  have htarget : ∀ᵐ p ∂π, p.2.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_Icc.preimage measurable_subtype_coe)).mp
    simpa only [hπ.2] using hβ
  have hlegal : ∀ᵐ p ∂π, C.clockClassAllowed fine (fine.rangeClassify p.1) (fine.rangeClassify p.2) := by
    filter_upwards [hsource,htarget,hgapLaw] with p hs ht hg
    exact ⟨(p.1.val,p.2.val),⟨⟨hs,ht⟩,hwindowGap.trans hg⟩,
      fine.rangeClassify_mem p.1,fine.rangeClassify_mem p.2⟩
  obtain ⟨p,_pref,hp,_hpref,_hcompare⟩ := OriginalRangeClockResamplingData.exists_pressure_limits
    C hF hcomplete hu ha hinj fine z₀ hz₀ f hε0 hε1 hη0 Rdata hq α β π hπ hlegal
  refine ⟨p,hp,?_⟩
  intro t L hL
  apply finiteClassLegalScalePressure_limit_le_of_block_bound
    (finrank ℝ (P C.seedIndex).seed.covector.ker)
    (fun x y ↦ C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y)) α β
    (C.originalMaskedClockKinetic fine z₀) (C.originalRangeClockProbe z₀ hz₀ f)
    (2 * K) ‖f‖ t
    (legalGridRepairConstant (finrank ℝ (P C.seedIndex).seed.covector.ker)
      coarse.count (legalClockTypeCount coarse.count)) (p t) (hp t) _ hL
  intro m hm L hL
  apply finiteClassLegalScalePressure_block_le_of_intensity_bound
    (finrank ℝ (P C.seedIndex).seed.covector.ker) m (by omega) hm
    (fun x y ↦ C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y)) α β
    (C.originalMaskedClockKinetic fine z₀) (C.originalRangeClockProbe z₀ hz₀ f)
    (2 * K) ‖f‖ t
    (legalGridRepairConstant (finrank ℝ (P C.seedIndex).seed.covector.ker)
      coarse.count (legalClockTypeCount coarse.count)) _ hL
  intro r
  exact hgrid fine hfull f Rdata hε1 α β hα hβ π hπ hgapLaw hsep hq m hm r t

end OTSelector.Reconstruction
