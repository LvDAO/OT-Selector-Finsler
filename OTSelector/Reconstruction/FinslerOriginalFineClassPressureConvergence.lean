import OTSelector.Reconstruction.FinslerOriginalCanonicalClockPressure
import OTSelector.Reconstruction.FinslerOriginalFullClockResamplingData
import OTSelector.Reconstruction.FinslerOriginalRangeClockResamplingPressure
import OTSelector.Analysis.RelativeErrorConvergence

/-! Actual finite coefficient-class pressures converge to the original
continuous scalar-clock pressure on one retained original law. Every fine
partition and every thermodynamic limit is produced internally. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
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

/-- On each actual retained original law, arbitrarily fine coefficient-class
models converge to the true original continuous scalar-legal pressure. Their
true thermodynamic limits and common original pressure are produced, with no
assumed uniform pressure bound or law-continuity callback. -/
theorem OriginalPopulationCoefficientCore.exists_original_fine_class_pressure_convergence
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    {range : Set ℝ} (hrange : IsCompact range) {gap : ℝ}
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (π : Measure (range × range)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π α β)
    (hgapLaw : ∀ᵐ p ∂π, gap ≤ p.2.val - p.1.val)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|)
    (hq : 4 < finrank ℝ (P C.seedIndex).seed.covector.ker) :
    ∃ fine : ∀ n : ℕ, FiniteScalarBins range (1 / ((n : ℝ) + 2)),
    ∃ p : ℝ → ℝ, ∃ pref : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ legalMarkedScalePressure
        (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β
        (fun x y v ↦ matrixQuadratic (C.matrix z₀ (x.val,y.val)) v)
        (C.originalRangeClockProbe z₀ hz₀ f) L t) atTop (𝓝 (p t))) ∧
      (∀ n, let γ := α.map (fine n).rangeClassify
        let τ := β.map (fine n).rangeClassify
        let _instγ : IsProbabilityMeasure γ := Measure.isProbabilityMeasure_map
          (fine n).measurable_rangeClassify.aemeasurable
        let _instτ : IsProbabilityMeasure τ := Measure.isProbabilityMeasure_map
          (fine n).measurable_rangeClassify.aemeasurable
        ∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure
          (finrank ℝ (P C.seedIndex).seed.covector.ker) (C.clockClassAllowed (fine n)) γ τ
          (C.clockClassKinetic (fine n) z₀) (C.clockClassProbe (fine n) z₀ hz₀ f) L t)
          atTop (𝓝 (pref n t))) ∧
      ∀ t, Tendsto (fun n ↦ pref n t) atTop (𝓝 (p t)) := by
  let accuracy := fun n : ℕ ↦ 1 / ((n : ℝ) + 2)
  have haccuracy n : 0 < accuracy n := by dsimp only [accuracy]; positivity
  have haccuracy1 n : accuracy n < 1 := by
    dsimp only [accuracy]
    apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hAcc : Tendsto accuracy atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    change Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) at h
    simpa only [accuracy,one_div] using h
  have hdata n := C.exists_original_full_clock_resampling_data hF hcomplete hu ha hinj
    z₀ hz₀ f hrange (haccuracy n) (haccuracy n) (haccuracy1 n).le (haccuracy n)
  choose fine hRdata hfull using hdata
  let Rdata := fun n ↦ Classical.choice (hRdata n)
  have hsource : ∀ᵐ p ∂π, p.1.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_Icc.preimage measurable_subtype_coe)).mp
    simpa only [hπ.1] using hα
  have htarget : ∀ᵐ p ∂π, p.2.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_Icc.preimage measurable_subtype_coe)).mp
    simpa only [hπ.2] using hβ
  have hlegal n : ∀ᵐ p ∂π, C.clockClassAllowed (fine n)
      ((fine n).rangeClassify p.1) ((fine n).rangeClassify p.2) := by
    filter_upwards [hsource,htarget,hgapLaw] with p hs ht hg
    exact ⟨(p.1.val,p.2.val),⟨⟨hs,ht⟩,hwindowGap.trans hg⟩,
      (fine n).rangeClassify_mem p.1,(fine n).rangeClassify_mem p.2⟩
  have hex n := OriginalRangeClockResamplingData.exists_pressure_limits C hF hcomplete hu ha hinj
    (fine n) z₀ hz₀ f (haccuracy n).le (haccuracy1 n).le (haccuracy n).le (Rdata n)
    hq α β π hπ (hlegal n)
  choose p pref hp hpref herror using hex
  have hcanonical n t : Tendsto (fun L ↦ legalMarkedScalePressure
      (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β
      (fun x y v ↦ matrixQuadratic (C.matrix z₀ (x.val,y.val)) v)
      (C.originalRangeClockProbe z₀ hz₀ f) L t) atTop (𝓝 (p n t)) := by
    exact (hp n t).congr' (Filter.Eventually.of_forall fun L ↦
      C.fine_clock_scalePressure_eq_canonical_original (fine n) hwindowGap (hfull n)
        z₀ hz₀ f α β hα hβ hsep L t)
  have huniq n t : p n t = p 0 t := tendsto_nhds_unique (hcanonical n t) (hcanonical 0 t)
  refine ⟨fine,p 0,pref,hcanonical 0,hpref,?_⟩
  intro t
  have hD : Tendsto (fun n ↦ |t| * accuracy n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hAcc.const_mul |t|
  apply tendsto_pressure_of_relative_error atTop (fun n ↦ pref n t) accuracy
    (fun n ↦ |t| * accuracy n) (p 0 t) (|t| * ‖f‖) hAcc hD
  apply Filter.Eventually.of_forall
  intro n
  exact ⟨(haccuracy n).le,haccuracy1 n,by simpa only [huniq n t] using herror n t⟩

end OTSelector.Reconstruction
