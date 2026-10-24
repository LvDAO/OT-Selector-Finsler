import OTSelector.Reconstruction.OriginalCubeTraceCompactnessInfBound
import OTSelector.Probability.StationaryScalarFaceAverage

/-! An actual vanishing common random bound for stationary smooth face pairings. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ} {G Ω : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : G → Ω → Ω) (hT : ∀ a, MeasurePreserving (T a) μ μ)
  (hzero : T 0 = id) (haddT : ∀ a b ω, T a (T b ω) = T (a+b) ω)
  (L : (Fin q → ℝ) →ₗ[ℝ] G)

/-- The common random bound is built literally from the translated original
observable, all actual finite cell integrals and their dyadic infimum. -/
def stationaryCubeTraceDualBound (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) (ω : Ω) : ℝ :=
  originalTraceDualInfBound (fun y ↦ stationaryScalarFaceReadout μ T L offset x R y ω)

omit [IsProbabilityMeasure μ] in
/-- The actual common stationary face bound is measurable in the original scene. -/
theorem measurable_stationaryCubeTraceDualBound
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) :
    Measurable (stationaryCubeTraceDualBound μ T L offset x R) :=
  measurable_originalTraceDualInfBound
    ((measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R).comp measurable_swap)

include hT hzero haddT

/-- Stationarity produces the integrability of the actual common bound;
no abstract integrability or face-energy bound is supplied as an input. -/
theorem integrable_stationaryCubeTraceDualBound
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) :
    Integrable (stationaryCubeTraceDualBound μ T L offset x R) μ := by
  apply integrable_originalTraceDualInfBound μ
    ((measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R).comp measurable_swap)
    ((integrable_sq_stationaryScalarFaceReadout_prod μ T hT hzero haddT L hTjoint offset x R
      isCompact_Icc.measure_lt_top.ne).swap)
  intro J
  exact integrable_sq_stationaryScalarFaceCell_average μ T hT hzero haddT L
    hTjoint offset x R isCompact_Icc.measure_lt_top.ne

/-- The literal common random quantity simultaneously controls every
smooth mean-zero unit-gradient test, on one full-measure original scene set. -/
theorem ae_all_smooth_trace_pairing_sq_le_stationaryCubeTraceDualBound
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) :
    ∀ᵐ ω ∂μ, ∀ (f : (Fin q → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1, f p) = 0 →
      boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1 →
      (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
        stationaryScalarFaceReadout μ T L offset x R y ω * f (y, 0))^2 ≤
          stationaryCubeTraceDualBound μ T L offset x R ω :=
  ae_all_smooth_trace_pairing_sq_le_originalTraceDualInfBound μ
    ((measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R).comp measurable_swap)
    ((integrable_sq_stationaryScalarFaceReadout_prod μ T hT hzero haddT L hTjoint offset x R
      isCompact_Icc.measure_lt_top.ne).swap)

/-- Zero actual face-invariant component forces the expectation of the
actual common bound to vanish. Joint scene measurability, whole-orbit strong
continuity and actual fixed projection are the only representation inputs;
weighted limits and scalar rates are proved internally. -/
theorem tendsto_integral_stationaryCubeTraceDualBound_zero
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (hcont : ∀ x : Lp ℝ 2 μ,
      Continuous (fun y : Fin q → ℝ ↦ stationaryKoopman μ T hT hzero haddT (L y) x))
    (offset : ℝ → G) {x : Lp ℝ 2 μ}
    (hx : (translationFixedSubspace (stationaryKoopman μ T hT hzero haddT) L.range).starProjection x = 0) :
    Tendsto (fun R : ℝ ↦ ∫ ω, stationaryCubeTraceDualBound μ T L offset x R ω ∂μ)
      atTop (𝓝 0) := by
  apply tendsto_integral_originalTraceDualInfBound_zero μ
    (fun R ↦ (measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R).comp measurable_swap)
    (fun R ↦ (integrable_sq_stationaryScalarFaceReadout_prod μ T hT hzero haddT L hTjoint offset x R
      isCompact_Icc.measure_lt_top.ne).swap)
    (fun R n J ↦ integrable_sq_stationaryScalarFaceCell_average μ T hT hzero haddT L
      hTjoint offset x R isCompact_Icc.measure_lt_top.ne) (C := ‖x‖^2)
  · intro R
    simp only [integral_sq_stationaryScalarFaceReadout μ T hT hzero haddT L offset x R]
    rw [setIntegral_const]
    have hV : volume.real (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1)) = 1 := by
      rw [measureReal_def, Real.volume_Icc_pi_toReal (fun _ ↦ zero_le_one)]
      simp
    simp [hV]
  · intro n J
    exact tendsto_integral_sq_stationaryScalarFaceCell_average_zero μ T hT hzero haddT L hcont
      hTjoint offset hx measurableSet_Icc isCompact_Icc.measure_lt_top.ne

end OTSelector.Reconstruction
