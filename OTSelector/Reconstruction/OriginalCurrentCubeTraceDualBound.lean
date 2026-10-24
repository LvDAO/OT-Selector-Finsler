import OTSelector.Reconstruction.OriginalCurrentScalarFaceCell
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessHomogeneous

/-! The literal vanishing common trace bound of the original stationary matching scene. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability
local instance originalCurrentTraceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {q r : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
  (L : (Fin r → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))

private theorem measurable_originalCurrentFaceField
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    Measurable (fun p : LegalMarkedOptimalInputScene q × (Fin r → ℝ) ↦
      Q.sceneScalarFaceReadout L offset x R p.2 p.1) := by
  change Measurable ((Function.uncurry (Q.sceneScalarFaceReadout L offset x R)) ∘
    (Prod.swap : LegalMarkedOptimalInputScene q × (Fin r → ℝ) → (Fin r → ℝ) × LegalMarkedOptimalInputScene q))
  exact (Q.measurable_sceneScalarFaceReadout L offset x R).comp
    (measurable_swap : Measurable (Prod.swap :
      LegalMarkedOptimalInputScene q × (Fin r → ℝ) → (Fin r → ℝ) × LegalMarkedOptimalInputScene q))

private theorem integrable_sq_originalCurrentFaceField
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    Integrable (fun p : LegalMarkedOptimalInputScene q × (Fin r → ℝ) ↦
      (Q.sceneScalarFaceReadout L offset x R p.2 p.1)^2)
      ((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1)))) :=
  (Q.integrable_sq_sceneScalarFaceReadout_prod L offset x R
    (A := Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1)) isCompact_Icc.measure_lt_top.ne).swap

/-- The common quantity is built from the actual original scene readout
and the countable infimum of its literal finite-cell approximation bounds. -/
def LegalWeightedStationaryPoissonMatching.sceneCubeTraceDualBound
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (R : ℝ) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  originalTraceDualInfBound (fun y ↦ Q.sceneScalarFaceReadout L offset x R y s)

/-- The literal original common bound is nonnegative at every scene. -/
theorem LegalWeightedStationaryPoissonMatching.sceneCubeTraceDualBound_nonneg
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (R : ℝ) (s : LegalMarkedOptimalInputScene q) :
    0 ≤ Q.sceneCubeTraceDualBound L offset x R s := originalTraceDualInfBound_nonneg _

/-- Joint original face/scene measurability produces the actual measurable common bound. -/
theorem LegalWeightedStationaryPoissonMatching.measurable_sceneCubeTraceDualBound
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    Measurable (Q.sceneCubeTraceDualBound L offset x R) := by
  unfold LegalWeightedStationaryPoissonMatching.sceneCubeTraceDualBound
  exact measurable_originalTraceDualInfBound (g := fun s y ↦ Q.sceneScalarFaceReadout L offset x R y s)
    (measurable_originalCurrentFaceField Q L offset x R)

/-- Actual original stationarity produces integrability of the common bound. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sceneCubeTraceDualBound
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    Integrable (Q.sceneCubeTraceDualBound L offset x R) (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  change Integrable (fun s ↦ originalTraceDualInfBound (fun y ↦ Q.sceneScalarFaceReadout L offset x R y s))
    (Q.law : Measure (LegalMarkedOptimalInputScene q))
  apply integrable_originalTraceDualInfBound (Q.law : Measure (LegalMarkedOptimalInputScene q))
    (g := fun s y ↦ Q.sceneScalarFaceReadout L offset x R y s)
    (measurable_originalCurrentFaceField Q L offset x R)
    (integrable_sq_originalCurrentFaceField Q L offset x R)
  intro J
  exact Q.integrable_sq_sceneScalarFaceCell_average L offset x R isCompact_Icc.measure_lt_top.ne

/-- One original full-measure scene set controls every smooth mean-zero
unit-gradient test by the same actual random quantity. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_smooth_trace_pairing_sq_le_sceneCubeTraceDualBound
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), ∀ (f : (Fin r → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      (∫ p in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1, f p) = 0 →
      boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1 →
      (∫ y in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1),
        Q.sceneScalarFaceReadout L offset x R y s * f (y, 0))^2 ≤
          Q.sceneCubeTraceDualBound L offset x R s :=
  ae_all_smooth_trace_pairing_sq_le_originalTraceDualInfBound (Q.law : Measure (LegalMarkedOptimalInputScene q))
    (g := fun s y ↦ Q.sceneScalarFaceReadout L offset x R y s)
    (measurable_originalCurrentFaceField Q L offset x R)
    (integrable_sq_originalCurrentFaceField Q L offset x R)

/-- The same actual common quantity controls all smooth zero-mean tests
homogeneously in their original gradient energy, on one original full-measure set. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_smooth_trace_pairing_sq_le_sceneCubeTraceDualBound_mul_energy
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), ∀ (f : (Fin r → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      (∫ p in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1, f p) = 0 →
      (∫ y in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1),
        Q.sceneScalarFaceReadout L offset x R y s * f (y, 0))^2 ≤
          Q.sceneCubeTraceDualBound L offset x R s *
            boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 := by
  have hm := measurable_originalCurrentFaceField Q L offset x R
  have hp := integrable_sq_originalCurrentFaceField Q L offset x R
  filter_upwards [hp.prod_right_ae] with s hs
  have hLp : MemLp (fun y ↦ Q.sceneScalarFaceReadout L offset x R y s) 2
      (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))) :=
    (memLp_two_iff_integrable_sq
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hs
  intro f hf hmean
  exact smooth_trace_pairing_sq_le_originalTraceDualInfBound_mul_energy hLp hf hmean

/-- Actual homogeneous absolute trace bound with the square root of the
same measurable original-scene common quantity. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_smooth_trace_pairing_abs_le_sceneCubeTraceDualBound_sqrt_energy
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) (R : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), ∀ (f : (Fin r → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      (∫ p in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1, f p) = 0 →
      |∫ y in Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1),
        Q.sceneScalarFaceReadout L offset x R y s * f (y, 0)| ≤
          Real.sqrt (Q.sceneCubeTraceDualBound L offset x R s) *
            Real.sqrt (boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1) := by
  filter_upwards [Q.ae_all_smooth_trace_pairing_sq_le_sceneCubeTraceDualBound_mul_energy L offset x R]
    with s hs
  intro f hf hmean
  have hB := Q.sceneCubeTraceDualBound_nonneg L offset x R s
  have hE := boxCollarGradientEnergy_nonneg f (fun _ ↦ 0) (fun _ ↦ 1) 1
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hE] using hs f hf hmean

/-- In each genuine centered face direction, the expectation of the actual
original-scene common trace bound vanishes. All stationarity, scalar realization,
finite-cell moments and weighted limits are produced internally. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_integral_sceneCubeTraceDualBound_zero
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    {x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))}
    (hx : (translationFixedSubspace Q.sceneEuclideanKoopman L.range).starProjection x = 0) :
    Tendsto (fun R : ℝ ↦ ∫ s, Q.sceneCubeTraceDualBound L offset x R s ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))
      atTop (𝓝 0) := by
  change Tendsto (fun R : ℝ ↦ ∫ s, originalTraceDualInfBound
    (fun y ↦ Q.sceneScalarFaceReadout L offset x R y s) ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)))
    atTop (𝓝 0)
  apply tendsto_integral_originalTraceDualInfBound_zero (Q.law : Measure (LegalMarkedOptimalInputScene q))
    (g := fun R s y ↦ Q.sceneScalarFaceReadout L offset x R y s)
    (fun R ↦ measurable_originalCurrentFaceField Q L offset x R)
    (fun R ↦ (Q.integrable_sq_sceneScalarFaceReadout_prod L offset x R
      isCompact_Icc.measure_lt_top.ne).swap)
    (fun R n J ↦ Q.integrable_sq_sceneScalarFaceCell_average L offset x R
      isCompact_Icc.measure_lt_top.ne) (C := ‖x‖^2)
  · intro R
    have hp := Q.integrable_sq_sceneScalarFaceReadout_prod L offset x R
      (A := Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1)) isCompact_Icc.measure_lt_top.ne
    rw [integral_integral_swap hp, Q.integral_sceneScalarFaceReadout_sq_average L offset x R
      isCompact_Icc.measure_lt_top.ne]
    have hV : volume.real (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1)) = 1 := by
      rw [measureReal_def, Real.volume_Icc_pi_toReal (fun _ ↦ zero_le_one)]
      simp
    simp [hV]
  · intro n J
    exact Q.tendsto_integral_sq_sceneScalarFaceCell_average_zero L offset hx
      measurableSet_Icc isCompact_Icc.measure_lt_top.ne

end OTSelector.Reconstruction
