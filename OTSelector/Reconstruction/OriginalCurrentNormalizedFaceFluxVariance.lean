import OTSelector.Reconstruction.OriginalCurrentScalarFaceCell
import OTSelector.Analysis.InnerProductSpace.FiniteCoefficientCauchy

/-! Actual signed finite face fluxes under one original stationary matching law. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
local instance originalFluxColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
  (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
  (offset : (Fin q × Fin 2) → ℝ → EuclideanSpace ℝ (Fin q))
  (x : Fin q → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))

/-- Each actual oriented face integral uses the same original scene law,
the fixed frame face map, and the specified literal spatial offset. -/
def LegalWeightedStationaryPoissonMatching.sceneOrientedFaceIntegral
    (R : ℝ) (j : Fin q × Fin 2) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∫ y in Icc (0 : ({k : Fin q // k ≠ j.1} → ℝ)) 1,
    Q.sceneScalarFaceReadout (orthonormalFaceMap b j.1) (offset j) (x j.1) R y s

/-- The normalized finite face flux is the literal signed sum of the 2q
original face integrals. Spatial area factors are not inserted into this unit-face average. -/
def LegalWeightedStationaryPoissonMatching.sceneNormalizedFaceFlux
    (R : ℝ) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∑ j : Fin q × Fin 2, (if j.2 = 0 then (-1 : ℝ) else 1) *
    Q.sceneOrientedFaceIntegral b offset x R j s

/-- Each actual random face integral is measurable under the original scene law. -/
theorem LegalWeightedStationaryPoissonMatching.measurable_sceneOrientedFaceIntegral
    (R : ℝ) (j : Fin q × Fin 2) :
    Measurable (Q.sceneOrientedFaceIntegral b offset x R j) := by
  let : IsFiniteMeasure (volume.restrict (Icc (0 : ({k : Fin q // k ≠ j.1} → ℝ)) 1)) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  exact measurable_finiteCell_average _
    (Q.measurable_sceneScalarFaceReadout (orthonormalFaceMap b j.1) (offset j) (x j.1) R)

/-- The literal 2q signed original face integral sum is measurable. -/
theorem LegalWeightedStationaryPoissonMatching.measurable_sceneNormalizedFaceFlux
    (R : ℝ) : Measurable (Q.sceneNormalizedFaceFlux b offset x R) := by
  unfold LegalWeightedStationaryPoissonMatching.sceneNormalizedFaceFlux
  exact Finset.measurable_sum Finset.univ
    (fun j _ ↦ (Q.measurable_sceneOrientedFaceIntegral b offset x R j).const_mul _)

/-- Every actual face average has its original finite second moment. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sq_sceneOrientedFaceIntegral
    (R : ℝ) (j : Fin q × Fin 2) :
    Integrable (fun s ↦ (Q.sceneOrientedFaceIntegral b offset x R j s)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
  Q.integrable_sq_sceneScalarFaceCell_average (orthonormalFaceMap b j.1)
    (offset j) (x j.1) R isCompact_Icc.measure_lt_top.ne

/-- Actual finite Cauchy controls the complete signed face sum by all its
original face-integral squares, with the literal number 2q of terms. -/
theorem LegalWeightedStationaryPoissonMatching.sceneNormalizedFaceFlux_sq_le
    (R : ℝ) (s : LegalMarkedOptimalInputScene q) :
    (Q.sceneNormalizedFaceFlux b offset x R s)^2 ≤
      ((2*q : ℕ) : ℝ) * ∑ j : Fin q × Fin 2,
        (Q.sceneOrientedFaceIntegral b offset x R j s)^2 := by
  have hc : ∀ j : Fin q × Fin 2, (if j.2 = 0 then (-1 : ℝ) else 1)^2 ≤ 1 := by
    intro j
    split_ifs <;> norm_num
  simpa only [LegalWeightedStationaryPoissonMatching.sceneNormalizedFaceFlux,
    Fintype.card_prod, Fintype.card_fin, Nat.mul_comm, mul_one] using
    sum_mul_sq_le_fintype_card_mul_of_coeff_sq_le
      (fun j : Fin q × Fin 2 ↦ if j.2 = 0 then (-1 : ℝ) else 1)
      (fun j ↦ Q.sceneOrientedFaceIntegral b offset x R j s) hc

/-- The entire actual finite face flux has an integrable square. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sq_sceneNormalizedFaceFlux
    (R : ℝ) :
    Integrable (fun s ↦ (Q.sceneNormalizedFaceFlux b offset x R s)^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hsum := (integrable_finsetSum Finset.univ (fun j _ ↦
    Q.integrable_sq_sceneOrientedFaceIntegral b offset x R j)).const_mul (((2*q : ℕ) : ℝ))
  apply hsum.mono' ((Q.measurable_sceneNormalizedFaceFlux b offset x R).aestronglyMeasurable.pow 2)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Q.sceneNormalizedFaceFlux_sq_le b offset x R s

/-- The original whole-flux second moment is bounded by the finite sum of
its actual original face-average second moments. -/
theorem LegalWeightedStationaryPoissonMatching.integral_sq_sceneNormalizedFaceFlux_le
    (R : ℝ) :
    (∫ s, (Q.sceneNormalizedFaceFlux b offset x R s)^2 ∂(Q.law : Measure _)) ≤
      ((2*q : ℕ) : ℝ) * ∑ j : Fin q × Fin 2,
        ∫ s, (Q.sceneOrientedFaceIntegral b offset x R j s)^2 ∂(Q.law : Measure _) := by
  have hsum := (integrable_finsetSum Finset.univ (fun j _ ↦
    Q.integrable_sq_sceneOrientedFaceIntegral b offset x R j)).const_mul (((2*q : ℕ) : ℝ))
  have h := integral_mono (Q.integrable_sq_sceneNormalizedFaceFlux b offset x R) hsum
    (fun s ↦ Q.sceneNormalizedFaceFlux_sq_le b offset x R s)
  simpa only [integral_const_mul, integral_finsetSum _
    (fun j _ ↦ Q.integrable_sq_sceneOrientedFaceIntegral b offset x R j)] using h

/-- Each true original normal face integral has vanishing second moment
once the original face-invariant projection of that normal readout is zero. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_integral_sq_sceneOrientedFaceIntegral_zero
    (hx : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection (x i) = 0)
    (j : Fin q × Fin 2) :
    Tendsto (fun R : ℝ ↦ ∫ s, (Q.sceneOrientedFaceIntegral b offset x R j s)^2
      ∂(Q.law : Measure _)) atTop (𝓝 0) := by
  apply Q.tendsto_integral_sq_sceneScalarFaceCell_average_zero (orthonormalFaceMap b j.1)
    (offset j) ?_ measurableSet_Icc isCompact_Icc.measure_lt_top.ne
  simpa only [range_orthonormalFaceMap] using hx j.1

/-- The literal normalized full signed face flux has vanishing original
second moment, produced from all actual face readouts under one law and frame.
No flux variance, mixing, or final rate is assumed. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_integral_sq_sceneNormalizedFaceFlux_zero
    (hx : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection (x i) = 0) :
    Tendsto (fun R : ℝ ↦ ∫ s, (Q.sceneNormalizedFaceFlux b offset x R s)^2
      ∂(Q.law : Measure _)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun R : ℝ ↦ ((2*q : ℕ) : ℝ) *
      (∑ j : Fin q × Fin 2, ∫ s, (Q.sceneOrientedFaceIntegral b offset x R j s)^2
        ∂(Q.law : Measure _))) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, mul_zero] using
      (tendsto_finsetSum Finset.univ (fun j _ ↦
        Q.tendsto_integral_sq_sceneOrientedFaceIntegral_zero b offset x hx j)).const_mul (((2*q : ℕ) : ℝ))
  exact squeeze_zero (fun R ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (fun R ↦ Q.integral_sq_sceneNormalizedFaceFlux_le b offset x R) hsum

end OTSelector.Reconstruction
