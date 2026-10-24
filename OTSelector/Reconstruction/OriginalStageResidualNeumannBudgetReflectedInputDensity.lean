import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetReflectedInputs
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! The two actual canonical reflected-input response means are subextensive. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The true surface-order means of the source and target reflected responses vanish after
normalization by the volume of the same actual original cube. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalStage_reflectedInput_bound_density_zero
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (K : Compacts (Fin q → ℝ)) (hq : 2 < q) (s t : ℝ) :
    Tendsto (fun R : ℝ ↦
      (∫ scene, originalStageSourceReflectedInputBound K R s t scene +
        originalStageTargetReflectedInputBound K R s t scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) /
          volume.real (haarRootCube (Fin q) R)) atTop (𝓝 0) := by
  let C := cubeReflectedResponseSobolevConstant q (originalEuclideanMollifierBound q)^2 *
    (4*(q:ℝ)*4^(q-1))
  let m := μ.real (Ico s t) + ν.real (Ioc s t)
  have hp : q-1 < q := by omega
  have hpower : Tendsto (fun R : ℝ ↦ R^(q-1)/R^q) atTop (𝓝 0) :=
    tendsto_pow_div_pow_atTop_zero hp
  have hlim := hpower.const_mul (C*m/(2:ℝ)^q)
  simp only [mul_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hb := Q.originalStage_reflectedInput_bounds K hq hR s t
    exact div_nonneg (integral_nonneg (fun scene ↦ add_nonneg (hb.2.2.1 scene).1
      (hb.2.2.1 scene).2)) measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hb := Q.originalStage_reflectedInput_bounds K hq hR s t
    have hRp : 0 < R := by linarith
    have hv : 0 < volume.real (haarRootCube (Fin q) R) := by
      rw [volume_real_haarRootCube (Fin q) hRp.le]
      positivity
    have he := div_le_div_of_nonneg_right hb.2.2.2.2.2.1 hv.le
    have heq : C * R^(q-1) * m / volume.real (haarRootCube (Fin q) R) =
        (C*m/(2:ℝ)^q) * (R^(q-1)/R^q) := by
      rw [volume_real_haarRootCube (Fin q) hRp.le, Fintype.card_fin, mul_pow]
      field_simp
    exact he.trans_eq heq

end OTSelector.Reconstruction
