import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedReflectedInputs
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! The reflected-input mean bound is uniform in the changing compact support of the test space. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The true surface-order means of the source and target reflected responses vanish after
normalization by the volume of the same actual original cube, even for arbitrary changing test supports. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalStageOriented_reflectedInput_varyingSupport_density_zero
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (K : ℝ → Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (hq : 2 < q) (s t : ℝ) :
    Tendsto (fun R : ℝ ↦
      (∫ scene, originalStageOrientedSourceReflectedInputBound (K R) b R s t scene +
        originalStageOrientedTargetReflectedInputBound (K R) b R s t scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) /
          volume.real (originalCenteredPhysicalCubeRegion b (2*R))) atTop (𝓝 0) := by
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
    have hb := Q.originalStageOriented_reflectedInput_bounds (K R) b hq hR s t
    exact div_nonneg (integral_nonneg (fun scene ↦ add_nonneg (hb.2.2.1 scene).1
      (hb.2.2.1 scene).2)) measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hb := Q.originalStageOriented_reflectedInput_bounds (K R) b hq hR s t
    have hRp : 0 < R := by linarith
    have hv : 0 < volume.real (originalCenteredPhysicalCubeRegion b (2*R)) := by
      rw [measureReal_def, volume_originalOrientedTraffic_cube b R, ← measureReal_def,
        volume_real_haarRootCube (Fin q) hRp.le]
      positivity
    have he := div_le_div_of_nonneg_right hb.2.2.2.2.2.1 hv.le
    have heq : C * R^(q-1) * m / volume.real (originalCenteredPhysicalCubeRegion b (2*R)) =
        (C*m/(2:ℝ)^q) * (R^(q-1)/R^q) := by
      rw [measureReal_def, volume_originalOrientedTraffic_cube b R, ← measureReal_def,
        volume_real_haarRootCube (Fin q) hRp.le, Fintype.card_fin, mul_pow]
      field_simp
    exact he.trans_eq heq

end OTSelector.Reconstruction
