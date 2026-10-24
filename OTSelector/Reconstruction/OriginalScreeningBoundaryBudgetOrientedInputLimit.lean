import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedInputMoments
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! The actual reflected-input scalar mass is negligible at surface-flux scale. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- At the true R^(q-1) flux scale, the actual reflected-input mass has vanishing
second moment, directly from the proved surface-order Poisson variance. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalScreening_orientedInputMass_normalized_sq_zero
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hq : 1 < q) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    Tendsto (fun R : ℝ ↦ ∫ scene,
      ((R^(q-1))⁻¹ * originalScreeningOrientedReflectedInputMass b R C c scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) atTop (𝓝 0) := by
  let γ := if c = 0 then μ else ν
  let D := γ.real C * (4*(q:ℝ)*4^(q-1))
  have hp : q-1 < (q-1)*2 := by omega
  have hl : Tendsto (fun R : ℝ ↦ D*(R^(q-1)/(R^(q-1))^2)) atTop (𝓝 0) := by
    simpa only [pow_mul, mul_zero] using
      (tendsto_pow_div_pow_atTop_zero hp :
        Tendsto (fun R : ℝ ↦ R^(q-1)/R^((q-1)*2)) atTop (𝓝 0)).const_mul D
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))) ?_ hl
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have h := Q.originalScreening_orientedInputMass_moments b hR hC c
  dsimp only at h
  have hs : (∫ scene, (originalScreeningOrientedReflectedInputMass b R C c scene)^2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤ D*R^(q-1) := by
    exact h.2.2.trans_eq (by dsimp [D, γ]; ring)
  simp_rw [mul_pow, integral_const_mul]
  calc
    _ ≤ ((R^(q-1))⁻¹)^2 * (D*R^(q-1)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = D*(R^(q-1)/(R^(q-1))^2) := by rw [div_eq_mul_inv, inv_pow]; ring

end OTSelector.Reconstruction
