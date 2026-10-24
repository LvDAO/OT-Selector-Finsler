import OTSelector.Reconstruction.OriginalCubeReflectedInputFubini
import OTSelector.Reconstruction.OriginalInputBoundaryWeightVariance
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetReflectedInputs

/-! The literal reflected full-input field has exactly the original scalar boundary mass. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Integrating the genuine reflected response over the same original cube gives exactly
the scalar boundary weight: the reflected kernel contributes the actual cube indicator. -/
theorem integral_originalCubeReflectedInputResponse_eq_boundaryWeight {q : ℕ}
    {η : (Fin q → ℝ) → ℝ} (hηI : Integrable η volume)
    (hηone : ∫ v, η v = 1) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) (x : Fin q → ℝ) :
    (∫ z in haarRootCube (Fin q) R, originalCubeReflectedInputResponse η R z x) =
      originalInputBoundaryWeight η R x := by
  have hk : IntegrableOn (fun z ↦ originalCubeReflectedKernel η R z x)
      (haarRootCube (Fin q) R) :=
    integrable_finsetSum Finset.univ (fun a _ ↦ (hηI.comp_sub_right
      (originalCubeReflectionImage R a x)).integrableOn)
  unfold originalInputBoundaryWeight originalCubeReflectedInputResponse
  by_cases hx : x ∈ haarRootCube (Fin q) R
  · simp only [indicator_of_mem hx]
    rw [integral_sub hk (hηI.comp_sub_right x).integrableOn,
      integral_originalCubeReflectedKernel_eq_one hηI hηone hηsupport hηeven hR hx]
  · simp only [indicator_of_notMem hx, zero_sub, integral_neg]

/-- Actual bounded-product Fubini turns the spatial integral of the same full-input
reflected field into the original class-marked boundaryweight readout. Infinite total
input mass is allowed; only the true expanded spatial window is required to be finite. -/
theorem integral_originalClassReflectedInputScalarField_eq_boundaryWeight {q : ℕ}
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hηone : ∫ v, η v = 1) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    {R : ℝ} (hR : 1 ≤ R) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ))
    (hσ : σ (haarRootCube (Fin q) (R+1) ×ˢ (univ : Set ℝ)) < ∞) :
    (∫ z in haarRootCube (Fin q) R, originalClassReflectedInputScalarField η R C σ z) =
      ∫ p, originalInputClassBoundaryWeight η R C p ∂σ := by
  have h := integral_originalClassReflectedInputScalarField_mul_eq_of_finite_outer
    hη hM hηM hηsupport hR hC σ hσ (u := fun _ ↦ (1 : ℝ)) continuous_const
  simp only [mul_one] at h
  rw [h]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  dsimp only
  rw [integral_originalCubeReflectedInputResponse_eq_boundaryWeight hηI hηone hηsupport hηeven hR]
  exact mul_comm _ _

end OTSelector.Reconstruction
