import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetBulkEnergy
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetBoundaryTrace
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetReflectedInputs

/-! Actual current energy, full-current face traces and both reflected-input responses
control the same cube residual simultaneously for every mean-zero smooth test. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The concrete original common Neumann coefficient: omitted-current bulk energy,
full-current true-face trace coefficient, and the two actual full-input response bounds. -/
def originalStageCurrentInputNeumannBudget {q : ℕ} (K : Compacts (Fin q → ℝ))
    (R s t : ℝ) (Jfull Jret : (Fin q → ℝ) → Fin q → ℝ)
    (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  4 * (originalStageCurrentLtwoEnergy (fun z ↦ Jfull z - Jret z) R +
    originalStageCurrentBoundaryTraceBound Jfull R +
    originalStageSourceReflectedInputBound K R s t scene +
    originalStageTargetReflectedInputBound K R s t scene)

/-- Every term of the concrete Neumann coefficient is nonnegative on an actual cube. -/
theorem originalStageCurrentInputNeumannBudget_nonneg {q : ℕ}
    (K : Compacts (Fin q → ℝ)) {R : ℝ} (hR : 0 ≤ R) (s t : ℝ)
    (Jfull Jret : (Fin q → ℝ) → Fin q → ℝ) (scene : LegalMarkedOptimalInputScene q) :
    0 ≤ originalStageCurrentInputNeumannBudget K R s t Jfull Jret scene := by
  have hs : 0 ≤ originalStageSourceReflectedInputBound K R s t scene := sq_nonneg _
  have ht : 0 ≤ originalStageTargetReflectedInputBound K R s t scene := sq_nonneg _
  exact mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (add_nonneg (originalStageCurrentLtwoEnergy_nonneg _ _)
      (originalStageCurrentBoundaryTraceBound_nonneg Jfull hR)) hs) ht)

/-- The literal divergence and reflected-input test pairing, before applying the actual
positive-slab identity that identifies it with the original stage densities. -/
def originalStageCurrentInputPairing {q : ℕ} (R s t : ℝ)
    (Jfull Jret : (Fin q → ℝ) → Fin q → ℝ) (scene : LegalMarkedOptimalInputScene q)
    (φ : (Fin q → ℝ) → ℝ) : ℝ :=
  (∫ z in haarRootCube (Fin q) R,
    originalStageCurrentDivergence (fun z ↦ Jfull z - Jret z) z * φ z) +
  (∫ z in haarRootCube (Fin q) R,
    originalClassReflectedInputScalarField (originalEuclideanMollifier q) R (Ico s t)
      (legalInputColorMeasure q scene.2 0) z * φ z) -
  (∫ z in haarRootCube (Fin q) R,
    originalClassReflectedInputScalarField (originalEuclideanMollifier q) R (Ioc s t)
      (legalInputColorMeasure q scene.2 1) z * φ z)

private theorem four_signed_squares (a b c d : ℝ) :
    (a-b+c-d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a+b), sq_nonneg (a-c), sq_nonneg (a+d),
    sq_nonneg (b+c), sq_nonneg (b-d), sq_nonneg (c+d)]

/-- The actual Poisson inputs provide one full-measure scene event. On that event every
actual C1 full/retained current pair with vanishing retained face trace has the same
concrete bound for all mean-zero smooth tests. The divergence theorem, gradient Cauchy,
compact face bound and both canonical reflected-input response estimates are internal. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_originalStageCurrentInput_Neumann_bound
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (K : Compacts (Fin q → ℝ)) (hq : 2 < q) {R : ℝ} (hR : 1 ≤ R) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ Jfull Jret : (Fin q → ℝ) → Fin q → ℝ,
      ContDiff ℝ 1 Jfull → ContDiff ℝ 1 (fun z ↦ Jfull z - Jret z) →
      (∀ z i, z i = R ∨ z i = -R → Jret z = 0) →
      ∀ φ : 𝓓_{K}(Fin q → ℝ, ℝ), (∫ z in haarRootCube (Fin q) R, φ z) = 0 →
      (originalStageCurrentInputPairing R s t Jfull Jret scene φ)^2 ≤
        originalStageCurrentInputNeumannBudget K R s t Jfull Jret scene *
          ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)) φ‖^2 := by
  filter_upwards [(Q.originalStage_reflectedInput_bounds K hq hR s t).2.2.2.2.2.2]
    with scene hinputs
  intro Jfull Jret hfull hdiff hret φ hm
  have hRp : 0 < R := by linarith
  let G := ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)) φ‖^2
  have hb := originalStageAxisBoundaryPairing_sq_le hfull.continuous hRp K φ hm
  have hg := originalStageCurrentGradientPairing_sq_le hdiff.continuous R K φ
  have hs := (hinputs φ hm).1
  have ht := (hinputs φ hm).2
  have hface : originalStageAxisBoundaryPairing (fun z ↦ Jfull z - Jret z) R φ =
      originalStageAxisBoundaryPairing Jfull R φ := by
    apply originalStageAxisBoundaryPairing_congr R
    intro z i hi
    rw [hret z i hi, sub_zero]
  unfold originalStageCurrentInputPairing
  rw [originalStageCurrent_gauss_green hdiff hRp.le (φ.contDiff.of_le (by norm_num)), hface]
  calc
    _ ≤ 4 * ((originalStageAxisBoundaryPairing Jfull R φ)^2 +
        (originalStageCurrentGradientPairing (fun z ↦ Jfull z - Jret z) R φ)^2 +
        (∫ z in haarRootCube (Fin q) R,
          originalClassReflectedInputScalarField (originalEuclideanMollifier q) R (Ico s t)
            (legalInputColorMeasure q scene.2 0) z * φ z)^2 +
        (∫ z in haarRootCube (Fin q) R,
          originalClassReflectedInputScalarField (originalEuclideanMollifier q) R (Ioc s t)
            (legalInputColorMeasure q scene.2 1) z * φ z)^2) := four_signed_squares _ _ _ _
    _ ≤ 4 * (originalStageCurrentBoundaryTraceBound Jfull R * G +
        originalStageCurrentLtwoEnergy (fun z ↦ Jfull z - Jret z) R * G +
        originalStageSourceReflectedInputBound K R s t scene * G +
        originalStageTargetReflectedInputBound K R s t scene * G) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hb hg) hs) ht) (by norm_num)
    _ = _ := by unfold originalStageCurrentInputNeumannBudget G; ring

end OTSelector.Reconstruction
