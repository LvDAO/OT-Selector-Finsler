import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetResponseMass
import OTSelector.Reconstruction.OriginalActualInputBoundaryLawTransfer

/-! Actual scalar reflected-input masses inherit their genuine original Poisson variance. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The literal spatial mass of the canonical reflected-input error in one original class. -/
def originalScreeningReflectedInputMass {q : ℕ} (R : ℝ) (C : Set ℝ) (c : Fin 2)
    (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ∫ z in haarRootCube (Fin q) R,
    originalClassReflectedInputScalarField (originalEuclideanMollifier q) R C
      (legalInputColorMeasure q scene.2 c) z

/-- The actual original full-input reflected mass has zero mean and surface-order variance.
Reflection mass preservation, genuine finite-window Fubini and actual full PPP law supply
this result; no assertion of independent selected ports is involved. -/
theorem LegalWeightedStationaryPoissonMatching.originalScreening_reflectedInput_mass_variance
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    {R : ℝ} (hR : 1 ≤ R) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    let I := originalScreeningReflectedInputMass R C c
    let γ := if c = 0 then μ else ν
    MemLp I 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ scene, I scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) = 0 ∧
    variance I (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≤
      γ.real C * ((4*(q:ℝ)*4^(q-1))*R^(q-1)) := by
  let η := originalEuclideanMollifier q
  have hmass : originalScreeningReflectedInputMass R C c =ᵐ[(Q.law : Measure (LegalMarkedOptimalInputScene q))]
      fun scene ↦ ∫ p, originalInputClassBoundaryWeight η R C p
        ∂legalInputColorMeasure q scene.2 c := by
    filter_upwards [Q.ae_finite_reflectedInputOuterWindow R c] with scene hs
    exact integral_originalClassReflectedInputScalarField_eq_boundaryWeight
      (contDiff_originalEuclideanMollifier q).continuous.measurable
      (integrable_originalEuclideanMollifier q) (integral_originalEuclideanMollifier_eq_one q)
      (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q))
      (coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q))
      (originalEuclideanMollifierBound_nonneg q) (abs_originalEuclideanMollifier_le q)
      hR hC (legalInputColorMeasure q scene.2 c) hs
  have h := Q.original_fullInput_boundaryWeight_variance
    (contDiff_originalEuclideanMollifier q).continuous.measurable
    (integrable_originalEuclideanMollifier q) (originalEuclideanMollifier_nonneg q)
    (integral_originalEuclideanMollifier_eq_one q)
    (fun x hx ↦ raw_unit_range_of_euclidean_unit_range
      (originalEuclideanMollifier_unit_range q) x hx.le) hR hC c
  dsimp only at h ⊢
  refine ⟨h.1.ae_eq hmass.symm, ?_, ?_⟩
  · exact (integral_congr_ae hmass).trans h.2.1
  · rw [variance_congr hmass]
    exact h.2.2.2

end OTSelector.Reconstruction
