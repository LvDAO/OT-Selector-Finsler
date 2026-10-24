import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetResponseMass
import OTSelector.Reconstruction.OriginalOrientedCubeReflectedFubini
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessOrientedInputHminus

/-! Literal full-input reflected mass on the same selected physical cube. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The same canonical raw scalar boundary weight read in the genuine physical frame. -/
def originalScreeningOrientedInputClassBoundaryWeight {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (C : Set ℝ)
    (p : LegalMarkedPhysicalPoint q) : ℝ :=
  originalInputClassBoundaryWeight (originalEuclideanMollifier q) R C
    (originalOrientedInputCoordinates b p)

/-- The actual physical-space integral of the unchanged original full-input reflected error. -/
def originalScreeningOrientedReflectedInputMass {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (R : ℝ) (C : Set ℝ) (c : Fin 2) (scene : LegalMarkedOptimalInputScene q) : ℝ :=
  ∫ z in originalCenteredPhysicalCubeRegion b (2*R),
    originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier q) (2*R) C
      (legalInputColorMeasure q scene.2 c) z

/-- Actual Haar transport, genuine finite-window Fubini and reflection mass preservation
identify the literal physical response mass with its same-input marked boundary weight. -/
theorem integral_originalOrientedClassReflectedInputScalarField_eq_boundaryWeight {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C) (σ : Measure (LegalMarkedPhysicalPoint q))
    (hσ : σ (originalCenteredPhysicalCubeRegion b (2*R+2) ×ˢ (univ : Set ℝ)) < ∞) :
    (∫ z in originalCenteredPhysicalCubeRegion b (2*R),
      originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier q) (2*R) C σ z) =
      ∫ p, originalScreeningOrientedInputClassBoundaryWeight b R C p ∂σ := by
  let σraw := σ.map (originalOrientedInputCoordinates b)
  have hhalf : (2*R)/2 = R := by ring
  have hf := integral_orientedClassReflectedInputScalarField_mul_eq_raw b
    (originalEuclideanMollifier_radial q) (2*R) C σ (fun _ ↦ (1:ℝ))
  simp only [mul_one, hhalf] at hf
  rw [hf]
  have hraw : σraw (haarRootCube (Fin q) (R+1) ×ˢ (univ : Set ℝ)) < ∞ := by
    have hw := map_oriented_input_outerWindow b (2*R) σ
    simp only [hhalf] at hw
    exact hw.trans_lt hσ
  change (∫ y in haarRootCube (Fin q) R, originalClassReflectedInputScalarField
    (originalEuclideanMollifier q) R C σraw y) = _
  rw [integral_originalClassReflectedInputScalarField_eq_boundaryWeight
    (contDiff_originalEuclideanMollifier q).continuous.measurable
    (integrable_originalEuclideanMollifier q) (integral_originalEuclideanMollifier_eq_one q)
    (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q))
    (coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q))
    (originalEuclideanMollifierBound_nonneg q) (abs_originalEuclideanMollifier_le q)
    hR hC σraw hraw]
  exact integral_map_equiv (originalOrientedInputCoordinates b) _

/-- The literal oriented full-input mass equals its genuine compact-spatial scalar Poisson
readout on one original-scene event, with no selected-port law. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalScreening_orientedInputMass_eq_boundaryWeight
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 1 ≤ R) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    originalScreeningOrientedReflectedInputMass b R C c =ᵐ[(Q.law : Measure _)]
      fun scene ↦ ∫ p, originalScreeningOrientedInputClassBoundaryWeight b R C p
        ∂legalInputColorMeasure q scene.2 c := by
  filter_upwards [Q.ae_finite_orientedReflectedInputOuterWindow b (2*R) c] with scene hs
  exact integral_originalOrientedClassReflectedInputScalarField_eq_boundaryWeight b hR hC _ hs

end OTSelector.Reconstruction
