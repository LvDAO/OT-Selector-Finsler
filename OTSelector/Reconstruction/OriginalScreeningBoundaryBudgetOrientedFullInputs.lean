import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetFullInputs
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedReflectedMass
import OTSelector.Reconstruction.OriginalOrientedCubeReflectedFubini
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessOrientedPoissonMoments

/-! Exact actual physical-frame full-input reflected-density splitting. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The same marked endpoint density, kernel and physical window are exactly their genuine
raw-frame readout; all original input marks are retained under an actual measurable equivalence. -/
theorem originalOrientedStageReflectedClassDensity_eq_raw_map {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) (C : Set ℝ)
    (σ : Measure (LegalMarkedPhysicalPoint q)) (z : Fin q → ℝ) :
    originalOrientedStageReflectedClassDensity b R C
      (σ.restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}) z =
      originalStageReflectedClassDensity (originalEuclideanMollifier q) R C
        ((σ.map (originalOrientedInputCoordinates b)).restrict {p | p.1 ∈ haarRootCube (Fin q) R})
        ((orthonormalPhysicalCubeMap b).symm z) := by
  let e := originalOrientedInputCoordinates b
  have hwindow : e ⁻¹' {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} =
      {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)} := by
    ext p
    change (orthonormalPhysicalCubeMap b).symm p.1 ∈ haarRootCube (Fin q) R ↔
      p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)
    rw [mem_originalCenteredPhysicalCubeRegion_iff, show (2*R)/2 = R by ring]
  rw [e.restrict_map, hwindow]
  unfold originalOrientedStageReflectedClassDensity originalStageReflectedClassDensity
  rw [setIntegral_map_equiv e]
  rfl

/-- Genuine physical full-input reflected smoothing is ordinary physical smoothing plus
the literal physical reflection error; finite expanded-window mass suffices for infinite input. -/
theorem originalOrientedFullInputReflectedClassDensity_eq_raw_add_response {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C) (σ : Measure (LegalMarkedPhysicalPoint q))
    (hσ : σ (originalCenteredPhysicalCubeRegion b (2*R+2) ×ˢ (univ : Set ℝ)) < ∞)
    {z : Fin q → ℝ} (hz : z ∈ originalCenteredPhysicalCubeRegion b (2*R)) :
    originalOrientedStageReflectedClassDensity b R C
      (σ.restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}) z =
      (∫ p in {p | p.2 ∈ C}, originalEuclideanMollifier q (z-p.1) ∂σ) +
        originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier q) (2*R) C σ z := by
  let e := originalOrientedInputCoordinates b
  let σraw := σ.map e
  have hhalf : (2*R)/2 = R := by ring
  have hraw : σraw (haarRootCube (Fin q) (R+1) ×ˢ (univ : Set ℝ)) < ∞ := by
    have hw := map_oriented_input_outerWindow b (2*R) σ
    simp only [hhalf] at hw
    exact hw.trans_lt hσ
  have hzraw : (orthonormalPhysicalCubeMap b).symm z ∈ haarRootCube (Fin q) R := by
    simpa only [hhalf] using (mem_originalCenteredPhysicalCubeRegion_iff b (2*R) z).mp hz
  rw [originalOrientedStageReflectedClassDensity_eq_raw_map]
  rw [originalFullInputReflectedClassDensity_eq_raw_add_response
    (contDiff_originalEuclideanMollifier q).continuous.measurable
    (originalEuclideanMollifierBound_nonneg q) (abs_originalEuclideanMollifier_le q)
    (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)) hR hC σraw hraw hzraw]
  rw [originalOrientedClassReflectedInputScalarField_eq_raw_map_of_radial b
    (originalEuclideanMollifier_radial q)]
  simp only [hhalf]
  congr 1
  change (∫ p in {p | p.2 ∈ C}, originalEuclideanMollifier q
    ((orthonormalPhysicalCubeMap b).symm z-p.1) ∂σ.map e) = _
  rw [setIntegral_map_equiv e]
  apply setIntegral_congr_fun (hC.preimage measurable_snd)
  intro p _
  change originalEuclideanMollifier q
    ((orthonormalPhysicalCubeMap b).symm z-(orthonormalPhysicalCubeMap b).symm p.1) = _
  rw [← map_sub, originalEuclideanMollifier_inverse_frame]

end OTSelector.Reconstruction
