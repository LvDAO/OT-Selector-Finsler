import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetFluxCoordinates

/-! The actual original physical full-current flux has the proved surface-scale second moment. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {μ ν : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
  (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
  (j : LegalMarkedOptimalInputScene q → Fin q → ℝ)
  (hj : ∀ k, MemLp (fun scene ↦ j scene k) 2 (Q.law : Measure _))

/-- Every actual rerooted spatial-current flux is the raw Hilbert face flux of the very
same frame and physical cube, on a single original-scene event. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalScreening_physicalFlux_eq_raw
    (hm : Measurable j) (R : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      originalScreeningPhysicalCurrentBoundaryPairing b
        (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) (2*R) (fun _ ↦ 1) =
      Q.sceneRawCenteredCubeFlux b
        (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
          (originalEuclideanNormalReadout (b i))) R scene := by
  cases q with
  | zero =>
    apply Eventually.of_forall
    intro scene
    simp [originalScreeningPhysicalCurrentBoundaryPairing,
      LegalWeightedStationaryPoissonMatching.sceneRawCenteredCubeFlux]
  | succ r =>
    filter_upwards [Q.ae_all_originalCurrent_physicalCube_pairing_eq b j hj hm (2*R)] with scene hs
    exact (hs (fun _ ↦ 1)).symm.trans
      (Q.sceneRawCenteredCubeFlux_eq_physicalConstantPairing b _ R scene).symm

include hj in
/-- The literal physical full-current flux has a finite second moment at every positive
radius; no selected-face variance or boundary integrability is supplied as a premise. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_sq_originalScreening_physicalFlux
    (hm : Measurable j) {R : ℝ} (hR : 0 < R) :
    Integrable (fun scene ↦ (originalScreeningPhysicalCurrentBoundaryPairing b
      (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) (2*R) (fun _ ↦ 1))^2)
        (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  apply (Q.integrable_sq_sceneRawCenteredCubeFlux b _ hR).congr
  filter_upwards [Q.ae_originalScreening_physicalFlux_eq_raw b j hj hm R] with scene hs
  exact congrArg (fun x : ℝ ↦ x^2) hs.symm

/-- Actual zero normal face projections imply the true literal full flux is negligible
in surface-scale L2, using the proved coordinate-area identity and original-scene law. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalScreening_physicalFlux_normalized_sq_zero
    (hm : Measurable j)
    (hproj : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
        (originalEuclideanNormalReadout (b i))) = 0) :
    Tendsto (fun R : ℝ ↦ ∫ scene,
      ((R^(q-1))⁻¹ * originalScreeningPhysicalCurrentBoundaryPairing b
        (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) (2*R) (fun _ ↦ 1))^2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) atTop (𝓝 0) := by
  have h := Q.tendsto_integral_sq_normalized_sceneRawCenteredCubeFlux_zero b _ hproj
  apply h.congr'
  apply Eventually.of_forall
  intro R
  apply integral_congr_ae
  filter_upwards [Q.ae_originalScreening_physicalFlux_eq_raw b j hj hm R] with scene hs
  rw [hs]

end OTSelector.Reconstruction
