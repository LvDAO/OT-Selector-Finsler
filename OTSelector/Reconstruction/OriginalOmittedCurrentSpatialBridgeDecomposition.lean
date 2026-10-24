import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeOccupation

/-! The actual omitted occupation is precisely full current minus retained current. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Genuine Fubini identifies the retained product smoothing with the literal retained current. -/
theorem integral_originalRetainedClockOccupation_spatialKernel_eq_current
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (∫ p : OriginalClockOccupationPoint S,
        η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalPairRestrictedClockOccupationMeasure S
          (originalPathLengthRetained S w R ell) A scene) =
      originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-z)) A scene := by
  have hi := integrable_originalPairRestrictedClockOccupation_spatialKernel S hF hw hη hcη
    (originalPathLengthRetained S w R ell) A scene htraffic z
  exact integral_prod_symm _ hi

/-- The actual omitted product current equals the literal full-minus-retained field. -/
theorem originalFull_sub_retainedCurrent_eq_omittedOccupation
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) A scene -
        originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-z)) A scene =
      ∫ p : OriginalClockOccupationPoint S,
        η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalPairRestrictedClockOccupationMeasure S
          (originalPathLengthRetained S w R ell)ᶜ A scene := by
  have hi := integrable_originalPairRestrictedClockOccupation_spatialKernel S hF hw hη hcη
    (originalPathLengthRetained S w R ell) A scene htraffic z
  have hic := integrable_originalPairRestrictedClockOccupation_spatialKernel S hF hw hη hcη
    (originalPathLengthRetained S w R ell)ᶜ A scene htraffic z
  have hsum := integral_add_measure hi hic
  rw [originalPairRestrictedClockOccupationMeasure_add_compl S _
    (measurableSet_originalPathLengthRetained S hF hw R ell)] at hsum
  rw [← integral_originalClockOccupation_spatialKernel_eq_current S hF hw hη hcη A scene htraffic z,
    ← integral_originalRetainedClockOccupation_spatialKernel_eq_current S hF hw R ell
      hη hcη A scene htraffic z, hsum, add_sub_cancel_left]

end OTSelector.Reconstruction
