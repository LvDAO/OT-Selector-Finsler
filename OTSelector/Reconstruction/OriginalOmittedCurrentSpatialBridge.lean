import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeDecomposition
import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutPositiveSmoothing

/-! Actual full-minus-retained current is C¹ and has the frozen omitted slab derivative. -/
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

/-- Actual compact local occupation makes the literal full-minus-retained field C¹ and
identifies its divergence with the unchanged omitted derivative, including its sign. -/
theorem originalOmittedCurrent_spatially_contDiff_divergence
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p))
        (originalClockOccupationMeasure S (Ioc s t) scene))
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ContDiff ℝ 1 (fun z ↦
      originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene -
      originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-z)) (Ioc s t) scene) ∧
    ∀ z, originalOmittedSmoothedSlabDerivative S w R ell s t η z scene =
      ∑ i : Fin (finrank ℝ S.covector.ker),
        fderiv ℝ (fun z ↦
          originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene -
          originalRetainedSeedPathClockSetCurrent S w R ell
            (fun x ↦ η (x-z)) (Ioc s t) scene) z (Pi.single i 1) i := by
  have hX := measurable_originalClockOccupationPosition S hF hw
  have hV : AEStronglyMeasurable (originalClockOccupationVelocity S w)
      (originalPairRestrictedClockOccupationMeasure S
        (originalPathLengthRetained S w R ell)ᶜ (Ioc s t) scene) :=
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
  have htr := integrable_originalPairRestrictedClockOccupation_compact_weight S
    (originalPathLengthRetained S w R ell)ᶜ (Ioc s t) scene htraffic
  have heq : (fun z ↦
      originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene -
      originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-z)) (Ioc s t) scene) =
      fun z ↦ ∫ p : OriginalClockOccupationPoint S,
        η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalPairRestrictedClockOccupationMeasure S
          (originalPathLengthRetained S w R ell)ᶜ (Ioc s t) scene :=
    funext (originalFull_sub_retainedCurrent_eq_omittedOccupation S hF hw R ell
      hη.continuous hcη (Ioc s t) scene htraffic)
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact contDiff_compact_kernel_current hη hcη hX hV htr
  · intro z
    rw [heq, divergence_compact_kernel_current hη hcη hX hV htr z]
    have hi := integrable_compact_kernel_gradientPairing hη hcη hX hV htr z
    change -(∫ a in (originalPathLengthRetained S w R ell)ᶜ,
      (∫ c in Ioc s t, fderiv ℝ (fun x ↦ η (x-z))
        (a.1 + originalSeedPathOffset S w c a.2)
        (originalSeedClockOccupation S w c a.2) ∂volume) ∂physicalScenePairKernel scene.1) = _
    congr 1
    simp only [fderiv_comp_sub]
    exact (integral_prod _ hi).symm

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- One full-measure set works for all actual retained regions, clock slabs and compact C¹
kernels. Local traffic, the C¹ field, and its exact divergence are produced from the original
weighted matching rather than supplied as completed regularity assumptions. -/
theorem ae_all_originalOmittedCurrent_spatially_contDiff_divergence
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (R ell s t : ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η →
        ContDiff ℝ 1 (fun z ↦
          originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene -
          originalRetainedSeedPathClockSetCurrent S w R ell
            (fun x ↦ η (x-z)) (Ioc s t) scene) ∧
        ∀ z, originalOmittedSmoothedSlabDerivative S w R ell s t η z scene =
          ∑ i : Fin (finrank ℝ S.covector.ker),
            fderiv ℝ (fun z ↦
              originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene -
              originalRetainedSeedPathClockSetCurrent S w R ell
                (fun x ↦ η (x-z)) (Ioc s t) scene) z (Pi.single i 1) i := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q]
    with scene hs
  intro R ell s t η hη hcη
  exact originalOmittedCurrent_spatially_contDiff_divergence S hF hw R ell s t scene
    (hs (Ioc s t)) hη hcη

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
