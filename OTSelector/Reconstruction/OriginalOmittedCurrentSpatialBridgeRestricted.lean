import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeMeasurability
import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeNorm

/-! Spatial regularity and actual traffic bounds for any original pair restriction. -/
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

/-- Genuine Fubini identifies any actual pair-restricted product occupation with its literal
clock-outer original current, using local traffic inherited from the unchanged full law. -/
theorem integral_originalPairRestrictedClockOccupation_spatialKernel_eq_current
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (∫ p : OriginalClockOccupationPoint S,
        η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalPairRestrictedClockOccupationMeasure S B A scene) =
      originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene := by
  exact integral_prod_symm _
    (integrable_originalPairRestrictedClockOccupation_spatialKernel S hF hw
      hη hcη B A scene htraffic z)

/-- Any actual restricted original current is C¹ and its true Fréchet derivative is the
integral of the differentiated compact kernel against the same restricted occupation. -/
theorem originalPairRestrictedCurrent_spatially_contDiff_derivative
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene)) :
    ContDiff ℝ 1 (fun z ↦
      originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene) ∧
    ∀ z, HasFDerivAt (fun z ↦
      originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene)
      (∫ p : OriginalClockOccupationPoint S,
        (-(fderiv ℝ η (originalClockOccupationPosition S w p - z))).smulRight
          (originalClockOccupationVelocity S w p)
        ∂originalPairRestrictedClockOccupationMeasure S B A scene) z := by
  have heq : (fun z ↦
      originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene) =
      fun z ↦ ∫ p : OriginalClockOccupationPoint S,
        η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalPairRestrictedClockOccupationMeasure S B A scene :=
    funext (fun z ↦ (integral_originalPairRestrictedClockOccupation_spatialKernel_eq_current
      S hF hw hη.continuous hcη B A scene htraffic z).symm)
  rw [heq]
  have hX := measurable_originalClockOccupationPosition S hF hw
  have hV : AEStronglyMeasurable (originalClockOccupationVelocity S w)
      (originalPairRestrictedClockOccupationMeasure S B A scene) :=
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
  have htr := integrable_originalPairRestrictedClockOccupation_compact_weight S B A scene htraffic
  exact ⟨contDiff_compact_kernel_current hη hcη hX hV htr,
    hasFDerivAt_compact_kernel_current hη hcη hX hV htr⟩

/-- The divergence of any actual restricted field is the negative literal restricted
clock-occupation derivative, retaining the true original pairs, clocks and velocities. -/
theorem divergence_originalPairRestrictedCurrent_spatial
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (∑ i : Fin (finrank ℝ S.covector.ker),
      fderiv ℝ (fun z ↦
        originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene)
        z (Pi.single i 1) i) =
      -(∫ a in B, ∫ c in A, fderiv ℝ (fun x ↦ η (x-z))
        (a.1 + originalSeedPathOffset S w c a.2) (originalSeedClockOccupation S w c a.2)
        ∂volume ∂physicalScenePairKernel scene.1) := by
  have heq : (fun z ↦
      originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene) =
      fun z ↦ ∫ p : OriginalClockOccupationPoint S,
        η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalPairRestrictedClockOccupationMeasure S B A scene :=
    funext (fun z ↦ (integral_originalPairRestrictedClockOccupation_spatialKernel_eq_current
      S hF hw hη.continuous hcη B A scene htraffic z).symm)
  have hX := measurable_originalClockOccupationPosition S hF hw
  have hV : AEStronglyMeasurable (originalClockOccupationVelocity S w)
      (originalPairRestrictedClockOccupationMeasure S B A scene) :=
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
  have htr := integrable_originalPairRestrictedClockOccupation_compact_weight S B A scene htraffic
  rw [heq, divergence_compact_kernel_current hη hcη hX hV htr z]
  congr 1
  simp only [fderiv_comp_sub]
  exact integral_prod _ (integrable_compact_kernel_gradientPairing hη hcη hX hV htr z)

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- One original-scene event supplies the true C¹ current and derivative for every actual
pair restriction, clock set and compact C¹ kernel, including oriented retention regions. -/
theorem ae_all_originalPairRestrictedCurrent_spatially_contDiff_derivative
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (B : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
          PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) (A : Set ℝ)
        (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η →
        ContDiff ℝ 1 (fun z ↦
          originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene) ∧
        ∀ z, HasFDerivAt (fun z ↦
          originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene)
          (∫ p : OriginalClockOccupationPoint S,
            (-(fderiv ℝ η (originalClockOccupationPosition S w p - z))).smulRight
              (originalClockOccupationVelocity S w p)
            ∂originalPairRestrictedClockOccupationMeasure S B A scene) z := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q]
    with scene hs
  intro B A η hη hcη
  exact originalPairRestrictedCurrent_spatially_contDiff_derivative S hF hw hη hcη
    B A scene (hs A)

/-- Actual restricted complete-path traffic is finite and bounds the same actual restricted
current, on one original-scene event for every restriction and nonnegative compact kernel. -/
theorem ae_all_originalPairRestrictedCurrent_norm_le_traffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (B : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
          PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) (A : Set ℝ)
        (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        Continuous η → HasCompactSupport η → (∀ x, 0 ≤ η x) → ∀ z,
        originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) B scene < ⊤ ∧
        ‖originalPairRestrictedSeedPathClockSetCurrent S w B (fun x ↦ η (x-z)) A scene‖ ≤
          (originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z)) B scene).toReal := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q]
    with scene hs
  intro B A η hη hcη hη0 z
  have ht := originalPairRestrictedClockOccupation_spatialKernel_traffic_lt_top S hF hw
    hη hcη hη0 B scene (hs univ) z
  refine ⟨ht, ?_⟩
  rw [← integral_originalPairRestrictedClockOccupation_spatialKernel_eq_current S hF hw
    hη hcη B A scene (hs A) z]
  simpa only [toReal_enorm] using ENNReal.toReal_mono ht.ne
    (originalPairRestrictedClockOccupation_spatialKernel_enorm_le_traffic S hF hw
      hη.measurable hη0 B A scene z)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
