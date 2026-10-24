import OTSelector.Reconstruction.OriginalCurrentSmoothedDivergence
import OTSelector.Reconstruction.OriginalRetainedSlabResidualBoundaryCurrent

/-! Pair restrictions inherit the actual original local traffic and its C¹ smoothing. -/
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

/-- The unchanged original pairs restricted to `B`, times the unchanged clock restriction. -/
def originalPairRestrictedClockOccupationMeasure (S : CalibratedLevelSeedPatch F u)
    (B : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (OriginalClockOccupationPoint S) :=
  ((physicalScenePairKernel scene.1).restrict B).prod (volume.restrict A)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Every pair restriction is dominated by the same actual full occupation. -/
theorem originalPairRestrictedClockOccupationMeasure_le
    (S : CalibratedLevelSeedPatch F u) (B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalPairRestrictedClockOccupationMeasure S B A scene ≤
      originalClockOccupationMeasure S A scene :=
  Measure.prod_mono Measure.restrict_le_self le_rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A measurable pair restriction and its complement add to the actual full occupation. -/
theorem originalPairRestrictedClockOccupationMeasure_add_compl
    (S : CalibratedLevelSeedPatch F u) (B) (hB : MeasurableSet B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalPairRestrictedClockOccupationMeasure S B A scene +
        originalPairRestrictedClockOccupationMeasure S Bᶜ A scene =
      originalClockOccupationMeasure S A scene := by
  unfold originalPairRestrictedClockOccupationMeasure originalClockOccupationMeasure
  rw [← Measure.add_prod, Measure.restrict_add_restrict_compl hB]

omit [BorelSpace E] in
/-- All pair restrictions inherit compact local traffic from the original full occupation. -/
theorem integrable_originalPairRestrictedClockOccupation_compact_weight
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker}
    (B) (A : Set ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene))
    (K : Set (Fin (finrank ℝ S.covector.ker) → ℝ)) (hK : IsCompact K) :
    Integrable (fun p : OriginalClockOccupationPoint S ↦
      K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
        (originalClockOccupationPosition S w p))
      (originalPairRestrictedClockOccupationMeasure S B A scene) :=
  (htraffic K hK).mono_measure (originalPairRestrictedClockOccupationMeasure_le S B A scene)

/-- The literal restricted current integrand is integrable, without a new traffic premise. -/
theorem integrable_originalPairRestrictedClockOccupation_spatialKernel
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
    Integrable (fun p : OriginalClockOccupationPoint S ↦
      η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p)
      (originalPairRestrictedClockOccupationMeasure S B A scene) :=
  integrable_compact_kernel_current hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
    (integrable_originalPairRestrictedClockOccupation_compact_weight S B A scene htraffic) z

/-- Actual pair-restricted smoothing is C¹ under the same original local traffic. -/
theorem contDiff_originalPairRestrictedClockOccupation_spatialKernel
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (B) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ K : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact K →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        K.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A scene)) :
    ContDiff ℝ 1 (fun z ↦ ∫ p : OriginalClockOccupationPoint S,
      η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalPairRestrictedClockOccupationMeasure S B A scene) :=
  contDiff_compact_kernel_current hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
    (integrable_originalPairRestrictedClockOccupation_compact_weight S B A scene htraffic)

end OTSelector.Reconstruction
