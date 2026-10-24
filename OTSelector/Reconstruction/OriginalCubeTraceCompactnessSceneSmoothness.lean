import OTSelector.Reconstruction.OriginalCurrentSpatialSmoothing
import OTSelector.Reconstruction.OriginalCurrentSpatialReroot

/-! The actual original clock-set current is spatially C¹ in almost every original scene. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Genuine original complete-path first traffic produces spatial C¹ regularity on a single
full-measure set, for every compact C¹ kernel and every original clock restriction. -/
theorem ae_all_originalClockSetCurrent_spatially_contDiff
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η →
        ContDiff ℝ 1 (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x - z)) A s) := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q]
    with s hs
  intro A η hη hcη
  have heq := funext (integral_originalClockOccupation_spatialKernel_eq_current
    S hF hw hη.continuous hcη A s (hs A))
  rw [← heq]
  exact contDiff_compact_kernel_current hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable (hs A)

/-- The actual original spatial derivative is obtained by differentiating the original
compact kernel inside the unchanged pair-times-clock occupation integral. -/
theorem ae_all_hasFDerivAt_originalClockSetCurrent_spatial
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ z,
        HasFDerivAt
          (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x - z)) A s)
          (∫ p : OriginalClockOccupationPoint S,
            (-(fderiv ℝ η (originalClockOccupationPosition S w p - z))).smulRight
              (originalClockOccupationVelocity S w p) ∂originalClockOccupationMeasure S A s) z := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q]
    with s hs
  intro A η hη hcη z
  have heq := funext (integral_originalClockOccupation_spatialKernel_eq_current
    S hF hw hη.continuous hcη A s (hs A))
  rw [← heq]
  exact hasFDerivAt_compact_kernel_current hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable (hs A) z

/-- In every true spatial direction the actual derivative is the literal differentiated
original kernel integral, with the negative sign from the translate `x - z`. -/
theorem ae_all_fderiv_originalClockSetCurrent_spatial_apply
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ z h,
        fderiv ℝ (fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x - z)) A s) z h =
          ∫ p : OriginalClockOccupationPoint S,
            (-(fderiv ℝ η (originalClockOccupationPosition S w p - z) h)) •
              originalClockOccupationVelocity S w p ∂originalClockOccupationMeasure S A s := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q]
    with s hs
  intro A η hη hcη z h
  have heq := funext (integral_originalClockOccupation_spatialKernel_eq_current
    S hF hw hη.continuous hcη A s (hs A))
  rw [← heq]
  exact fderiv_compact_kernel_current_apply hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable (hs A) z h

/-- The stationary reroot representation of the same original smoothed current is genuinely
C¹ in space. Its regularity follows from original first traffic, rather than being assumed. -/
theorem ae_all_originalClockSetCurrent_reroot_contDiff
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η →
        ContDiff ℝ 1 (fun z ↦ originalSeedPathClockSetCurrent S w η A
          (legalMarkedInputSceneReroot (finrank ℝ S.covector.ker) z s)) := by
  filter_upwards [D.ae_all_originalClockSetCurrent_spatially_contDiff hF hw hbounds Q]
    with s hs
  intro A η hη hcη
  simpa only [originalSeedPathClockSetCurrent_reroot S hF hw hη.continuous.measurable]
    using hs A η hη hcη

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
