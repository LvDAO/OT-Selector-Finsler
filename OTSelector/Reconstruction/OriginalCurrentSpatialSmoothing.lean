import OTSelector.Analysis.Calculus.CompactKernelCurrent
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessLocalTraffic
import OTSelector.Reconstruction.OriginalMinimizerPrefixCurrentCentering

/-! Genuine Fubini identification of spatial smoothing with the same original clock-set current. -/

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

/-- The actual compact spatial kernel is integrable on original pair times restricted clock,
using precisely the same original occupation's compact-local absolute traffic. -/
theorem integrable_originalClockOccupation_spatialKernel
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (A : Set ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ B : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact B →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        B.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A s))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    Integrable (fun p : OriginalClockOccupationPoint S ↦
      η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p)
      (originalClockOccupationMeasure S A s) :=
  integrable_compact_kernel_current hη hcη
    (measurable_originalClockOccupationPosition S hF hw)
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable htraffic z

/-- The literal product-occupation smoothing equals the whole same original clock-set current
with its spatial kernel translated by `z`. Product integrability is proved from local traffic,
then genuine Fubini exchanges the original pair and clock integrals. -/
theorem integral_originalClockOccupation_spatialKernel_eq_current
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (A : Set ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (htraffic : ∀ B : Set (Fin (finrank ℝ S.covector.ker) → ℝ), IsCompact B →
      Integrable (fun p : OriginalClockOccupationPoint S ↦
        B.indicator (fun _ ↦ ‖originalClockOccupationVelocity S w p‖)
          (originalClockOccupationPosition S w p)) (originalClockOccupationMeasure S A s))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (∫ p : OriginalClockOccupationPoint S,
        η (originalClockOccupationPosition S w p - z) • originalClockOccupationVelocity S w p
        ∂originalClockOccupationMeasure S A s) =
      originalSeedPathClockSetCurrent S w (fun x ↦ η (x - z)) A s := by
  have hi := integrable_originalClockOccupation_spatialKernel S hF hw hη hcη A s htraffic z
  exact integral_prod_symm _ hi

end OTSelector.Reconstruction
