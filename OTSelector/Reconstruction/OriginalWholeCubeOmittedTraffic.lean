import OTSelector.Reconstruction.OriginalSpatialTrafficSquare
import OTSelector.MeasureTheory.Integral.ShellBulkBound

/-! # Actual whole-cube omitted traffic has a collar-plus-long-path square bound -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The omitted original absolute current has its exact spatially integrated
second-moment bound: a genuine original boundary collar plus the stationary
long-path traffic square. No tail rate or endpoint-square moment is assumed. -/
theorem lintegral_original_wholeCube_omittedTraffic_sq_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {R ell radius : ℝ} (hell : 0 ≤ ell) (hradius : 0 ≤ radius)
    (hR : 3 * ell + radius ≤ R) (hηsupport : ∀ x, radius < ‖x‖ → η x = 0) :
    (∫⁻ scene, ∫⁻ z in haarRootCube (Fin (finrank ℝ S.covector.ker)) R,
      originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x - z))
        (originalPathLengthRetained S w R ell)ᶜ scene ^ 2 ∂volume
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
    (∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) *
        volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R \
          haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell - radius)) +
    (∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η ell scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) *
        volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) := by
  have hA := (measurableSet_originalPathLengthRetained S hF hw R ell).compl
  have hmeas := (measurable_original_restrictedPathTraffic_shift_joint hF hw hη hA).pow_const 2
  rw [← lintegral_lintegral_swap hmeas.aemeasurable]
  apply lintegral_on_le_shell_and_bulk volume measurableSet_Icc measurableSet_Icc
  · intro z hz
    calc
      _ ≤ ∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w (fun x ↦ η (x - z)) scene ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
        apply lintegral_mono
        intro scene
        exact pow_le_pow_left' (originalSeedRestrictedPathAbsoluteTraffic_le_full S w
          (fun x ↦ η (x - z)) _ scene) 2
      _ = _ := Q.lintegral_original_fullTraffic_sq_shift hF hw hη z
  · intro z hz
    exact D.lintegral_original_deepOmittedTraffic_sq_le_longPath_sq hF hw Q hη hell hradius hR hηsupport hz

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
