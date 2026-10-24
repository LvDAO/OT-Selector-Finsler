import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficSupport
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume
import OTSelector.MeasureTheory.Integral.ShellBulkBound

/-! Actual same-frame omitted square traffic has a true collar-plus-long-path bound. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Deep same-frame observation points see only genuine long omitted paths; stationarity
is applied to the original unchanged matching and the original unchanged physical kernel. -/
theorem lintegral_original_oriented_deepOmittedTraffic_sq_le_longPath_sq
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {R ell radius : ℝ} (hell : 0 ≤ ell) (hradius : 0 ≤ radius)
    (hR : 3 * (originalStageFrameCollarFactor b * ell) +
      originalStageFrameCollarFactor b * radius ≤ R)
    (hηsupport : ∀ x, radius < ‖x‖ → η x = 0)
    {z : Fin (finrank ℝ S.covector.ker) → ℝ}
    (hz : z ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - (3 * (originalStageFrameCollarFactor b * ell) +
        originalStageFrameCollarFactor b * radius)))) :
    (∫⁻ scene, originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z))
        (originalOrientedPathLengthRetained S w b R ell)ᶜ scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
    ∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η ell scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
  have hC : 0 ≤ originalStageFrameCollarFactor b := by
    linarith [one_le_originalStageFrameCollarFactor b]
  have hsupport : ∀ y, η (y-z) ≠ 0 → y ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - 3 * (originalStageFrameCollarFactor b * ell))) :=
    translated_kernel_support_in_originalOrientedCube b hradius (by linarith) hηsupport
      (by simpa only [sub_sub] using hz)
  calc
    _ ≤ ∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w (fun x ↦ η (x-z)) ell scene ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_original_oriented_omittedPathTraffic_le_longPathTraffic hF hw b Q
        hell (by linarith [mul_nonneg hC hradius]) hsupport] with scene hscene
      exact pow_le_pow_left' hscene 2
    _ = _ := Q.lintegral_original_longPathTraffic_sq_shift hF hw hη ell z

/-- The genuine actual omitted square traffic in the same selected physical cube is
bounded by full traffic times its genuine collar volume plus original long-path square
traffic times the same physical cube volume. No rotation of the original law is made. -/
theorem lintegral_original_oriented_wholeCube_omittedTraffic_sq_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {R ell radius : ℝ} (hell : 0 ≤ ell) (hradius : 0 ≤ radius)
    (hR : 3 * (originalStageFrameCollarFactor b * ell) +
      originalStageFrameCollarFactor b * radius ≤ R)
    (hηsupport : ∀ x, radius < ‖x‖ → η x = 0) :
    (∫⁻ scene, ∫⁻ z in originalCenteredPhysicalCubeRegion b (2 * R),
      originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z))
        (originalOrientedPathLengthRetained S w b R ell)ᶜ scene ^ 2 ∂volume
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
    (∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) *
        volume (originalCenteredPhysicalCubeRegion b (2 * R) \
          originalCenteredPhysicalCubeRegion b
            (2 * (R - (3 * (originalStageFrameCollarFactor b * ell) +
              originalStageFrameCollarFactor b * radius)))) +
    (∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η ell scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) *
        volume (originalCenteredPhysicalCubeRegion b (2 * R)) := by
  have hA := (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell).compl
  have hmeas := (measurable_original_restrictedPathTraffic_shift_joint hF hw hη hA).pow_const 2
  rw [← lintegral_lintegral_swap hmeas.aemeasurable]
  apply lintegral_on_le_shell_and_bulk volume
    (measurableSet_originalOrientedTraffic_cube b R)
    (measurableSet_originalOrientedTraffic_cube b _)
  · intro z hz
    calc
      _ ≤ ∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w (fun x ↦ η (x-z)) scene ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
        apply lintegral_mono
        intro scene
        exact pow_le_pow_left' (originalSeedRestrictedPathAbsoluteTraffic_le_full S w
          (fun x ↦ η (x-z)) _ scene) 2
      _ = _ := Q.lintegral_original_fullTraffic_sq_shift hF hw hη z
  · intro z hz
    exact D.lintegral_original_oriented_deepOmittedTraffic_sq_le_longPath_sq
      hF hw b Q hη hell hradius hR hηsupport hz

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
