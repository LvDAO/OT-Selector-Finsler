import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedRetentionGeometry
import OTSelector.Reconstruction.OriginalSpatialTrafficSquare

/-! Actual omitted original paths in one fixed physical cube orientation. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm

/-- A raw compact kernel translated in the same physical frame has its support in the
larger same-frame cube. Only its actual inverse-frame operator norm enlarges the collar. -/
theorem translated_kernel_support_in_originalOrientedCube
    {q : ℕ} (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {η : (Fin q → ℝ) → ℝ} {R radius : ℝ}
    (hradius : 0 ≤ radius) (hR : originalStageFrameCollarFactor b * radius ≤ R)
    (hηsupport : ∀ x, radius < ‖x‖ → η x = 0)
    {z : Fin q → ℝ}
    (hz : z ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - originalStageFrameCollarFactor b * radius))) :
    ∀ y, η (y-z) ≠ 0 → y ∈ originalCenteredPhysicalCubeRegion b (2 * R) := by
  intro y hy
  have hC : 0 ≤ originalStageFrameCollarFactor b := by
    linarith [one_le_originalStageFrameCollarFactor b]
  have hyz : ‖y-z‖ ≤ radius := by
    by_contra h
    exact hy (hηsupport _ (lt_of_not_ge h))
  rw [mem_originalCenteredPhysicalCubeRegion_iff] at hz ⊢
  have hhalf (r : ℝ) : 2 * r / 2 = r := by ring
  rw [hhalf] at hz ⊢
  have hzN := (mem_haarRootCube_iff_norm_le (sub_nonneg.mpr hR) _).mp hz
  apply (mem_haarRootCube_iff_norm_le ((mul_nonneg hC hradius).trans hR) _).mpr
  have hd := (norm_inverse_originalStageFrame_le b (y-z)).trans
    (mul_le_mul_of_nonneg_left hyz hC)
  rw [map_sub] at hd
  have hn := norm_le_norm_sub_add ((orthonormalPhysicalCubeMap b).symm y)
    ((orthonormalPhysicalCubeMap b).symm z)
  linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- A short unchanged original path omitted by the same-frame retained set contributes
zero traffic to a kernel supported in that frame's genuine deep physical cube. -/
theorem original_oriented_omitted_shortPath_clockIntegral_eq_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell)
    (hR : 3 * (originalStageFrameCollarFactor b * ell) ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηsupport : ∀ y, η y ≠ 0 → y ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - 3 * (originalStageFrameCollarFactor b * ell))))
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (homitted : (x,m) ∉ originalOrientedPathLengthRetained S w b R ell)
    (hshort : originalSeedPairPathLength S w m ≤ ell) :
    (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ ∂volume) = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro c
  change ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
    ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ = 0
  by_cases hc : c ∈ Ico m.1.1 m.1.2
  · have hηzero : η (x + originalSeedPathOffset S w c m) = 0 := by
      by_contra hne
      have hp := hηsupport _ hne
      rw [← originalSeedCompletePath_eq_anchor_add_offset] at hp
      exact homitted (D.originalOrientedPathLengthRetained_of_path_mem_deepCube hF hw b
        hell hR ha hb (Ico_subset_Icc_self hc) hp hshort)
    simp only [hηzero, ENNReal.ofReal_zero, zero_mul]
  · rw [originalSeedClockOccupation_eq_indicator_velocity, indicator_of_notMem hc]
    simp

/-- The genuine omitted traffic in any same-frame deep-supported kernel is bounded by
the unchanged stationary original long-path traffic; the matching law is never rotated. -/
theorem ae_original_oriented_omittedPathTraffic_le_longPathTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell)
    (hR : 3 * (originalStageFrameCollarFactor b * ell) ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηsupport : ∀ y, η y ≠ 0 → y ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - 3 * (originalStageFrameCollarFactor b * ell)))) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalSeedRestrictedPathAbsoluteTraffic S w η
        (originalOrientedPathLengthRetained S w b R ell)ᶜ scene ≤
      originalSeedLongPathAbsoluteTraffic S w η ell scene := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hscene
  rw [originalSeedRestrictedPathAbsoluteTraffic,
    ← lintegral_indicator (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell).compl,
    originalSeedLongPathAbsoluteTraffic_eq_pairTail]
  apply lintegral_mono_ae
  filter_upwards [hscene] with a ha
  by_cases hret : a ∈ originalOrientedPathLengthRetained S w b R ell
  · rw [indicator_of_notMem (show a ∉ (originalOrientedPathLengthRetained S w b R ell)ᶜ from
      fun h ↦ h hret)]
    exact zero_le
  · rw [indicator_of_mem (show a ∈ (originalOrientedPathLengthRetained S w b R ell)ᶜ from hret)]
    by_cases hlong : ell < originalSeedPairPathLength S w a.2
    · simp only [hlong, ite_true, le_refl]
    · simpa only [hlong, ite_false] using le_of_eq
        (D.original_oriented_omitted_shortPath_clockIntegral_eq_zero hF hw b hell hR hηsupport
          ha.1 ha.2.1 hret (le_of_not_gt hlong))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
