import OTSelector.Reconstruction.OriginalTargetPortCountExpectation
import OTSelector.Reconstruction.OriginalLongPathAbsoluteTraffic

/-! # Exact retained and omitted original complete-path traffic -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Literal original complete-path absolute traffic restricted to a fixed
Borel set of unchanged source anchors and full paired marks. -/
def originalSeedRestrictedPathAbsoluteTraffic (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  ∫⁻ a in A, ∫⁻ c : ℝ,
    ENNReal.ofReal (η (a.1 + originalSeedPathOffset S w c a.2)) *
      ENNReal.ofReal ‖originalSeedClockOccupation S w c a.2‖ ∂volume
    ∂physicalScenePairKernel scene.1

/-- Restrictions of the original traffic remain Borel original-scene readouts. -/
theorem measurable_originalSeedRestrictedPathAbsoluteTraffic
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hA : MeasurableSet A) :
    Measurable (originalSeedRestrictedPathAbsoluteTraffic S w η A) := by
  let H := fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    ∫⁻ c : ℝ, ENNReal.ofReal (η (a.1 + originalSeedPathOffset S w c a.2)) *
      ENNReal.ofReal ‖originalSeedClockOccupation S w c a.2‖ ∂volume
  have hH : Measurable H := by
    have h := (hη.ennreal_ofReal.comp (measurable_fst.fst.add
      ((measurable_originalSeedPathOffset_joint S hF hw).comp
        (measurable_fst.snd.prodMk measurable_snd)))).mul
      (((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal).comp
        (measurable_fst.snd.prodMk measurable_snd))
    exact h.lintegral_prod_right'
  have hread := (hH.indicator hA).lintegral_kernel
    (κ := physicalScenePairKernel)
  convert hread.comp measurable_fst using 1
  ext scene
  exact (lintegral_indicator hA H).symm

/-- The retained and omitted restrictions sum to the exact same original full
traffic, including both original clock endpoints and the original speed. -/
theorem originalSeedRestrictedPathAbsoluteTraffic_add_compl
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    {A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hA : MeasurableSet A)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalSeedRestrictedPathAbsoluteTraffic S w η A scene +
      originalSeedRestrictedPathAbsoluteTraffic S w η Aᶜ scene =
        originalSeedCompletePathAbsoluteTraffic S w η scene :=
  lintegral_add_compl _ hA

/-- Every literal restriction is dominated by the same full original traffic. -/
theorem originalSeedRestrictedPathAbsoluteTraffic_le_full
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalSeedRestrictedPathAbsoluteTraffic S w η A scene ≤
      originalSeedCompletePathAbsoluteTraffic S w η scene :=
  setLIntegral_le_lintegral _ _

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- A short original path which was omitted cannot contribute any absolute
clock traffic to a kernel supported in the deep physical cube. -/
theorem original_omitted_shortPath_clockIntegral_eq_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3 * ell ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηsupport : ∀ y, η y ≠ 0 → y ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell))
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (homitted : (x, m) ∉ originalPathLengthRetained S w R ell)
    (hshort : originalSeedPairPathLength S w m ≤ ell) :
    (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ ∂volume) = 0 := by
  have hzero (c : ℝ) : ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ = 0 := by
    by_cases hc : c ∈ Ico m.1.1 m.1.2
    · have hηzero : η (x + originalSeedPathOffset S w c m) = 0 := by
        by_contra hne
        have hpath : originalSeedCompletePath S w x m c ∈
            haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell) := by
          rw [originalSeedCompletePath_eq_anchor_add_offset]
          exact hηsupport _ hne
        exact homitted (D.originalPathLengthRetained_of_path_mem_deepCube hF hw hell hR ha hb
          (Ico_subset_Icc_self hc) hpath hshort)
      simp only [hηzero, ENNReal.ofReal_zero, zero_mul]
    · rw [originalSeedClockOccupation_eq_indicator_velocity,
        indicator_of_notMem hc]
      simp
  simp only [hzero, lintegral_zero]

/-- In almost every original scene the omitted traffic in any deep-supported
kernel is bounded by literal long-path traffic of the same matching. -/
theorem ae_original_omittedPathTraffic_le_longPathTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3 * ell ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηsupport : ∀ y, η y ≠ 0 → y ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell)) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalSeedRestrictedPathAbsoluteTraffic S w η
          (originalPathLengthRetained S w R ell)ᶜ scene ≤
        originalSeedLongPathAbsoluteTraffic S w η ell scene := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hscene
  rw [originalSeedRestrictedPathAbsoluteTraffic,
    ← lintegral_indicator (measurableSet_originalPathLengthRetained S hF hw R ell).compl,
    originalSeedLongPathAbsoluteTraffic_eq_pairTail]
  apply lintegral_mono_ae
  filter_upwards [hscene] with a ha
  by_cases hret : a ∈ originalPathLengthRetained S w R ell
  · rw [indicator_of_notMem (show a ∉ (originalPathLengthRetained S w R ell)ᶜ from
      fun h ↦ h hret)]
    exact zero_le
  · rw [indicator_of_mem (show a ∈ (originalPathLengthRetained S w R ell)ᶜ from hret)]
    by_cases hlong : ell < originalSeedPairPathLength S w a.2
    · simp only [hlong, ite_true, le_refl]
    · simpa only [hlong, ite_false] using le_of_eq
        (D.original_omitted_shortPath_clockIntegral_eq_zero hF hw hell hR hηsupport
          ha.1 ha.2.1 hret (le_of_not_gt hlong))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
