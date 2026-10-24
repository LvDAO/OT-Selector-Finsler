import OTSelector.Reconstruction.SpatialPathTrafficMeasurability
import OTSelector.Reconstruction.OriginalRetainedPathTraffic

/-! # Spatial second moments and actual omitted original traffic -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false

/-- A compact smoothing kernel observed inside a smaller physical cube remains
supported in the prescribed deeper cube. Radii use the actual Haar convention. -/
theorem translated_kernel_support_in_haarRootCube
    {ι : Type*} [Fintype ι] {η : (ι → ℝ) → ℝ} {R radius : ℝ}
    (hradius : 0 ≤ radius) (hR : radius ≤ R)
    (hηsupport : ∀ x, radius < ‖x‖ → η x = 0)
    {z : ι → ℝ} (hz : z ∈ haarRootCube ι (R - radius)) :
    ∀ y, η (y - z) ≠ 0 → y ∈ haarRootCube ι R := by
  intro y hy
  have hyz : ‖y - z‖ ≤ radius := by
    by_contra h
    exact hy (hηsupport _ (lt_of_not_ge h))
  have hzN := (mem_haarRootCube_iff_norm_le (sub_nonneg.mpr hR) z).mp hz
  apply (mem_haarRootCube_iff_norm_le (hradius.trans hR) y).mpr
  have hn := norm_le_norm_sub_add y z
  linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Literal restricted original absolute traffic is jointly Borel in its
physical observation point and its unchanged original scene. -/
theorem measurable_original_restrictedPathTraffic_shift_joint
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {A : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))} (hA : MeasurableSet A) :
    Measurable (fun p : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
      originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x - p.1)) A p.2) :=
  measurable_restricted_pairClockTraffic_shift_joint _
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal hA

/-- The same actual original complete traffic has the same second moment at
every physical observation point. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_original_fullTraffic_sq_shift
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w (fun x ↦ η (x - z)) scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
    ∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
  Q.lintegral_completePathTraffic_shift _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal
    (measurable_id.pow_const 2) z

/-- Long-path traffic keeps the identical spatial second moment under the
same original stationary law and original path-length threshold. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_original_longPathTraffic_sq_shift
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (R : ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w (fun x ↦ η (x - z)) R scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
    ∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η R scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) :=
  Q.lintegral_completePathTraffic_shift _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal
    (Measurable.ite (measurableSet_lt measurable_const
      ((measurable_originalSeedPairPathLength S hF hw).comp measurable_fst))
      (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal measurable_const)
    (measurable_id.pow_const 2) z

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- In every deep physical observation window, the actual omitted traffic
second moment is bounded by its original stationary long-path second moment. -/
theorem lintegral_original_deepOmittedTraffic_sq_le_longPath_sq
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {R ell radius : ℝ} (hell : 0 ≤ ell) (hradius : 0 ≤ radius)
    (hR : 3 * ell + radius ≤ R) (hηsupport : ∀ x, radius < ‖x‖ → η x = 0)
    {z : Fin (finrank ℝ S.covector.ker) → ℝ}
    (hz : z ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell - radius)) :
    (∫⁻ scene, originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x - z))
        (originalPathLengthRetained S w R ell)ᶜ scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
    ∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η ell scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
  have hsupport : ∀ y, η (y - z) ≠ 0 → y ∈
      haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell) :=
    translated_kernel_support_in_haarRootCube hradius (by linarith) hηsupport hz
  calc
    _ ≤ ∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w (fun x ↦ η (x - z)) ell scene ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_original_omittedPathTraffic_le_longPathTraffic hF hw Q hell
        (by linarith) hsupport] with scene hscene
      exact pow_le_pow_left' hscene 2
    _ = _ := Q.lintegral_original_longPathTraffic_sq_shift hF hw hη ell z

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
