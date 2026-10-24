import OTSelector.Reconstruction.OriginalPathLengthRetention
import OTSelector.Reconstruction.OriginalOrientedCubeReflectedKernel

/-! True original-path retention in the same chosen physical orientation. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A fixed coordinate distortion of the chosen physical frame, bounded below by one.
It only enlarges the geometric collar; the actual original path-length cutoff is unchanged. -/
def originalStageFrameCollarFactor {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) : ℝ :=
  max 1 ‖(orthonormalPhysicalCubeMap b).symm.toContinuousLinearMap‖

theorem one_le_originalStageFrameCollarFactor {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    1 ≤ originalStageFrameCollarFactor b := le_max_left _ _

/-- The literal inverse frame map obeys its genuine coordinate operator norm. -/
theorem norm_inverse_originalStageFrame_le {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (v : Fin q → ℝ) :
    ‖(orthonormalPhysicalCubeMap b).symm v‖ ≤ originalStageFrameCollarFactor b * ‖v‖ := by
  exact ((orthonormalPhysicalCubeMap b).symm.toContinuousLinearMap.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual original retained set in the chosen physical cube. The source is in the
smaller oriented cube and the unchanged full original path length is at most ell. -/
def originalOrientedPathLengthRetained (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) :
    Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :=
  {a | (orthonormalPhysicalCubeMap b).symm a.1 ∈
      haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * (originalStageFrameCollarFactor b * ell)) ∧
    originalSeedPairPathLength S w a.2 ≤ ell}

/-- This is a Borel restriction of the very same original matching kernel. -/
theorem measurableSet_originalOrientedPathLengthRetained
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker}
    (hw : w ∈ S.labels) (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) :
    MeasurableSet (originalOrientedPathLengthRetained S w b R ell) :=
  (measurableSet_Icc.preimage ((orthonormalPhysicalCubeMap b).symm.continuous.measurable.comp measurable_fst)).inter
    (measurableSet_le ((measurable_originalSeedPairPathLength S hF hw).comp measurable_snd) measurable_const)

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual original full path, viewed in the chosen frame, stays within a fixed frame
factor times its same genuine full path length of the unchanged original source. -/
theorem norm_frame_originalSeedCompletePath_sub_source_le_pathLength
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c : ℝ} (hc : c ∈ Icc m.1.1 m.1.2) :
    ‖(orthonormalPhysicalCubeMap b).symm (originalSeedCompletePath S w x m c) -
      (orthonormalPhysicalCubeMap b).symm x‖ ≤
        originalStageFrameCollarFactor b * originalSeedPairPathLength S w m := by
  rw [← map_sub]
  exact (norm_inverse_originalStageFrame_le b _).trans
    (mul_le_mul_of_nonneg_left (D.norm_originalSeedCompletePath_sub_source_le_pathLength
      hF hw x m ha hb hc) (by linarith [one_le_originalStageFrameCollarFactor b]))

/-- Every retained original path remains in the actual inner physical cube with exactly
this chosen orientation, without rotating the original scene or changing its clocks. -/
theorem originalOrientedPathLengthRetained_path_mem_innerCube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (hret : (x, m) ∈ originalOrientedPathLengthRetained S w b R ell)
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c : ℝ} (hc : c ∈ Icc m.1.1 m.1.2) :
    originalSeedCompletePath S w x m c ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - originalStageFrameCollarFactor b * ell)) := by
  have hC : 0 ≤ originalStageFrameCollarFactor b := by linarith [one_le_originalStageFrameCollarFactor b]
  have hcollar := mul_nonneg hC hell
  have hx : ‖(orthonormalPhysicalCubeMap b).symm x‖ ≤ R - 2 * (originalStageFrameCollarFactor b * ell) :=
    (mem_haarRootCube_iff_norm_le (by linarith) _).mp hret.1
  have hp := (D.norm_frame_originalSeedCompletePath_sub_source_le_pathLength hF hw b x m ha hb hc).trans
    (mul_le_mul_of_nonneg_left hret.2 hC)
  rw [mem_originalCenteredPhysicalCubeRegion_iff]
  have hrad : 2 * (R - originalStageFrameCollarFactor b * ell) / 2 =
      R - originalStageFrameCollarFactor b * ell := by ring
  rw [hrad]
  apply (mem_haarRootCube_iff_norm_le (by linarith) _).mpr
  have htri := norm_le_norm_sub_add
    ((orthonormalPhysicalCubeMap b).symm (originalSeedCompletePath S w x m c))
    ((orthonormalPhysicalCubeMap b).symm x)
  linarith

/-- The unchanged target endpoint lies in the same oriented inner cube. -/
theorem originalOrientedPathLengthRetained_target_mem_innerCube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (hret : (x, m) ∈ originalOrientedPathLengthRetained S w b R ell)
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2) :
    x + m.2 ∈ originalCenteredPhysicalCubeRegion b (2 * (R - originalStageFrameCollarFactor b * ell)) := by
  simpa only [D.originalSeedCompletePath_target hF hw x m ha hb hab] using
    D.originalOrientedPathLengthRetained_path_mem_innerCube hF hw b hell hR hret ha hb
      (right_mem_Icc.mpr hab.le)

/-- A short actual original path meeting the deeper cube belongs to this same retained set. -/
theorem originalOrientedPathLengthRetained_of_path_mem_deepCube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3 * (originalStageFrameCollarFactor b * ell) ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c : ℝ} (hc : c ∈ Icc m.1.1 m.1.2)
    (hpath : originalSeedCompletePath S w x m c ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - 3 * (originalStageFrameCollarFactor b * ell))))
    (hlength : originalSeedPairPathLength S w m ≤ ell) :
    (x, m) ∈ originalOrientedPathLengthRetained S w b R ell := by
  refine ⟨?_, hlength⟩
  have hC : 0 ≤ originalStageFrameCollarFactor b := by linarith [one_le_originalStageFrameCollarFactor b]
  have hcollar := mul_nonneg hC hell
  have hp : ‖(orthonormalPhysicalCubeMap b).symm (originalSeedCompletePath S w x m c)‖ ≤
      R - 3 * (originalStageFrameCollarFactor b * ell) := by
    rw [mem_originalCenteredPhysicalCubeRegion_iff] at hpath
    have hrad : 2 * (R - 3 * (originalStageFrameCollarFactor b * ell)) / 2 =
      R - 3 * (originalStageFrameCollarFactor b * ell) := by ring
    rw [hrad] at hpath
    exact (mem_haarRootCube_iff_norm_le (by linarith) _).mp hpath
  have hd := (D.norm_frame_originalSeedCompletePath_sub_source_le_pathLength hF hw b x m ha hb hc).trans
    (mul_le_mul_of_nonneg_left hlength hC)
  apply (mem_haarRootCube_iff_norm_le (by linarith) _).mpr
  have htri := norm_le_norm_sub_add ((orthonormalPhysicalCubeMap b).symm x)
    ((orthonormalPhysicalCubeMap b).symm (originalSeedCompletePath S w x m c))
  rw [norm_sub_rev] at htri
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
