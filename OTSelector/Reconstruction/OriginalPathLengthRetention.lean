import OTSelector.Reconstruction.OriginalFullPathRadius
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary

/-!
# A measurable retained core of the unchanged original complete paths

Retain a genuine edge when its source lies in the smaller cube and its full
original path length is at most the collar. Every retained path lies in the
inner cube. Deep-interior omitted contributors must have long original paths.
-/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

/-- The actual Haar cube is the closed coordinate-norm ball of the same radius. -/
theorem mem_haarRootCube_iff_norm_le {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 ≤ R)
    (x : ι → ℝ) : x ∈ haarRootCube ι R ↔ ‖x‖ ≤ R := by
  constructor
  · intro hx
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    exact abs_le.mpr ⟨hx.1 i, hx.2 i⟩
  · intro hx
    constructor <;> intro i
    · exact (abs_le.mp ((norm_le_pi_norm x i).trans hx)).1
    · exact (abs_le.mp ((norm_le_pi_norm x i).trans hx)).2

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The literal source-anchor/paired-mark retained set, defined before looking at
any reserve or repair and without changing any original edge. -/
def originalPathLengthRetained (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :=
  {a | a.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell) ∧ originalSeedPairPathLength S w a.2 ≤ ell}

/-- The retained core is a Borel restriction of the actual original matching kernel. -/
theorem measurableSet_originalPathLengthRetained
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ) :
    MeasurableSet (originalPathLengthRetained S w R ell) :=
  ((measurableSet_Icc).preimage measurable_fst).inter
    (measurableSet_le ((measurable_originalSeedPairPathLength S hF hw).comp measurable_snd)
      measurable_const)

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every retained actual path, at all its original clocks, stays in the inner cube. -/
theorem originalPathLengthRetained_path_mem_innerCube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (hretained : (x, m) ∈ originalPathLengthRetained S w R ell)
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c : ℝ} (hc : c ∈ Icc m.1.1 m.1.2) :
    originalSeedCompletePath S w x m c ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) := by
  have hx : ‖x‖ ≤ R - 2 * ell :=
    (mem_haarRootCube_iff_norm_le (by linarith) x).mp hretained.1
  have hpath := (D.norm_originalSeedCompletePath_sub_source_le_pathLength hF hw x m ha hb hc).trans
    hretained.2
  apply (mem_haarRootCube_iff_norm_le (by linarith) _).mpr
  have hn := norm_le_norm_sub_add (originalSeedCompletePath S w x m c) x
  linarith

/-- The target of each retained actual legal edge lies in that same inner cube. -/
theorem originalPathLengthRetained_target_mem_innerCube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (hretained : (x, m) ∈ originalPathLengthRetained S w R ell)
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2) :
    x + m.2 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) := by
  simpa only [D.originalSeedCompletePath_target hF hw x m ha hb hab] using
    D.originalPathLengthRetained_path_mem_innerCube hF hw hell hR hretained ha hb
      (right_mem_Icc.mpr hab.le)

/-- A short actual path meeting the deeper cube is necessarily in the retained core. -/
theorem originalPathLengthRetained_of_path_mem_deepCube
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3 * ell ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c : ℝ} (hc : c ∈ Icc m.1.1 m.1.2)
    (hpath : originalSeedCompletePath S w x m c ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell))
    (hlength : originalSeedPairPathLength S w m ≤ ell) :
    (x, m) ∈ originalPathLengthRetained S w R ell := by
  refine ⟨?_, hlength⟩
  have hp : ‖originalSeedCompletePath S w x m c‖ ≤ R - 3 * ell :=
    (mem_haarRootCube_iff_norm_le (by linarith) _).mp hpath
  have hd := (D.norm_originalSeedCompletePath_sub_source_le_pathLength hF hw x m ha hb hc).trans hlength
  apply (mem_haarRootCube_iff_norm_le (by linarith) _).mpr
  have hn := norm_le_norm_sub_add x (originalSeedCompletePath S w x m c)
  rw [norm_sub_rev] at hn
  linarith

/-- Every omitted deep-interior contributor has actual full path length above the collar. -/
theorem original_unretained_deep_path_has_long_length
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3 * ell ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c : ℝ} (hc : c ∈ Icc m.1.1 m.1.2)
    (hpath : originalSeedCompletePath S w x m c ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell))
    (homitted : (x, m) ∉ originalPathLengthRetained S w R ell) :
    ell < originalSeedPairPathLength S w m := by
  by_contra h
  exact homitted (D.originalPathLengthRetained_of_path_mem_deepCube hF hw hell hR ha hb hc hpath
    (le_of_not_gt h))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
