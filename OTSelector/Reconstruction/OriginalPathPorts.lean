import OTSelector.Reconstruction.OriginalPathLengthRetention

/-! # Actual original source and target ports left by full-path retention -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- An original source inside the full cube whose unchanged edge was not retained. -/
def originalPathSourcePorts (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :=
  {a | a.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R ∧
    a ∉ originalPathLengthRetained S w R ell}

/-- The same actual edge contributes a target port when its original target is
inside the full cube and it was not retained. -/
def originalPathTargetPorts (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell : ℝ) : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :=
  {a | a.1 + a.2.2 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R ∧
    a ∉ originalPathLengthRetained S w R ell}

theorem measurableSet_originalPathSourcePorts
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ) :
    MeasurableSet (originalPathSourcePorts S w R ell) :=
  (measurableSet_Icc.preimage measurable_fst).inter
    (measurableSet_originalPathLengthRetained S hF hw R ell).compl

theorem measurableSet_originalPathTargetPorts
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ) :
    MeasurableSet (originalPathTargetPorts S w R ell) :=
  (measurableSet_Icc.preimage (measurable_fst.add measurable_snd.snd)).inter
    (measurableSet_originalPathLengthRetained S hF hw R ell).compl

/-- Every original source port is either in the original boundary collar or has
actual full path length larger than the collar. -/
theorem originalPathSourcePorts_subset_boundary_or_long
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (R ell : ℝ) :
    originalPathSourcePorts S w R ell ⊆
      {a | a.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R \
        haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell)} ∪
      {a | a.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R ∧
        ell < originalSeedPairPathLength S w a.2} := by
  intro a ha
  by_cases hx : a.1 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 2 * ell)
  · right
    refine ⟨ha.1, lt_of_not_ge ?_⟩
    intro hlength
    exact ha.2 ⟨hx, hlength⟩
  · exact Or.inl ⟨ha.1, hx⟩

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every actual legal target port is in the target boundary collar or has long
original path length. The same retained set is used for both original colors. -/
theorem originalPathTargetPort_mem_boundary_or_long
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 3 * ell ≤ R)
    {x : Fin (finrank ℝ S.covector.ker) → ℝ}
    {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2)
    (hport : (x, m) ∈ originalPathTargetPorts S w R ell) :
    x + m.2 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R \
        haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell) ∨
      (x + m.2 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R ∧
        ell < originalSeedPairPathLength S w m) := by
  by_cases hx : x + m.2 ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell)
  · right
    refine ⟨hport.1, lt_of_not_ge ?_⟩
    intro hlength
    have hpath : originalSeedCompletePath S w x m m.1.2 ∈
        haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 3 * ell) := by
      simpa only [D.originalSeedCompletePath_target hF hw x m ha hb hab] using hx
    exact hport.2 (D.originalPathLengthRetained_of_path_mem_deepCube hF hw hell hR ha hb
      (right_mem_Icc.mpr hab.le) hpath hlength)
  · exact Or.inl ⟨hport.1, hx⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
