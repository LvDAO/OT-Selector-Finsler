import OTSelector.Reconstruction.FinslerOriginalCompletePath

/-! # Joint measurability of the actual original complete path and its offset -/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual complete path is Borel jointly in the physical source anchor, original paired
clocks, full displacement, and physical observation clock. -/
theorem measurable_originalSeedCompletePath (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (fun z : ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) × ℝ ↦
      originalSeedCompletePath S w z.1.1 z.1.2 z.2) := by
  have hA := S.measurable_familyLabelCompliance hF (Module.finBasis ℝ S.covector.ker)
    (w := fun _ : ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) × ℝ ↦ (⟨w, hw⟩ : S.labels))
    measurable_const (measurable_fst.snd.fst.fst.sub_const (S.level : ℝ))
    (measurable_snd.sub_const (S.level : ℝ))
  have hp : Measurable (fun z : ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) × ℝ ↦
      originalSeedPairMomentum S w z.1.2) :=
    (measurable_originalSeedPairMomentum S hF hw).comp measurable_fst.snd
  have hmul : Continuous (fun z :
      Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ z.1 *ᵥ z.2) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact measurable_fst.fst.add (hmul.measurable.comp (hA.prodMk hp))

/-- The displacement from the unchanged source anchor to its actual path position at clock c. -/
def originalSeedPathOffset (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (c : ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
    Fin (finrank ℝ S.covector.ker) → ℝ := originalSeedCompletePath S w 0 m c

theorem measurable_originalSeedPathOffset (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) (c : ℝ) :
    Measurable (originalSeedPathOffset S w c) :=
  (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

/-- A spatial translation of the source translates the entire original path by the same amount. -/
theorem originalSeedCompletePath_eq_anchor_add_offset (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) (c : ℝ) :
    originalSeedCompletePath S w x m c = x + originalSeedPathOffset S w c m := by
  simp [originalSeedPathOffset, originalSeedCompletePath]

end OTSelector.Reconstruction
