import OTSelector.Reconstruction.CompletePathTrafficReroot
import OTSelector.Reconstruction.OriginalMinimizerPrefixCurrentCentering

/-! Literal spatial rerooting of the same original vector-valued path current. -/

open Set Function Filter MeasureTheory Manifold
open scoped ENNReal Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Actual pair-kernel rerooting changes only the anchor coordinate in its Bochner integral.
This follows from the original physical reroot's pushforward, with no integrability premise. -/
theorem integral_physicalScenePairKernel_reroot
    {q : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (v : Fin q → ℝ) (scene : LegalMarkedOptimalInputScene q)
    {G : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) → Y}
    (hG : StronglyMeasurable G) :
    (∫ p, G p ∂physicalScenePairKernel (legalMarkedInputSceneReroot q v scene).1) =
      ∫ p, G (p.1 - v, p.2) ∂physicalScenePairKernel scene.1 := by
  change (∫ p, G p ∂physicalScenePairKernel (physicalSceneReroot v scene.1)) = _
  rw [physicalScenePairKernel_reroot]
  exact integral_map_of_stronglyMeasurable
    ((measurable_fst.sub_const v).prodMk measurable_snd) hG

/-- Rerooting the literal vector-valued path-window readout translates its spatial kernel.
The original mark offset and vector occupation remain the same functions of the same mark. -/
theorem legalMarkedPathWindowReadout_reroot
    {q : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    {f : PhysicalPairPalmMark (Fin q) → Y} (hf : StronglyMeasurable f)
    (v : Fin q → ℝ) (scene : LegalMarkedOptimalInputScene q) :
    legalMarkedPathWindowReadout q d η f (legalMarkedInputSceneReroot q v scene) =
      legalMarkedPathWindowReadout q d (fun x ↦ η (x - v)) f scene := by
  have hG : StronglyMeasurable
      (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
        η (p.1 + d p.2) • f p.2) :=
    (hη.comp (measurable_fst.add (hd.comp measurable_snd))).stronglyMeasurable.smul
      (hf.comp_measurable measurable_snd)
  unfold legalMarkedPathWindowReadout
  rw [integral_physicalScenePairKernel_reroot v scene hG]
  apply integral_congr_ae
  filter_upwards with p
  have hx : p.1 - v + d p.2 = p.1 + d p.2 - v := by abel
  rw [hx]

/-- The whole original clock-set current has its literal spatial-translate representation under
the same original reroot, without changing clocks, paired marks, offset or occupation. -/
theorem originalSeedPathClockSetCurrent_reroot
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {F : ContinuousFinslerNorm E M} {u : M → ℝ}
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (Module.finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (A : Set ℝ) (v : Fin (Module.finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (Module.finrank ℝ S.covector.ker)) :
    originalSeedPathClockSetCurrent S w η A
        (legalMarkedInputSceneReroot (Module.finrank ℝ S.covector.ker) v scene) =
      originalSeedPathClockSetCurrent S w (fun x ↦ η (x - v)) A scene := by
  unfold originalSeedPathClockSetCurrent
  apply integral_congr_ae
  filter_upwards with c
  have hc : Measurable
      (fun m : PhysicalPairPalmMark (Fin (Module.finrank ℝ S.covector.ker)) ↦ (m, c)) :=
    measurable_id.prodMk measurable_const
  have hd : Measurable (originalSeedPathOffset S w c) := by
    change Measurable
      ((fun z : PhysicalPairPalmMark (Fin (Module.finrank ℝ S.covector.ker)) × ℝ ↦
        originalSeedPathOffset S w z.2 z.1) ∘ (fun m ↦ (m, c)))
    exact (measurable_originalSeedPathOffset_joint S hF hw).comp hc
  have hf : StronglyMeasurable (originalSeedClockOccupation S w c) := by
    apply Measurable.stronglyMeasurable
    change Measurable
      ((fun z : PhysicalPairPalmMark (Fin (Module.finrank ℝ S.covector.ker)) × ℝ ↦
        originalSeedClockOccupation S w z.2 z.1) ∘ (fun m ↦ (m, c)))
    exact (measurable_originalSeedClockOccupation S hF hw).comp hc
  exact legalMarkedPathWindowReadout_reroot _ hd hη hf v scene

end OTSelector.Reconstruction
