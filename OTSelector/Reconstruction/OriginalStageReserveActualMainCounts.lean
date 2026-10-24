import OTSelector.Reconstruction.OriginalStageResidualDensityExcessEndpoints
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowColors
import Mathlib.MeasureTheory.Function.Floor

/-! Actual full-scene cube counts, their measurability and their original-array identity. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Read the literal original colored input count in the same physical cube. Natural floor
makes a total measurable readout; actual integer scene arrays prove it equals the exact count. -/
def originalStageMainWindowCount {q : ℕ} (R : ℝ) (c : Fin 2)
    (scene : LegalMarkedOptimalInputScene q) : ℕ :=
  ⌊(scene.2 : Measure (LegalColoredInputPoint q)).real
    ((haarRootCube (Fin q) R ×ˢ (univ : Set ℝ)) ×ˢ {c})⌋₊

/-- The count is observed from the actual original scene, so it can enter the auxiliary
mark/count law without an unmeasurable selection of an array representation. -/
theorem measurable_originalStageMainWindowCount {q : ℕ} (R : ℝ) (c : Fin 2) :
    Measurable (originalStageMainWindowCount (q := q) R c) := by
  let U : Set (LegalColoredInputPoint q) := (haarRootCube (Fin q) R ×ˢ univ) ×ˢ {c}
  have hU : MeasurableSet U := (measurableSet_Icc.prod MeasurableSet.univ).prod (measurableSet_singleton c)
  have hm : Measurable (fun scene : LegalMarkedOptimalInputScene q ↦
      (scene.2 : Measure (LegalColoredInputPoint q)) U) :=
    (Measure.measurable_coe hU).comp (measurable_localFiniteMeasure_coe.comp measurable_snd)
  exact hm.ennreal_toReal.nat_floor

/-- Under an internally produced original-array representation, the measurable count is
exactly its unchanged array length on each original color. -/
theorem IsOriginalStageMainWindowArrays.mainWindowCounts {q : ℕ} {R : ℝ}
    {scene : LegalMarkedOptimalInputScene q} {sourceMain targetMain : MarkedCloudSpace q ℝ}
    (h : IsOriginalStageMainWindowArrays R scene sourceMain targetMain) :
    originalStageMainWindowCount R 0 scene = sourceMain.1 ∧
    originalStageMainWindowCount R 1 scene = targetMain.1 := by
  have hs := h.actual_counts.1
  have ht := h.actual_counts.2
  have hW : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} :=
    measurableSet_Icc.preimage measurable_fst
  have hcolor (c : Fin 2) :
      (scene.2 : Measure (LegalColoredInputPoint q)).real ((haarRootCube (Fin q) R ×ˢ univ) ×ˢ {c}) =
      (legalInputColorMeasure q scene.2 c).real {p | p.1 ∈ haarRootCube (Fin q) R} := by
    rw [measureReal_def, measureReal_def, legalInputColorMeasure_apply_prod q _ c hW]
    have heq : (haarRootCube (Fin q) R ×ˢ (univ : Set ℝ)) =
        {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} := by ext p; simp
    rw [heq]
  simp only [originalStageMainWindowCount, hcolor, hs, ht, Nat.floor_natCast, and_self]

/-- The measurable actual two-color full excess agrees with the actual original-array excess. -/
theorem OriginalStageExcessRemovalData.sourceExcess_eq_actualSceneCounts
    {q : ℕ} (A : OriginalStageExcessRemovalData q) {R : ℝ} {scene : LegalMarkedOptimalInputScene q}
    (h : IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain) :
    A.sourceExcess =
      (originalStageMainWindowCount R 0 scene + A.sourceReserve.1) -
        (originalStageMainWindowCount R 1 scene + A.targetReserve.1) ∧
    A.targetExcess =
      (originalStageMainWindowCount R 1 scene + A.targetReserve.1) -
        (originalStageMainWindowCount R 0 scene + A.sourceReserve.1) := by
  rw [h.mainWindowCounts.1, h.mainWindowCounts.2]
  exact ⟨rfl, rfl⟩

end OTSelector.Reconstruction
