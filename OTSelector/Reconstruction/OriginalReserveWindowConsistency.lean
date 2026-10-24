import OTSelector.Reconstruction.OriginalReserveWindowPrefixMeasures

/-! Exact Poisson window consistency on the same original physical point measures. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The original two-color window point measure is a measurable readout. -/
theorem measurable_originalInputTwoBlockMeasure (q : ℕ) :
    Measurable (legalInputTwoBlockMeasure q) :=
  measurable_localFiniteMeasure_coe.comp (measurable_legalInputTwoBlockLocal q)

/-- A fixed spatial window restriction is measurable on the same finite arrays. -/
theorem measurable_originalInputTwoBlockSpatialRestriction (q : ℕ)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) :
    Measurable (fun b ↦ (legalInputTwoBlockMeasure q b).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' U)) := by
  have h : Measurable (fun b ↦ legalInputRestrictionLocal
      ((Prod.fst ∘ Prod.fst) ⁻¹' U) (legalInputTwoBlockLocal q b)) :=
    (measurable_legalInputRestrictionLocal
      (hU.preimage (measurable_fst.comp measurable_fst))).comp
        (measurable_legalInputTwoBlockLocal q)
  exact measurable_localFiniteMeasure_coe.comp h

/-- A containing Poisson window restricted to the actual smaller physical
window has exactly its physical-volume Poisson law, including both original marks. -/
theorem map_originalPoissonWindow_spatial_restriction
    (q : ℕ) {S : ℝ} (hS : 0 < S)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ haarRootCube (Fin q) S) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
      (fun b ↦ (legalInputTwoBlockMeasure q b).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' U)) =
      (legalInputPoissonWindowLaw q U α β).map (legalInputTwoBlockMeasure q) := by
  let L := 4 * (S + 1)
  have hmargin : S + 1 < L / 2 := by dsimp [L]; linarith
  have hz : (0 : Fin q → ℝ) ∈ haarRootCube (Fin q) (L / 2 - S - 1) := by
    constructor <;> intro i <;> dsimp <;> linarith
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) q)).ne'
  have hW := map_legalInputRootWindows_eq_of_inner_root q hS.le hmargin
    measurableSet_Icc (Subset.refl _) hvol α β hz
  change (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).map
    (fun ω ↦ legalInputRootWindows q (Real.toNNReal L) (haarRootCube (Fin q) S) (0, ω)) =
      legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β at hW
  have hUlaw := map_legalInputRootWindows_eq_of_inner_root q hS.le hmargin
    hU hsub hpos α β hz
  have hWmap : Measurable (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦
      legalInputRootWindows q (Real.toNNReal L) (haarRootCube (Fin q) S) (0, ω)) :=
    (measurable_legalInputRootWindows q (Real.toNNReal L) measurableSet_Icc).comp
      measurable_prodMk_left
  have hUmap : Measurable (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦
      legalInputRootWindows q (Real.toNNReal L) U (0, ω)) :=
    (measurable_legalInputRootWindows q (Real.toNNReal L) hU).comp
      measurable_prodMk_left
  rw [← hW, Measure.map_map (measurable_originalInputTwoBlockSpatialRestriction q hU) hWmap,
    ← hUlaw, Measure.map_map (measurable_originalInputTwoBlockMeasure q) hUmap]
  apply Measure.map_congr
  exact .of_forall fun ω ↦ originalInputRootWindows_nested_measure q (Real.toNNReal L)
    hU measurableSet_Icc hsub 0 ω

end OTSelector.Reconstruction
