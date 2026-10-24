import OTSelector.Probability.CavitySemidiscreteLocalPlan
import OTSelector.MeasureTheory.SpatialLongEdgeWindow
import OTSelector.Probability.CavitySemidiscreteRootedEnergy
import OTSelector.Probability.CavitySemidiscreteActualScene

/-!
Conditions: A measurable spatial window and an extended nonnegative edge-length threshold.

Objects: The marked product-space long-edge window and its measurability.

Proof detail: Intersect the source spatial preimage with the measurable extended-distance threshold set.

Sources: D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106); D. H. Fremlin, Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33 (https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32).
Relation: A measurable-window definition/adapter; no escape-mass or tail theorem from the original file is covered.
-/

/-!
# Actual rooted long-edge mass from original transport energy

The source-window tail is read from the full original allocation plan. Translating
both endpoints leaves displacement unchanged, so the Haar root estimate controls
escape in the noncompact target coordinate.
-/

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]





/-- The actual rooted plan's escape mass is precisely the original allocation's
translated source-window readout, with the same displacement and total mass. -/
theorem cavitySpatialRootedPlan_longEdgeWindow {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (r : ℝ≥0∞) :
    cavitySpatialRootedPlan μ a Y N z (cavityLongEdgeWindow U r) =
      ENNReal.ofReal N * cavityRootWindowReadout (semidiscreteAllocationMeasure μ a)
        (fun e ↦ e.1.1)
        (fun e ↦ if r ≤ ENNReal.ofReal (‖(Y e.2).1 - e.1.1‖ ^ 2) then 1 else 0) U z := by
  let f : (((ι → ℝ) × A) × Fin (m + 1)) → (((ι → ℝ) × A) × ((ι → ℝ) × B)) :=
    Prod.map (cavitySpatialTranslate z) (fun j ↦ cavitySpatialTranslate z (Y j))
  have hf : Measurable f :=
    (show Measurable (cavitySpatialTranslate z : ((ι → ℝ) × A) → ((ι → ℝ) × A)) from
      measurable_cavitySpatialTranslate.comp
        (measurable_const.prodMk measurable_id)).prodMap (measurable_of_finite _)
  change (ENNReal.ofReal N • (semidiscreteAllocationMeasure μ a).map f) _ = _
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hf (measurableSet_cavityLongEdgeWindow hU r),
    ← lintegral_indicator_one ((measurableSet_cavityLongEdgeWindow hU r).preimage hf)]
  congr 1
  apply lintegral_congr
  rintro ⟨⟨x, s⟩, j⟩
  simp only [Set.indicator_apply, Set.mem_preimage, f, Prod.map_apply,
    cavityLongEdgeWindow, Set.mem_ofPred_eq, cavitySpatialTranslate]
  change (if x - z ∈ U ∧ r ≤ ENNReal.ofReal (‖((Y j).1 - z) - (x - z)‖ ^ 2)
    then 1 else 0) =
      if x - z ∈ U then (if r ≤ ENNReal.ofReal (‖(Y j).1 - x‖ ^ 2) then 1 else 0) else 0
  rw [sub_sub_sub_cancel_right]
  by_cases hs : x - z ∈ U <;> simp only [hs, ite_true, ite_false, true_and, false_and]

/-- Original global squared displacement controls long-edge mass at the actual
uniform root. All source-target allocations and target collisions are allowed. -/
theorem lintegral_cavitySpatialRootedPlan_longEdgeWindow_le {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsFiniteMeasure μ] (p : Fin (m + 1) → ℝ)
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    (∫⁻ z, cavitySpatialRootedPlan μ a Y N z (cavityLongEdgeWindow U r)
      ∂cavityRootMeasure volume D N) ≤
      (volume U * ∫⁻ e, ENNReal.ofReal (‖(Y e.2).1 - e.1.1‖ ^ 2)
        ∂semidiscreteAllocationMeasure μ a) / r := by
  have := ha.isFiniteMeasure_allocationMeasure
  simp_rw [cavitySpatialRootedPlan_longEdgeWindow μ a Y N _ U hU r]
  exact lintegral_cavityRoot_scaled_window_tail_le volume (semidiscreteAllocationMeasure μ a)
    (fun e ↦ e.1.1) measurable_fst.fst
    (fun e ↦ ENNReal.ofReal (‖(Y e.2).1 - e.1.1‖ ^ 2))
    ((((measurable_of_finite Y).comp measurable_snd).fst.sub measurable_fst.fst).norm.pow_const 2).ennreal_ofReal
    U hU D N hN r hr0 hrt

end OTSelector.Probability
