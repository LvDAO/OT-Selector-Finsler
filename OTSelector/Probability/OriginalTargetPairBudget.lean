import OTSelector.Probability.OriginalTargetConfigurationTightness
import OTSelector.PointProcess.LocalConfigurationPairWitness
import Mathlib.Probability.Independence.Basic

/-!
# Original iid spatial pair budgets

The normalized original spatial marginal bounds close pairs by the volume of a
small spatial ball. Marks may depend arbitrarily on position. Integrating the
original independent root does not change the bound.
-/

open MeasureTheory ProbabilityTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal

noncomputable section
namespace OTSelector.Probability

/-- Distinct coordinates of the original iid array have their original product law. -/
theorem measurePreserving_iid_distinct_pair
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν] {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (fun y : Fin n → X ↦ (y i, y j))
      (Measure.pi (fun _ : Fin n ↦ ν)) (ν.prod ν) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have hind : iIndepFun (fun k (y : Fin n → X) ↦ y k)
      (Measure.pi (fun _ : Fin n ↦ ν)) := iIndepFun_pi (fun _ ↦ aemeasurable_id)
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable]
  rw [(measurePreserving_eval (fun _ : Fin n ↦ ν) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n ↦ ν) j).map_eq]

variable {ι B : Type*} [Fintype ι] [MeasurableSpace B]

/-- The normalized original spatial marginal dominates every translated window. -/
theorem original_marked_translated_mass_le
    (ν : Measure ((ι → ℝ) × B)) (D : Set (ι → ℝ)) {a : ℝ≥0∞}
    (hν : ν.map Prod.fst = a • volume.restrict D)
    {W : Set (ι → ℝ)} (hW : MeasurableSet W) (z : ι → ℝ) :
    ν {y | y.1 - z ∈ W} ≤ a * volume W := by
  have hA : MeasurableSet {y : ι → ℝ | y - z ∈ W} :=
    (measurable_id.sub measurable_const) hW
  change ν (Prod.fst ⁻¹' {y : ι → ℝ | y - z ∈ W}) ≤ _
  rw [← Measure.map_apply measurable_fst hA, hν, Measure.smul_apply,
    smul_eq_mul]
  have ht : volume {y : ι → ℝ | y - z ∈ W} = volume W := by
    calc
      _ = volume ((fun y ↦ y + -z) ⁻¹' W) := by
        simp only [sub_eq_add_neg]
        rfl
      _ = volume W := measure_preimage_add_right volume (-z) W
  exact (mul_le_mul_right (Measure.restrict_le_self _) a).trans_eq (by rw [ht])

/-- One original independent target pair has the exact scale of the small-ball
budget, with no regularity assumption on its conditional marks. -/
theorem original_marked_pair_mass_le
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (D : Set (ι → ℝ)) {a : ℝ≥0∞}
    (hν : ν.map Prod.fst = a • volume.restrict D)
    {W : Set (ι → ℝ)} (hW : MeasurableSet W) (z : ι → ℝ) (e : ℝ) :
    (ν.prod ν) {p | p.1.1 - z ∈ W ∧ dist p.1.1 p.2.1 < e} ≤
      a * a * (volume W * volume (Metric.ball (0 : ι → ℝ) e)) := by
  let A : Set ((ι → ℝ) × B) := {x | x.1 - z ∈ W}
  have hA : MeasurableSet A := (measurable_fst.sub measurable_const) hW
  have hs : MeasurableSet {p : ((ι → ℝ) × B) × ((ι → ℝ) × B) |
      p.1.1 - z ∈ W ∧ dist p.1.1 p.2.1 < e} :=
    ((measurable_fst.fst.sub measurable_const) hW).inter
      (measurableSet_lt (measurable_fst.fst.dist measurable_snd.fst) measurable_const)
  have hb (x : (ι → ℝ) × B) :
      ν {y | dist x.1 y.1 < e} ≤ a * volume (Metric.ball (0 : ι → ℝ) e) := by
    convert original_marked_translated_mass_le ν D hν
      (W := Metric.ball (0 : ι → ℝ) e) Metric.isOpen_ball.measurableSet x.1 using 1
    congr 1
    ext y
    simp only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ x, A.indicator
        (fun _ ↦ a * volume (Metric.ball (0 : ι → ℝ) e)) x ∂ν := by
      apply lintegral_mono
      intro x
      change ν {y | x.1 - z ∈ W ∧ dist x.1 y.1 < e} ≤ _
      by_cases hx : x ∈ A
      · simpa only [show x.1 - z ∈ W from hx, true_and, indicator_of_mem hx] using hb x
      · have hx' : x.1 - z ∉ W := hx
        simp only [hx', false_and, ofPred_false, measure_empty,
          indicator_of_notMem hx, le_refl]
    _ = (a * volume (Metric.ball (0 : ι → ℝ) e)) * ν A := by
      rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ (a * volume (Metric.ball (0 : ι → ℝ) e)) * (a * volume W) :=
      mul_le_mul_right (original_marked_translated_mass_le ν D hν hW z) _
    _ = _ := by ring

end OTSelector.Probability
