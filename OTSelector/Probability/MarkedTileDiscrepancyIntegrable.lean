import OTSelector.Probability.MarkedTileDiscrepancy
import OTSelector.Probability.MarkedTileRepair

/-!
# The total tile-label discrepancy

This module defines the total label-count discrepancy of a two-colour marked
cloud and proves its measurability, integrability and the bound by the total
number of points.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {C A B : Type*} [Fintype C] [DecidableEq C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace A] [MeasurableSpace B]

/-- The total label discrepancy of a two-colour marked cloud. -/
def tileLabelDiscrepancy (ω : TwoMarkedCloudSpace q (C × A) (C × B)) : ℝ :=
  ∑ c : C,
    |((sourceLabelCount (q := q) c ω.1 : ℕ) : ℝ) -
      ((targetLabelCount (q := q) c ω.2 : ℕ) : ℝ)|

/-- The label counts partition the source cloud: their sum is the total count. -/
theorem sum_sourceLabelCount {q : ℕ} {C A : Type*} [Fintype C] [DecidableEq C]
    (z : MarkedCloudSpace q (C × A)) :
    (∑ c : C, sourceLabelCount (q := q) c z) = z.1 := by
  classical
  have h := @Finset.card_eq_sum_card_fiberwise (Fin z.1) C _ (fun i => (z.2 i).2.1)
    Finset.univ Finset.univ (fun i _ => Finset.mem_univ _)
  simpa only [sourceLabelCount, Finset.card_univ, Fintype.card_fin] using h.symm

/-- The label counts partition the target cloud: their sum is the total count. -/
theorem sum_targetLabelCount {q : ℕ} {C B : Type*} [Fintype C] [DecidableEq C]
    (z : MarkedCloudSpace q (C × B)) :
    (∑ c : C, targetLabelCount (q := q) c z) = z.1 := by
  classical
  have h := @Finset.card_eq_sum_card_fiberwise (Fin z.1) C _ (fun i => (z.2 i).2.1)
    Finset.univ Finset.univ (fun i _ => Finset.mem_univ _)
  simpa only [targetLabelCount, Finset.card_univ, Fintype.card_fin] using h.symm

/-- The total discrepancy is bounded by the total number of points. -/
theorem abs_tileLabelDiscrepancy_le (ω : TwoMarkedCloudSpace q (C × A) (C × B)) :
    |tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B) ω| ≤
      ((mSourceCount ω : ℕ) : ℝ) + ((mTargetCount ω : ℕ) : ℝ) := by
  classical
  unfold tileLabelDiscrepancy
  rw [abs_of_nonneg (Finset.sum_nonneg fun c _ => abs_nonneg _)]
  have hb : ∀ c : C,
      |((sourceLabelCount (q := q) c ω.1 : ℕ) : ℝ) -
        ((targetLabelCount (q := q) c ω.2 : ℕ) : ℝ)| ≤
      ((sourceLabelCount (q := q) c ω.1 : ℕ) : ℝ) +
        ((targetLabelCount (q := q) c ω.2 : ℕ) : ℝ) := by
    intro c
    exact abs_sub_le_iff.mpr
      ⟨by linarith [abs_nonneg ((targetLabelCount (q := q) c ω.2 : ℕ) : ℝ)],
       by linarith [abs_nonneg ((sourceLabelCount (q := q) c ω.1 : ℕ) : ℝ)]⟩
  calc (∑ c : C,
        |((sourceLabelCount (q := q) c ω.1 : ℕ) : ℝ) -
          ((targetLabelCount (q := q) c ω.2 : ℕ) : ℝ)|)
      ≤ ∑ c : C,
          (((sourceLabelCount (q := q) c ω.1 : ℕ) : ℝ) +
            ((targetLabelCount (q := q) c ω.2 : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun c _ => hb c
    _ = ((mSourceCount ω : ℕ) : ℝ) + ((mTargetCount ω : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum,
          sum_sourceLabelCount, sum_targetLabelCount]
        rfl

/-- Measurability of the total label discrepancy. -/
theorem measurable_tileLabelDiscrepancy :
    Measurable (tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B)) := by
  classical
  unfold tileLabelDiscrepancy
  refine Finset.measurable_sum _ fun c _ => ?_
  have hfst : Measurable (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) => ω.1) :=
    measurable_fst
  have hsnd : Measurable (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) => ω.2) :=
    measurable_snd
  have hsrc : Measurable (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
      (sourceLabelCount (q := q) c ω.1 : ℕ)) := by
    have h := (measurable_markLabelCount (q := q) (C := C) (A := A) c).comp hfst
    exact h
  have htgt : Measurable (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
      (targetLabelCount (q := q) c ω.2 : ℕ)) := by
    have h := (measurable_markLabelCount (q := q) (C := C) (A := B) c).comp hsnd
    exact h
  exact continuous_abs.measurable.comp (((measurable_from_nat (α := ℝ)).comp hsrc).sub
    ((measurable_from_nat (α := ℝ)).comp htgt))

/-- Integrability of the total label discrepancy under the two-colour marked
Poisson law. -/
theorem integrable_tileLabelDiscrepancy
    (α : Measure (C × A)) [IsProbabilityMeasure α]
    (β : Measure (C × B)) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B))
      (twoMarkedCloudLaw q (C × A) (C × B) α β r) := by
  have hbdd : Integrable
      (fun ω : TwoMarkedCloudSpace q (C × A) (C × B) =>
        ((mSourceCount ω : ℕ) : ℝ) + ((mTargetCount ω : ℕ) : ℝ))
      (twoMarkedCloudLaw q (C × A) (C × B) α β r) :=
    (integrable_mSourceCount (q := q) α β r).add
      (integrable_mTargetCount (q := q) α β r)
  refine hbdd.mono'
    (measurable_tileLabelDiscrepancy (q := q) (C := C) (A := A) (B := B)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_tileLabelDiscrepancy_le ω

end OTSelector.Probability
