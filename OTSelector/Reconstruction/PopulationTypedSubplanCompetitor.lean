import OTSelector.Reconstruction.PopulationTypedSubplanEnergy
import OTSelector.Reconstruction.TaggedDyadicCompetitorEnergy

/-!
# One original competitor has total and small-subplan energy control

The fixed subplan refinement preserves the whole original physical population.
The same measurable full permutation bounds total cost and the cost attributed
to that prescribed subplan, with constants independent of its mass.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)

/-- The same original-sample full assignment satisfies both the uniform total
energy estimate and the prescribed subplan's vanishing-mass estimate. -/
theorem fixed_subplan_full_competitor {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π) :
    let R := D.refineSubplan η hη
    ∃ K : ℕ,
      (∀ i : Fin n, Measurable (fun ξ ↦
        taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) ξ i)) ∧
      (Integrable (fun ξ ↦ assignmentCost (fun i j ↦ cost (ξ.1 i).1 (ξ.2 j).1)
        (taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) ξ)) (R.markedLaw n) ∧
        ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
          (∫ ξ, assignmentCost (fun i j ↦ cost (ξ.1 i).1 (ξ.2 j).1)
            (taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) ξ)
            ∂R.markedLaw n) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card (Option (Bool × T)) : ℝ) ^ (2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card (Option (Bool × T)))) ∧
      (Integrable (D.subplanAttributedEnergy η hη n K) (R.markedLaw n) ∧
        ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
          (∫ ξ, D.subplanAttributedEnergy η hη n K ξ ∂R.markedLaw n) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
            (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal) := by
  let R := D.refineSubplan η hη
  obtain ⟨hP, hL, hx, hy, _⟩ := R.iid_facts hπ n
  let : IsProbabilityMeasure (R.markedLaw n) := hP
  let : IsProbabilityMeasure R.coordinateLaw := hL
  obtain ⟨K, hK⟩ := R.marked_all_smallMass_energies hq hn hπ
  have hσ := measurable_taggedHierarchyAssignment_eval K (R.sourceSample n)
    (R.targetSample n) hx hy
  have hs := hK (selectedSubplanTags (T := T))
  rw [card_selectedSubplanTags, D.refineSubplan_selected_coordinate_mass η hη] at hs
  refine ⟨K, hσ, ?_, hs⟩
  have hmass : (∑ t : Option (Bool × T), R.coordinateLaw.real {x | x.1 = t}) = 1 := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      sum_measureReal_preimage_singleton (μ := R.coordinateLaw) Finset.univ (f := Prod.fst)
        (fun t _ ↦ measurable_fst (measurableSet_singleton t))
  have hall := hK Finset.univ
  simp only [Finset.card_univ, hmass, Real.one_rpow, Real.sqrt_one, mul_one] at hall
  have hcm (i j : Fin n) : Measurable (fun ξ :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        cost (ξ.1 i).1 (ξ.2 j).1) :=
    D.measurable_cost.comp (show Measurable (fun ξ :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        ((ξ.1 i).1, (ξ.2 j).1)) from by fun_prop)
  have hb := R.iid_cost_bounds hπ n
  have ht := expected_assignmentCost_le_all_type_energy (R.markedLaw n)
    (R.sourceSample n) (R.targetSample n) (fun ξ i j ↦ cost (ξ.1 i).1 (ξ.2 j).1)
    hcm (taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n))
    hσ (by positivity) hb.1 hb.2 hall.1 hall.2
  refine ⟨ht.1, ht.2.trans ?_⟩
  apply add_le_add le_rfl
  simpa only [mul_one, R, refineSubplan] using mul_le_mul_of_nonneg_left
    (highDimensional_count_power_le_one hq hn)
    (mul_nonneg R.bound_nonneg (Real.sqrt_nonneg _))

end OTSelector.Reconstruction.PopulationTypedCostData
