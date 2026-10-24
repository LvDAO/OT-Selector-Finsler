import OTSelector.Reconstruction.PopulationTypedRecoveryEnergy
import OTSelector.Reconstruction.FinslerPopulationTypedSubplanData
import OTSelector.Reconstruction.TaggedDyadicPressureRecovery

/-!
# Energy recovery for a fixed original subplan

The original RN refinement marks the prescribed subplan before sampling. A single
full assignment controls all edges incident to its selected marks, including the
count-completion edges. The constants depend only on the original finite atlas.
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

/-- The literal full-permutation energy charged to marks belonging to the fixed
original subplan. The physical samples and edge cost are unchanged. -/
def subplanAttributedEnergy (η : Measure (X × Y)) (hη : η ≤ π) (n K : ℕ)
    (ω : (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T))) : ℝ :=
  let R := D.refineSubplan η hη
  attributedTypesEnergy (selectedSubplanTags (T := T))
    (fun i ↦ R.sourceSample n i ω) (fun i ↦ R.targetSample n i ω)
    (fun i j ↦ cost (ω.1 i).1 (ω.2 j).1)
    (taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) ω)

/-- The small-mass energy bound for every fixed original subplan, with constants
independent of that subplan and the sample size. -/
theorem fixed_subplan_energy {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π) :
    ∃ K : ℕ,
      Integrable (D.subplanAttributedEnergy η hη n K)
        ((D.refineSubplan η hη).markedLaw n) ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ ω, D.subplanAttributedEnergy η hη n K ω
          ∂(D.refineSubplan η hη).markedLaw n) ≤
        D.quadraticConstant * dyadicMatchingConstant q *
          (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
          (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * Real.sqrt (2 * Fintype.card T) *
          (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal := by
  obtain ⟨K, hK⟩ := (D.refineSubplan η hη).marked_all_smallMass_energies hq hn hπ
  refine ⟨K, ?_⟩
  have h := hK (selectedSubplanTags (T := T))
  rw [card_selectedSubplanTags, D.refineSubplan_selected_coordinate_mass η hη] at h
  exact h

omit [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))] [IsFiniteMeasure π]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- The normalization of the original count-completion term vanishes for q > 4,
without a lower bound on the prescribed subplan mass. -/
theorem fixed_subplan_count_error_tendsto (hq : 4 < q) (η : Measure (X × Y)) :
    Filter.Tendsto (fun n : ℕ ↦ D.globalBound * Real.sqrt (2 * Fintype.card T) *
      (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal)
      Filter.atTop (nhds 0) := by
  exact tendsto_normalized_typeCount_error (by exact_mod_cast hq) _ _

end OTSelector.Reconstruction.PopulationTypedCostData
