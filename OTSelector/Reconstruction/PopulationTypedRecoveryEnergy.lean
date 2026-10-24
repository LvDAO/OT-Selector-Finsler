import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.PopulationTypedMatchingEnergy
import OTSelector.Reconstruction.FinslerPopulationTypedCostData

/-!
# Expected energy from actual original population type data

All iid and samplewise quadratic inputs are discharged by the actual RN-marked
population producer. Both the literal original minimum and every deterministic
subplan attribution retain the same original marginal laws.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)

/-- The original physical assignment rate, with no supplied iid or samplewise
cost hypotheses: the actual type data produce every such input. -/
theorem original_iid_assignment_rate {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    Integrable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0) P₀ ∧
    ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
      (∫ ω : (Fin n → X) × (Fin n → Y),
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0 ∂P₀) ≤
      D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card (Option T)) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) := by
  have hb := D.iid_cost_bounds hπ n
  exact D.types.original_iid_assignment_rate_of_typed_bounds hq hn hπ
    D.sourceCoordinate D.targetCoordinate (cubeOrigin (q := q))
    D.measurable_sourceCoordinate D.measurable_targetCoordinate D.common_coordinate
    cost D.measurable_cost D.quadratic_nonneg D.bound_nonneg
    ⟨hb.1, hb.2, D.iid_quadratic hπ n⟩

/-- A single constant bounds the normalized original expected assignment for
all positive sample sizes in dimension q > 4. -/
theorem original_iid_assignment_uniform {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    Integrable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0) P₀ ∧
    ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
      (∫ ω : (Fin n → X) × (Fin n → Y),
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0 ∂P₀) ≤
      D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card (Option T)) := by
  have h := D.original_iid_assignment_rate hq hn hπ
  refine ⟨h.1, h.2.trans ?_⟩
  apply add_le_add le_rfl
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (highDimensional_count_power_le_one hq hn)
    (mul_nonneg D.bound_nonneg (Real.sqrt_nonneg _))

/-- The same original marked full competitor controls every fixed type
subcollection. Its mass is read directly in the actual common coordinate law. -/
theorem marked_all_smallMass_energies {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) :
    ∃ K : ℕ, ∀ S : Finset (Option T),
      Integrable (fun ω ↦ attributedTypesEnergy S (fun i ↦ D.sourceSample n i ω)
        (fun i ↦ D.targetSample n i ω) (fun i j ↦ cost (ω.1 i).1 (ω.2 j).1)
        (taggedHierarchyAssignment K (D.sourceSample n) (D.targetSample n) ω)) (D.markedLaw n) ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ ω, attributedTypesEnergy S (fun i ↦ D.sourceSample n i ω)
          (fun i ↦ D.targetSample n i ω) (fun i j ↦ cost (ω.1 i).1 (ω.2 j).1)
          (taggedHierarchyAssignment K (D.sourceSample n) (D.targetSample n) ω) ∂D.markedLaw n) ≤
        D.quadraticConstant * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ)) *
          (∑ t ∈ S, D.coordinateLaw.real {x | x.1 = t}) ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * Real.sqrt (2 * S.card) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) *
          Real.sqrt (∑ t ∈ S, D.coordinateLaw.real {x | x.1 = t}) := by
  obtain ⟨hP, hL, hx, hy, hxi, hyi, hxl, hyl, hxy⟩ := D.iid_facts hπ n
  let : IsProbabilityMeasure (D.markedLaw n) := hP
  let : IsProbabilityMeasure D.coordinateLaw := hL
  have hcm (i j : Fin n) : Measurable (fun ω : (Fin n → X × Option T) ×
      (Fin n → Y × Option T) ↦ cost (ω.1 i).1 (ω.2 j).1) :=
    D.measurable_cost.comp (show Measurable (fun ω : (Fin n → X × Option T) ×
      (Fin n → Y × Option T) ↦ ((ω.1 i).1, (ω.2 j).1)) from by fun_prop)
  have hb := D.iid_cost_bounds hπ n
  exact exists_taggedHierarchy_all_smallMass_energies hq hn (D.markedLaw n) D.coordinateLaw
    (D.sourceSample n) (D.targetSample n) hx hy hxi hyi hxl hyl hxy
    (fun ω i j ↦ cost (ω.1 i).1 (ω.2 j).1) hcm
    D.quadratic_nonneg D.bound_nonneg hb.1 hb.2 (D.iid_quadratic hπ n)

end PopulationTypedCostData
end OTSelector.Reconstruction
