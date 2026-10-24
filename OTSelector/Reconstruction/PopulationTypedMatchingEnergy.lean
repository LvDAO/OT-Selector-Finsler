import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.TaggedDyadicUniformPressure
import OTSelector.Reconstruction.FinslerPopulationTypedIIDFacts
import OTSelector.Reconstruction.FinslerPopulationMarkedAssignmentTransfer

/-!
# Original physical assignment energy from the actual RN-marked experiment

The common type-coordinate law and both independent iid arrays are produced
from the original subcoupling types. Forgetting the RN marks then returns the
literal physical minimum and its expectation under the unchanged populations.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PopulationSubcouplingTypes
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Produced iid laws suffice for the actual original normalized assignment
rate. The marked bounds are later filled by the original finite upper atlas. -/
theorem original_iid_assignment_rate_of_typed_bounds
    {q n : ℕ} (hq : 4 < q) (hn : 0 < n) (hπ : Vlasov.IsCoupling π μ ν)
    (a : T → X → DyadicUnitCube q) (b : T → Y → DyadicUnitCube q)
    (z₀ : DyadicUnitCube q) (ha : ∀ t, Measurable (a t)) (hb : ∀ t, Measurable (b t))
    (hlabel : ∀ t, (D.source t).map (a t) = (D.target t).map (b t))
    (cost : X → Y → ℝ) (hc : Measurable (Function.uncurry cost))
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmarked :
      let P := (Measure.pi (fun _ : Fin n ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : Fin n ↦ D.targetMarkedLaw ν))
      let xs := fun i (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) ↦
        populationTypedCoordinate a z₀ (ω.1 i)
      let ys := fun j (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) ↦
        populationTypedCoordinate b z₀ (ω.2 j)
      (∀ᵐ ω ∂P, ∀ i j, 0 ≤ cost (ω.1 i).1 (ω.2 j).1) ∧
      (∀ᵐ ω ∂P, ∀ i j, cost (ω.1 i).1 (ω.2 j).1 ≤ B) ∧
      ∀ tag : Option T, ∀ᵐ ω ∂P, ∀ i j, (xs i ω).1 = tag → (ys j ω).1 = tag →
        cost (ω.1 i).1 (ω.2 j).1 ≤ C *
          ‖dyadicCubePoint (xs i ω).2 - dyadicCubePoint (ys j ω).2‖ ^ 2) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    Integrable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0) P₀ ∧
    ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
      (∫ ω : (Fin n → X) × (Fin n → Y),
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0 ∂P₀) ≤
      C * dyadicMatchingConstant q * (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
      B * Real.sqrt (2 * Fintype.card (Option T)) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) := by
  classical
  let P := (Measure.pi (fun _ : Fin n ↦ D.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ D.targetMarkedLaw ν))
  let L := D.typeCoordinateLaw μ a z₀
  let xs := fun i (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) ↦
    populationTypedCoordinate a z₀ (ω.1 i)
  let ys := fun j (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) ↦
    populationTypedCoordinate b z₀ (ω.2 j)
  obtain ⟨hP, hL, hx, hy, hxi, hyi, hxl, hyl, hxy⟩ :=
    D.iid_type_coordinate_facts (I := Fin n) (J := Fin n) hπ a b z₀ ha hb hlabel
  let : IsProbabilityMeasure P := hP
  let : IsProbabilityMeasure L := hL
  have hcm (i j : Fin n) : Measurable (fun ω : (Fin n → X × Option T) ×
      (Fin n → Y × Option T) ↦ cost (ω.1 i).1 (ω.2 j).1) := by
    exact hc.comp (show Measurable (fun ω : (Fin n → X × Option T) ×
      (Fin n → Y × Option T) ↦ ((ω.1 i).1, (ω.2 j).1)) from by fun_prop)
  have he := expected_assignmentValue_le_taggedHierarchy_rate hq hn P L xs ys hx hy
    hxi hyi hxl hyl hxy (fun ω i j ↦ cost (ω.1 i).1 (ω.2 j).1) hcm hC hB
    hmarked.1 hmarked.2.1 hmarked.2.2
  have hm : Measurable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0) := by
    apply Probability.measurable_assignmentValue
    intro i j
    exact hc.comp (show Measurable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      (ω.1 i, ω.2 j)) from by fun_prop)
  obtain ⟨hi, hint⟩ := D.iid_physical_integral hπ _ hm
  exact ⟨hi.mpr he.1, hint ▸ he.2⟩

/-- A uniform sample-size bound for the literal original physical minimum. -/
theorem original_iid_assignment_uniform_of_typed_bounds
    {q n : ℕ} (hq : 4 < q) (hn : 0 < n) (hπ : Vlasov.IsCoupling π μ ν)
    (a : T → X → DyadicUnitCube q) (b : T → Y → DyadicUnitCube q)
    (z₀ : DyadicUnitCube q) (ha : ∀ t, Measurable (a t)) (hb : ∀ t, Measurable (b t))
    (hlabel : ∀ t, (D.source t).map (a t) = (D.target t).map (b t))
    (cost : X → Y → ℝ) (hc : Measurable (Function.uncurry cost))
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmarked :
      let P := (Measure.pi (fun _ : Fin n ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : Fin n ↦ D.targetMarkedLaw ν))
      let xs := fun i (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) ↦
        populationTypedCoordinate a z₀ (ω.1 i)
      let ys := fun j (ω : (Fin n → X × Option T) × (Fin n → Y × Option T)) ↦
        populationTypedCoordinate b z₀ (ω.2 j)
      (∀ᵐ ω ∂P, ∀ i j, 0 ≤ cost (ω.1 i).1 (ω.2 j).1) ∧
      (∀ᵐ ω ∂P, ∀ i j, cost (ω.1 i).1 (ω.2 j).1 ≤ B) ∧
      ∀ tag : Option T, ∀ᵐ ω ∂P, ∀ i j, (xs i ω).1 = tag → (ys j ω).1 = tag →
        cost (ω.1 i).1 (ω.2 j).1 ≤ C *
          ‖dyadicCubePoint (xs i ω).2 - dyadicCubePoint (ys j ω).2‖ ^ 2) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    Integrable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0) P₀ ∧
    ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
      (∫ ω : (Fin n → X) × (Fin n → Y),
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0 ∂P₀) ≤
      C * dyadicMatchingConstant q * (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
      B * Real.sqrt (2 * Fintype.card (Option T)) := by
  have h := D.original_iid_assignment_rate_of_typed_bounds hq hn hπ a b z₀ ha hb hlabel
    cost hc hC hB hmarked
  refine ⟨h.1, h.2.trans ?_⟩
  apply add_le_add le_rfl
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (highDimensional_count_power_le_one hq hn) (mul_nonneg hB (Real.sqrt_nonneg _))

end PopulationSubcouplingTypes
end OTSelector.Reconstruction
