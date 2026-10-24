import OTSelector.Reconstruction.FinslerPopulationMarkedAssignmentTransfer
import OTSelector.Reconstruction.ConditionalPermutationRecovery

/-!
# Actual marked matching returns a plan on the original physical iid sample

The original population RN marking has the exact physical iid pushforward.
Conditioning its full permutation gives one measurable fractional plan on that
original sample. Every integrable physical cost and probe keeps its expectation.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [MeasurableSingletonClass (Option T)] in
/-- An actual full marked assignment yields a feasible measurable plan on the
unchanged original two-color iid sample, preserving every physical linear readout
with the same returned matrix. The construction assumes no balanced type counts. -/
theorem original_iid_fractional_recovery {n : ℕ}
    (hπ : Vlasov.IsCoupling π μ ν)
    (σ : ((Fin n → X × Option T) × (Fin n → Y × Option T)) → Assignment n)
    (hσ : ∀ i, Measurable (fun ξ ↦ σ ξ i)) :
    let P := (Measure.pi (fun _ : Fin n ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ D.targetMarkedLaw ν))
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    let forget := Prod.map (fun x : Fin n → X × Option T ↦ fun i ↦ (x i).1)
      (fun y : Fin n → Y × Option T ↦ fun j ↦ (y j).1)
    ∃ W : ((Fin n → X) × (Fin n → Y)) → Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, Measurable (fun ξ ↦ W ξ i j)) ∧
      (∀ ξ, W ξ ∈ doublyStochastic ℝ (Fin n)) ∧
      ∀ cost : ((Fin n → X) × (Fin n → Y)) → Matrix (Fin n) (Fin n) ℝ,
        (∀ i j, Measurable (fun ξ ↦ cost ξ i j)) →
        Integrable (fun ξ ↦ assignmentCost (cost (forget ξ)) (σ ξ)) P →
        Integrable (fun ξ ↦ fractionalAssignmentCost (cost ξ) (W ξ)) P₀ ∧
          (∫ ξ, fractionalAssignmentCost (cost ξ) (W ξ) ∂P₀) =
            ∫ ξ, assignmentCost (cost (forget ξ)) (σ ξ) ∂P := by
  let _instAssignmentMeasurable : MeasurableSpace (Assignment n) := ⊤
  let P := (Measure.pi (fun _ : Fin n ↦ D.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ D.targetMarkedLaw ν))
  let forget := Prod.map (fun x : Fin n → X × Option T ↦ fun i ↦ (x i).1)
    (fun y : Fin n → Y × Option T ↦ fun j ↦ (y j).1)
  have hforget : Measurable forget := by fun_prop
  refine ⟨conditionalPermutationMatrix P forget σ,
    fun i j ↦ measurable_conditionalPermutationMatrix_eval P forget σ i j,
    fun ξ ↦ conditionalPermutationMatrix_mem P forget σ ξ, ?_⟩
  intro cost hc hi
  have h := conditionalPermutationMatrix_integral_cost P forget hforget σ hσ cost hc hi
  simpa only [P, forget, D.iid_physical_law hπ] using h

end OTSelector.Reconstruction.PopulationSubcouplingTypes
