import OTSelector.Probability.TypedPopulationSampling
import OTSelector.Probability.CavitySemidiscretePressureSampling

/-!
# Return marked assignment estimates to the original physical iid law

Forgetting the produced RN marks preserves every measurable physical statistic,
its integrability and expectation. Bounds for the literal marked-sample minimum
therefore apply to the unchanged original two-color physical sample.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PopulationSubcouplingTypes
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [MeasurableSingletonClass (Option T)] in
/-- Every measurable physical statistic has identical integrability and expectation
under the original iid law and its produced RN-marked extension. -/
theorem iid_physical_integral {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν)
    (F : (I → X) × (J → Y) → ℝ) (hF : Measurable F) :
    let P := (Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))
    let P₀ := (Measure.pi (fun _ : I ↦ μ)).prod (Measure.pi (fun _ : J ↦ ν))
    let forget := Prod.map (fun x : I → X × Option T ↦ fun i ↦ (x i).1)
      (fun y : J → Y × Option T ↦ fun j ↦ (y j).1)
    (Integrable F P₀ ↔ Integrable (fun ω ↦ F (forget ω)) P) ∧
      (∫ ω, F (forget ω) ∂P) = ∫ ω, F ω ∂P₀ := by
  have hm : Measurable (Prod.map (fun x : I → X × Option T ↦ fun i ↦ (x i).1)
      (fun y : J → Y × Option T ↦ fun j ↦ (y j).1)) := by fun_prop
  have hi := integrable_map_measure (μ :=
    (Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))) hF.aestronglyMeasurable hm.aemeasurable
  have he := integral_map (μ :=
    (Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))) hm.aemeasurable hF.aestronglyMeasurable
  rw [D.iid_physical_law hπ] at hi he
  exact ⟨hi, he.symm⟩

omit [MeasurableSingletonClass (Option T)] in
/-- A finite matching bound proved in the actual marked experiment is an exact
bound for the unchanged original physical assignment minimum. -/
theorem original_iid_assignment_bound_of_marked {n : ℕ}
    (hπ : Vlasov.IsCoupling π μ ν) (cost : X → Y → ℝ)
    (hc : Measurable (Function.uncurry cost)) {R : ℝ}
    (hmarked :
      Integrable (fun ω : (Fin n → X × Option T) × (Fin n → Y × Option T) ↦
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i).1 (ω.2 j).1) 0 0)
        ((Measure.pi (fun _ : Fin n ↦ D.sourceMarkedLaw μ)).prod
          (Measure.pi (fun _ : Fin n ↦ D.targetMarkedLaw ν))) ∧
      (∫ ω : (Fin n → X × Option T) × (Fin n → Y × Option T),
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i).1 (ω.2 j).1) 0 0
        ∂(Measure.pi (fun _ : Fin n ↦ D.sourceMarkedLaw μ)).prod
          (Measure.pi (fun _ : Fin n ↦ D.targetMarkedLaw ν))) ≤ R) :
    Integrable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0)
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ∧
      (∫ ω : (Fin n → X) × (Fin n → Y),
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ≤ R := by
  have hm : Measurable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0) := by
    apply Probability.measurable_assignmentValue
    intro i j
    exact hc.comp (show Measurable (fun ω : (Fin n → X) × (Fin n → Y) ↦ (ω.1 i, ω.2 j)) from
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
  obtain ⟨hi, he⟩ := D.iid_physical_integral hπ _ hm
  exact ⟨hi.mpr hmarked.1, he ▸ hmarked.2⟩

end PopulationSubcouplingTypes
end OTSelector.Reconstruction
