import OTSelector.Reconstruction.OriginalIIDActualTiltSignedLower
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Exact signed mean readouts of the genuine particle-indexed original iid optimizer. -/
open Set Function Filter MeasureTheory ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ} [NeZero n]

/-- Every integrable signed original mean-plan readout is the expectation of the
same full original finite plan's readout, including all particles and cost ties. -/
theorem integral_originalIIDOptimalMeanPlan_readout
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) (scale : ℝ)
    (f : X × Y → ℝ) (hf : Integrable f (originalIIDOptimalMeanPlan μ ν cost scale n)) :
    (∫ p, f p ∂originalIIDOptimalMeanPlan μ ν cost scale n) =
      ∫ ξ, ∫ p, f p ∂originalIIDOptimalPhysicalPlan (n := n) cost scale ξ
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)) := by
  let law := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
  let Γ : Kernel ((Fin n → X) × (Fin n → Y)) (X × Y) :=
    ⟨originalIIDOptimalPhysicalPlan cost scale,measurable_originalIIDOptimalPhysicalPlan cost hcost scale⟩
  let : IsMarkovKernel Γ := ⟨fun ξ ↦ by
    change IsProbabilityMeasure (empiricalMeasure _)
    infer_instance⟩
  have hπ : (Γ ∘ₖ Kernel.const Unit law) () = originalIIDOptimalMeanPlan μ ν cost scale n := by
    rw [← Measure.comp_eq_comp_const_apply]
    rfl
  have hf' : Integrable f ((Γ ∘ₖ Kernel.const Unit law) ()) := by rw [hπ]; exact hf
  have h := ProbabilityTheory.Kernel.integral_comp (κ := Kernel.const Unit law) (η := Γ) (a := ()) hf'
  rw [hπ] at h
  exact h

/-- The original mean-plan cost is exactly the original iid assignment minimum
per particle, with its actual scaling and deterministic full-cost optimizer. -/
theorem integral_originalIIDOptimalMeanPlan_assignment_value
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) (scale : ℝ)
    (hf : Integrable (fun p : X × Y ↦ scale*cost p.1 p.2)
      (originalIIDOptimalMeanPlan μ ν cost scale n)) :
    (∫ p, scale*cost p.1 p.2 ∂originalIIDOptimalMeanPlan μ ν cost scale n) =
      ∫ ξ, perturbedAssignmentValue (fun i j ↦ scale*cost (ξ.1 i) (ξ.2 j)) 0 0 / n
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)) := by
  rw [integral_originalIIDOptimalMeanPlan_readout μ ν cost hcost scale _ hf]
  exact integral_congr_ae (Eventually.of_forall (fun ξ ↦ integral_originalIIDOptimalPhysicalPlan_cost cost hcost scale ξ))

end OTSelector.Reconstruction
