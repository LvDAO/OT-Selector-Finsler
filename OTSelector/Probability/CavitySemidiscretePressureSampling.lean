import OTSelector.Probability.CavitySemidiscretePressureExtension
import OTSelector.Probability.IIDBipartiteAssignment

/-!
# Finite pressure integrability and transfer to original iid samples

The actual attained assignment value is measurable and integrable whenever its
finitely many original edge costs are. The exact iid array law transfers the complete
Dirichlet semidiscrete pressure identity to any original probability space.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The actual finite assignment minimum is the infimum of its finitely many objectives. -/
theorem assignmentValue_eq_iInf_cost (cost : Matrix (Fin n) (Fin n) ℝ) :
    perturbedAssignmentValue cost 0 0 = ⨅ σ : Assignment n, assignmentCost cost σ := by
  have hle σ : perturbedAssignmentValue cost 0 0 ≤ assignmentCost cost σ := by
    simpa only [perturbedEdgeCost_zero] using perturbedAssignmentValue_le cost 0 0 σ
  apply le_antisymm (le_ciInf hle)
  have hb : BddBelow (range (assignmentCost cost)) :=
    ⟨_, by rintro _ ⟨σ, rfl⟩; exact hle σ⟩
  have hmin : perturbedAssignmentValue cost 0 0 =
      assignmentCost cost (optimalAssignment cost) := by
    simp only [perturbedAssignmentValue, perturbedEdgeCost_zero]
  exact (ciInf_le hb (optimalAssignment cost)).trans_eq hmin.symm

/-- Entrywise measurability gives measurability of the actual attained value, including ties. -/
theorem measurable_assignmentValue (cost : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hc : ∀ i j, Measurable (fun ω ↦ cost ω i j)) :
    Measurable (fun ω ↦ perturbedAssignmentValue (cost ω) 0 0) := by
  simp only [assignmentValue_eq_iInf_cost]
  apply Measurable.iInf
  intro σ
  exact Finset.measurable_sum _ (fun i _ ↦ hc i (σ i))

/-- Summed absolute edge costs bound the actual minimum without an optimizer selection premise. -/
theorem norm_assignmentValue_le_sum (cost : Matrix (Fin n) (Fin n) ℝ) :
    ‖perturbedAssignmentValue cost 0 0‖ ≤ ∑ i, ∑ j, ‖cost i j‖ := by
  simp only [perturbedAssignmentValue, perturbedEdgeCost_zero, assignmentCost]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (cost i j)) (Finset.mem_univ _)

/-- Integrable original edges give an integrable finite minimum. -/
theorem integrable_assignmentValue (P : Measure Ω)
    (cost : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hc : ∀ i j, Measurable (fun ω ↦ cost ω i j))
    (hci : ∀ i j, Integrable (fun ω ↦ cost ω i j) P) :
    Integrable (fun ω ↦ perturbedAssignmentValue (cost ω) 0 0) P := by
  apply (integrable_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun j _ ↦ (hci i j).norm))).mono'
    (measurable_assignmentValue cost hc).aestronglyMeasurable
  exact Eventually.of_forall fun ω ↦ norm_assignmentValue_le_sum (cost ω)

variable {m : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

/-- The complete bounded-tilt pressure identity on the original iid probability space. -/
theorem integral_original_iid_pressure_eq_dirichlet_semidiscreteValue
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (X : Fin (m + 1) → Ω → S) (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c g : Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (c j)) (hci : ∀ j, Integrable (c j) μ)
    (hg : ∀ j, Measurable (g j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (G : ℝ≥0) (hbound : ∀ s j, |g j s| ≤ G) (t : ℝ) :
    Integrable (semidiscreteValue μ (fun s j ↦ c j s + t * g j s)) (dirichletOne m) ∧
    Integrable (fun ω ↦ perturbedAssignmentValue (fun i j ↦ c j (X i ω))
      (fun i j ↦ g j (X i ω)) t / (m + 1 : ℕ)) P ∧
    (∫ ω, perturbedAssignmentValue (fun i j ↦ c j (X i ω))
      (fun i j ↦ g j (X i ω)) t / (m + 1 : ℕ) ∂P) =
      ∫ p, semidiscreteValue μ (fun s j ↦ c j s + t * g j s) p ∂dirichletOne m := by
  have hm : Measurable (fun ω i ↦ X i ω) := measurable_pi_lambda _ hX
  have hmap : P.map (fun ω i ↦ X i ω) = Measure.pi (fun _ : Fin (m + 1) ↦ μ) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable) hi]
    simp_rw [hlaw]
  have h := integral_iid_perturbedAssignmentValue_eq_dirichlet_semidiscreteValue
    μ c g hc hci hg hatom G hbound t
  have hpres : MeasurePreserving (fun ω i ↦ X i ω) P (Measure.pi (fun _ : Fin (m + 1) ↦ μ)) :=
    ⟨hm, hmap⟩
  refine ⟨h.1, hpres.integrable_comp_of_integrable h.2.1, ?_⟩
  rw [← h.2.2, ← hmap, integral_map hm.aemeasurable]
  rw [hmap]
  exact h.2.1.aestronglyMeasurable

end OTSelector.Probability
