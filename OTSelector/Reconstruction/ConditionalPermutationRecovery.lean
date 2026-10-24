import OTSelector.Finite.FractionalOptimal
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Returning a marked permutation to the original sample

Conditioning a finite permutation on the original sample gives a measurable
doubly stochastic matrix. Every integrable physical edge cost has exactly the
same expectation before and after this conditional averaging.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
  [MeasurableSpace (Assignment n)] [MeasurableSingletonClass (Assignment n)]

omit [MeasurableSingletonClass (Assignment n)] in
/-- Measurability of every matched index gives measurability of the complete
finite permutation, with its discrete measurable structure. -/
theorem measurable_assignment_of_eval (σ : Ω → Assignment n)
    (hσ : ∀ i, Measurable (fun ω ↦ σ ω i)) : Measurable σ := by
  apply measurable_to_countable'
  intro τ
  have he : σ ⁻¹' {τ} = ⋂ i, {ω | σ ω i = τ i} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
    exact ⟨fun h i ↦ congrArg (fun e : Assignment n ↦ e i) h, fun h ↦ Equiv.ext h⟩
  rw [he]
  exact MeasurableSet.iInter fun i ↦ (hσ i) (measurableSet_singleton _)

/-- The average permutation matrix conditioned on the unchanged physical sample. -/
def conditionalPermutationMatrix (P : Measure Ω) [IsFiniteMeasure P]
    (physical : Ω → X) (σ : Ω → Assignment n) (x : X) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ τ : Assignment n, (condDistrib σ physical P x).real {τ} • τ.permMatrix ℝ

/-- Every conditional matrix is feasible, including physical samples in null sets. -/
theorem conditionalPermutationMatrix_mem (P : Measure Ω) [IsFiniteMeasure P]
    (physical : Ω → X) (σ : Ω → Assignment n) (x : X) :
    conditionalPermutationMatrix P physical σ x ∈ doublyStochastic ℝ (Fin n) := by
  apply convex_doublyStochastic.sum_mem
  · intro τ _
    exact ENNReal.toReal_nonneg
  · simp
  · intro τ _
    exact permMatrix_mem_doublyStochastic

/-- The returned fractional plan is a measurable function of the physical sample. -/
theorem measurable_conditionalPermutationMatrix_eval (P : Measure Ω) [IsFiniteMeasure P]
    (physical : Ω → X) (σ : Ω → Assignment n) (i j : Fin n) :
    Measurable (fun x ↦ conditionalPermutationMatrix P physical σ x i j) := by
  simp only [conditionalPermutationMatrix, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact Finset.measurable_sum _ fun τ _ ↦
    ((Kernel.measurable_coe (condDistrib σ physical P)
      (measurableSet_singleton τ)).ennreal_toReal).mul_const _

/-- Conditional averaging preserves both integrability and the expected value of
the selected permutation's actual physical linear cost. -/
theorem conditionalPermutationMatrix_integral_cost
    (P : Measure Ω) [IsFiniteMeasure P]
    (physical : Ω → X) (hphysical : Measurable physical)
    (σ : Ω → Assignment n) (hσ : ∀ i, Measurable (fun ω ↦ σ ω i))
    (cost : X → Matrix (Fin n) (Fin n) ℝ)
    (hcost : ∀ i j, Measurable (fun x ↦ cost x i j))
    (hint : Integrable (fun ω ↦ assignmentCost (cost (physical ω)) (σ ω)) P) :
    Integrable (fun x ↦ fractionalAssignmentCost (cost x)
      (conditionalPermutationMatrix P physical σ x)) (P.map physical) ∧
    (∫ x, fractionalAssignmentCost (cost x)
      (conditionalPermutationMatrix P physical σ x) ∂P.map physical) =
        ∫ ω, assignmentCost (cost (physical ω)) (σ ω) ∂P := by
  have hσm := measurable_assignment_of_eval σ hσ
  let g : X × Assignment n → ℝ := fun p ↦ assignmentCost (cost p.1) p.2
  have hg : Measurable g := measurable_from_prod_countable_left fun τ ↦
    Finset.measurable_sum _ fun i _ ↦ hcost i (τ i)
  have hpair : Measurable (fun ω ↦ (physical ω, σ ω)) := hphysical.prodMk hσm
  have hjoint : Integrable g (P.map (fun ω ↦ (physical ω, σ ω))) :=
    (integrable_map_measure hg.aestronglyMeasurable hpair.aemeasurable).mpr hint
  have he : (fun x ↦ fractionalAssignmentCost (cost x)
      (conditionalPermutationMatrix P physical σ x)) =ᵐ[P.map physical]
      fun x ↦ ∫ τ, g (x, τ) ∂condDistrib σ physical P x := by
    filter_upwards [hjoint.condDistrib_ae_map hσm.aemeasurable] with x hx
    rw [integral_fintype hx, conditionalPermutationMatrix,
      fractionalAssignmentCost_sum_perm]
    rfl
  refine ⟨(hjoint.integral_condDistrib_map hσm.aemeasurable).congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  have hjoint' : Integrable g ((P.map physical) ⊗ₘ condDistrib σ physical P) := by
    rwa [compProd_map_condDistrib hσm.aemeasurable]
  rw [← Measure.integral_compProd hjoint', compProd_map_condDistrib hσm.aemeasurable,
    integral_map hpair.aemeasurable hg.aestronglyMeasurable]

end OTSelector.Reconstruction
