import OTSelector.Probability.EmpiricalMeasure
import OTSelector.Finite.CostOptimizer
import OTSelector.Finite.PerturbedValue
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! The original two-color finite experiment has an everywhere measurable
optimal physical plan with both empirical marginals, even when costs have ties.
Its actual physical energy equals the original finite assignment minimum. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Ω] {n : ℕ}

/-- A measurable finite sample gives a measurable empirical measure. -/
theorem measurable_originalEmpiricalMeasure
    (x : Ω → Fin n → X) (hx : ∀ i, Measurable (fun w ↦ x w i)) :
    Measurable (fun w ↦ empiricalMeasure (x w)) := by
  apply Measure.measurable_of_measurable_coe
  intro H hH
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  exact (Finset.measurable_sum _ (fun i _ ↦
    (Measure.measurable_coe hH).comp (Measure.measurable_dirac.comp (hx i)))).const_mul _

/-- Nonnegative integration against a generic empirical measure is its exact
finite average, including repeated observations. -/
theorem lintegral_originalEmpiricalMeasure (x : Fin n → X)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂empiricalMeasure x) = (n : ℝ≥0∞)⁻¹ * ∑ i, f (x i) := by
  rw [empiricalMeasure, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac' _ hf, smul_eq_mul]

/-- The original full iid physical sample paired by the fixed exact tie rule.
The definition does not discard observations or condition on a local core. -/
def originalIIDOptimalPhysicalPlan (cost : X → Y → ℝ) (scale : ℝ)
    (ξ : (Fin n → X) × (Fin n → Y)) : Measure (X × Y) :=
  empiricalMeasure (fun i ↦ (ξ.1 i, ξ.2
    (firstOptimalAssignment (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) i)))

/-- The deterministic first-minimum rule keeps the actual physical plan
measurable for every sample, without uniqueness or a selected-event premise. -/
theorem measurable_originalIIDOptimalPhysicalPlan
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) (scale : ℝ) :
    Measurable (originalIIDOptimalPhysicalPlan (n := n) cost scale) := by
  classical
  change Measurable (fun p : X × Y ↦ cost p.1 p.2) at hcost
  let _ : MeasurableSpace (Assignment n) := ⊤
  let _ : MeasurableSingletonClass (Assignment n) := ⟨fun _ ↦ trivial⟩
  have hc (i j : Fin n) : Measurable
      (fun ξ : (Fin n → X) × (Fin n → Y) ↦ scale * cost (ξ.1 i) (ξ.2 j)) :=
    by
      have hxy : Measurable (fun ξ : (Fin n → X) × (Fin n → Y) ↦ (ξ.1 i, ξ.2 j)) :=
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp measurable_snd)
      exact (hcost.comp hxy).const_mul scale
  have hσ := measurable_firstOptimalAssignment
    (fun ξ : (Fin n → X) × (Fin n → Y) ↦
      fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) hc
  apply measurable_originalEmpiricalMeasure
  intro i
  apply ((measurable_pi_apply i).comp measurable_fst).prodMk
  have hi : Measurable (fun ξ : (Fin n → X) × (Fin n → Y) ↦
      firstOptimalAssignment (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) i) :=
    (measurable_of_countable (fun σ : Assignment n ↦ σ i)).comp hσ
  have heval : Measurable (fun p : (Fin n → Y) × Fin n ↦ p.1 p.2) :=
    measurable_from_prod_countable_left (fun j ↦ measurable_pi_apply j)
  exact heval.comp (measurable_snd.prodMk hi)

/-- Every original source observation keeps exactly its empirical mass. -/
theorem originalIIDOptimalPhysicalPlan_source (cost : X → Y → ℝ) (scale : ℝ)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    (originalIIDOptimalPhysicalPlan cost scale ξ).map Prod.fst = empiricalMeasure ξ.1 := by
  rw [originalIIDOptimalPhysicalPlan, map_empiricalMeasure _ _ measurable_fst]
  rfl

/-- Every original target observation keeps exactly its empirical mass. -/
theorem originalIIDOptimalPhysicalPlan_target (cost : X → Y → ℝ) (scale : ℝ)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    (originalIIDOptimalPhysicalPlan cost scale ξ).map Prod.snd = empiricalMeasure ξ.2 := by
  rw [originalIIDOptimalPhysicalPlan, map_empiricalMeasure _ _ measurable_snd]
  exact empiricalMeasure_comp_perm ξ.2 _

instance originalIIDOptimalPhysicalPlan.instIsProbabilityMeasure [NeZero n]
    (cost : X → Y → ℝ) (scale : ℝ) (ξ : (Fin n → X) × (Fin n → Y)) :
    IsProbabilityMeasure (originalIIDOptimalPhysicalPlan cost scale ξ) :=
  empiricalMeasure.instIsProbabilityMeasure _

/-- A real measurable physical readout is integrable in each original finite
plan. This fact uses only its finite support, not a population moment input. -/
theorem integrable_originalIIDOptimalPhysicalPlan [NeZero n]
    (cost : X → Y → ℝ) (scale : ℝ)
    (ξ : (Fin n → X) × (Fin n → Y))
    {f : X × Y → ℝ} (hf : StronglyMeasurable f) :
    Integrable f (originalIIDOptimalPhysicalPlan cost scale ξ) := by
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i _
    exact integrable_dirac' hf (by simp)
  · exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- The actual plan's scaled physical energy is exactly the normalized
original finite minimum, with no local density or frame approximation. -/
theorem integral_originalIIDOptimalPhysicalPlan_cost
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℝ) (ξ : (Fin n → X) × (Fin n → Y)) :
    (∫ p, scale * cost p.1 p.2 ∂originalIIDOptimalPhysicalPlan cost scale ξ) =
      perturbedAssignmentValue (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) 0 0 / n := by
  change Measurable (fun p : X × Y ↦ cost p.1 p.2) at hcost
  change _ = perturbedAssignmentValue
    (show Matrix (Fin n) (Fin n) ℝ from fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) 0 0 / n
  rw [originalIIDOptimalPhysicalPlan]
  rw [integral_empiricalMeasure _ (hcost.const_mul scale).stronglyMeasurable]
  have hv := perturbedAssignmentValue_eq_of_optimal
    (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) 0 0
    (firstOptimalAssignment (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)))
    (by simpa only [perturbedEdgeCost_zero] using
      firstOptimalAssignment_isOptimal (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)))
  rw [hv]
  simp only [perturbedEdgeCost_zero, assignmentCost, div_eq_mul_inv, mul_comm]

/-- Nonnegative physical costs give the exact nonnegative energy, still on
the unchanged original finite plan. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_cost [NeZero n]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (hcost0 : ∀ x y, 0 ≤ cost x y) {scale : ℝ} (hscale : 0 ≤ scale)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    (∫⁻ p, ENNReal.ofReal (scale * cost p.1 p.2)
      ∂originalIIDOptimalPhysicalPlan cost scale ξ) =
      ENNReal.ofReal (perturbedAssignmentValue
        (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) 0 0 / n) := by
  change Measurable (fun p : X × Y ↦ cost p.1 p.2) at hcost
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_originalIIDOptimalPhysicalPlan cost scale ξ
      (hcost.const_mul scale).stronglyMeasurable)
    (Filter.Eventually.of_forall (fun p ↦ mul_nonneg hscale (hcost0 p.1 p.2)))]
  rw [integral_originalIIDOptimalPhysicalPlan_cost cost hcost scale ξ]

end OTSelector.Reconstruction
