import OTSelector.Finite.HierarchicalAssignment
import OTSelector.Reconstruction.IIDTypedCountRepair
import OTSelector.Probability.CavitySemidiscretePressureSampling

/-!
# Original iid assignment estimates from a partition hierarchy

The histogram fluctuations are evaluated under the original independent
color laws and applied to one actual full permutation.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Original independent colors have the multiscale histogram estimate for any
finite measurable partition, for arbitrary common population law. -/
theorem iid_partition_discrepancy_bound
    {Ω X C : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype C]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (xs ys : Fin n → Ω → X)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (cell : X → C) (hm : ∀ a, MeasurableSet {x | cell x = a}) :
    Integrable (fun ξ ↦ ∑ a, |partitionCount (fun i ↦ cell (xs i ξ)) a -
      partitionCount (fun i ↦ cell (ys i ξ)) a|) P ∧
    (∫ ξ, ∑ a, |partitionCount (fun i ↦ cell (xs i ξ)) a -
      partitionCount (fun i ↦ cell (ys i ξ)) a| ∂P) ≤
        Real.sqrt (2 * (n : ℝ) * Fintype.card C) := by
  classical
  have hmass : (∑ a, μ.real {x | cell x = a}) = 1 := by
    simpa [Set.preimage, Set.mem_singleton_iff] using (sum_measureReal_preimage_singleton (μ := μ) Finset.univ
      (f := cell) (fun a _ ↦ hm a))
  have heq (zs : Fin n → Ω → X) (a : C) (ξ : Ω) :
      iidTypeCount zs {x | cell x = a} ξ = partitionCount (fun i ↦ cell (zs i ξ)) a := by
    simp only [iidTypeCount, partitionCount, partitionIndicator, Set.indicator,
      Set.mem_ofPred_eq]
  simpa only [heq, mul_one] using iidTypeCount_total_difference_bound P μ μ xs ys hx hy
    hxi hyi hxl hyl hxy (fun a ↦ {x | cell x = a}) (fun a ↦ {x | cell x = a})
    hm hm (fun _ ↦ rfl) hmass

/-- A finite partition hierarchy gives a distribution-free expected assignment
bound. Its competitor is the one genuine permutation from the hierarchy theorem. -/
theorem expected_hierarchical_assignment_bound
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    {K n : ℕ} {C : Fin K → Type*} [∀ k, Fintype (C k)]
    (xs ys : Fin n → Ω → X)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (cell : (k : Fin K) → X → C k)
    (hm : ∀ k a, MeasurableSet {x | cell k x = a})
    (hnested : ∀ (k l : Fin K), k ≤ l → ∀ a b,
      cell l a = cell l b → cell k a = cell k b)
    (cost : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j))
    (hcn : ∀ ξ i j, 0 ≤ cost ξ i j)
    (base : ℝ) (weight : Fin K → ℝ) (hw : ∀ k, 0 ≤ weight k)
    (hcost : ∀ ξ i j, cost ξ i j ≤ base +
      ∑ k, weight k * partitionDistance (cell k (xs i ξ)) (cell k (ys j ξ))) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (cost ξ) 0 0) P ∧
    (∫ ξ, perturbedAssignmentValue (cost ξ) 0 0 ∂P) ≤ (n : ℝ) * base +
      (1 / 2 : ℝ) * ∑ k, weight k * Real.sqrt (2 * (n : ℝ) * Fintype.card (C k)) := by
  classical
  let d : Fin K → Ω → ℝ := fun k ξ ↦
    ∑ a, |partitionCount (fun i ↦ cell k (xs i ξ)) a -
      partitionCount (fun i ↦ cell k (ys i ξ)) a|
  have hd (k : Fin K) := iid_partition_discrepancy_bound P μ xs ys hx hy hxi hyi hxl hyl
    hxy (cell k) (hm k)
  have hci (i j : Fin n) : Integrable (fun ξ ↦ cost ξ i j) P := by
    apply (integrable_const (base + ∑ k, weight k)).mono' (hc i j).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hcn ξ i j)]
    exact (hcost ξ i j).trans (add_le_add le_rfl (Finset.sum_le_sum (fun k _ ↦ by
      simpa using mul_le_mul_of_nonneg_left (partitionDistance_bounds _ _).2 (hw k))))
  have hi := Probability.integrable_assignmentValue P cost hc hci
  have hdi : Integrable (fun ξ ↦ (n : ℝ) * base + (1 / 2 : ℝ) *
      ∑ k, weight k * d k ξ) P := (integrable_const _).add
        ((integrable_finsetSum _ (fun k _ ↦ (hd k).1.const_mul (weight k))).const_mul _)
  refine ⟨hi, ?_⟩
  have hp (ξ : Ω) : perturbedAssignmentValue (cost ξ) 0 0 ≤
      (n : ℝ) * base + (1 / 2 : ℝ) * ∑ k, weight k * d k ξ := by
    obtain ⟨σ, hσ⟩ := exists_hierarchical_assignment_cost_bound cell hnested
      (fun i ↦ xs i ξ) (fun i ↦ ys i ξ) (cost ξ) base weight (hcost ξ)
    have hv := perturbedAssignmentValue_le (cost ξ) 0 0 σ
    simp only [perturbedEdgeCost_zero] at hv
    exact hv.trans hσ
  have hle := integral_mono hi hdi hp
  rw [integral_add (integrable_const _) ((integrable_finsetSum _
    (fun k _ ↦ (hd k).1.const_mul (weight k))).const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ (fun k _ ↦ (hd k).1.const_mul (weight k))] at hle
  simp only [integral_const_mul] at hle
  exact hle.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun k _ ↦ mul_le_mul_of_nonneg_left (hd k).2 (hw k))) (by norm_num)))

end OTSelector.Reconstruction
