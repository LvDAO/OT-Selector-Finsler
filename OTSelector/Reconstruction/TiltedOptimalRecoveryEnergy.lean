import OTSelector.Reconstruction.AssignmentPressureLocalization
import OTSelector.Finite.PressureRegularity
import OTSelector.Finite.CostOptimizer

/-!
# Recovery energy for the whole tilted fractional optimal face

The unperturbed original assignment value controls the base energy of every
fractional tilted optimum. A bounded probe contributes exactly the usual two
comparison terms, so the result can consume the original typed upper bound.
-/

open Set MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false in
/-- Positive microscopic scaling commutes with the literal finite minimum. -/
theorem assignmentValue_posScale {n : ℕ} (c : Matrix (Fin n) (Fin n) ℝ)
    {k : ℝ} (hk : 0 < k) :
    perturbedAssignmentValue (fun i j ↦ k * c i j) 0 0 =
      k * perturbedAssignmentValue c 0 0 := by
  let σ := optimalAssignment c
  have hσ : OptimalAssignment c σ := optimalAssignment_isOptimal c
  have hs : OptimalAssignment (fun i j ↦ k * c i j) σ := by
    simpa only [add_zero] using
      (optimalAssignment_posScale_add_rowColumn_iff c k hk (fun _ ↦ 0) (fun _ ↦ 0) σ).mpr hσ
  have hzero := perturbedAssignmentValue_eq_of_optimal c 0 0 σ
    (by simpa only [perturbedEdgeCost_zero] using hσ)
  have hscaled := perturbedAssignmentValue_eq_of_optimal (fun i j ↦ k * c i j) 0 0 σ
    (by simpa only [perturbedEdgeCost_zero] using hs)
  simp only [perturbedEdgeCost_zero] at hzero hscaled
  rw [hscaled, hzero]
  simp only [assignmentCost, Finset.mul_sum]

/-- Every tilted fractional optimum has base energy at most the original
zero-tilt minimum plus twice the bounded-probe comparison cost. -/
theorem optimalFractional_base_energy_le_zero_pressure {n : ℕ}
    (c g W : Matrix (Fin n) (Fin n) ℝ) (τ G : ℝ)
    (hW : OptimalFractionalAssignment (perturbedEdgeCost c g τ) W)
    (hg : ∀ i j, |g i j| ≤ G) :
    fractionalAssignmentCost c W ≤ perturbedAssignmentValue c 0 0 + 2 * n * |τ| * G := by
  have hv := perturbedAssignmentValue_abs_sub_le_of_edge_bound c g c 0 τ 0 (|τ| * G)
    (fun i j ↦ by
      simpa only [perturbedEdgeCost, zero_mul, add_zero, add_sub_cancel_left, abs_mul] using
        mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg τ))
  have hw := perturbedAssignmentValue_eq_of_optimalFractional c g W τ hW
  rw [fractionalAssignmentCost_perturbedEdgeCost] at hw
  have hp := fractionalAssignmentCost_abs_le_of_feasible hW.1 hg
  have hp' : |τ * fractionalAssignmentCost g W| ≤ |τ| * (n * G) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg τ)
  have hlow := (abs_le.mp hp').1
  have hupp := (abs_le.mp hv).2
  nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- The actual expected base energy of any measurable fractional optimum is
controlled by the original unperturbed expected pressure, including ties. -/
theorem expected_optimalFractional_base_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (c g W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (τ G B : ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hWm : ∀ i j, Measurable (fun ξ ↦ W ξ i j))
    (hopt : ∀ᵐ ξ ∂P, OptimalFractionalAssignment (perturbedEdgeCost (c ξ) (g ξ) τ) (W ξ))
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ c ξ i j)
    (hcb : ∀ᵐ ξ ∂P, ∀ i j, c ξ i j ≤ B)
    (hgb : ∀ᵐ ξ ∂P, ∀ i j, |g ξ i j| ≤ G) :
    Integrable (fun ξ ↦ fractionalAssignmentCost (c ξ) (W ξ) / n) P ∧
      (∫ ξ, fractionalAssignmentCost (c ξ) (W ξ) / n ∂P) ≤
        (∫ ξ, perturbedAssignmentValue (c ξ) 0 0 / n ∂P) + 2 * |τ| * G := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : Measurable (fun ξ ↦ fractionalAssignmentCost (c ξ) (W ξ) / n) := by
    apply Measurable.div_const
    unfold fractionalAssignmentCost
    exact Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _
      (fun j _ ↦ (hWm i j).mul (hc i j)))
  have hi : Integrable (fun ξ ↦ fractionalAssignmentCost (c ξ) (W ξ) / n) P := by
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    filter_upwards [hopt, hcn, hcb] with ξ ho hnon hbd
    have hnon' : 0 ≤ fractionalAssignmentCost (c ξ) (W ξ) :=
      Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦
        mul_nonneg (nonneg_of_mem_doublyStochastic ho.1) (hnon i j)))
    have hle := fractionalAssignmentCost_mono_of_feasible ho.1 hbd
    rw [fractionalAssignmentCost_const_of_feasible ho.1] at hle
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnon' hnR.le)]
    exact (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hle)
  have hci (i j : Fin n) : Integrable (fun ξ ↦ c ξ i j) P := by
    apply (integrable_const B).mono' (hc i j).aestronglyMeasurable
    filter_upwards [hcn, hcb] with ξ hnon hbd
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnon i j)] using hbd i j
  have hvi : Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) 0 0 / n) P :=
    (Probability.integrable_assignmentValue P c hc hci).div_const (n : ℝ)
  have hui : Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) 0 0 / n + 2 * |τ| * G) P :=
    hvi.add (integrable_const _)
  refine ⟨hi, ?_⟩
  have hle := integral_mono_ae hi hui (by
    filter_upwards [hopt, hgb] with ξ ho hg
    have h := div_le_div_of_nonneg_right
      (optimalFractional_base_energy_le_zero_pressure (c ξ) (g ξ) (W ξ) τ G ho hg) hnR.le
    have he : (2 * (n : ℝ) * |τ| * G) / n = 2 * |τ| * G := by field_simp
    simpa only [add_div, he] using h)
  simpa only [integral_add hvi (integrable_const _), integral_const, probReal_univ,
    one_smul] using hle

end OTSelector.Reconstruction
