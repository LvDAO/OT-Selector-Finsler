import OTSelector.Reconstruction.TaggedDyadicPressureRecovery

/-!
# Uniform expected upper pressure from the original typed competitor

The genuine count-completion remainder is uniformly bounded in dimension q > 4.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false in
/-- A sample-size independent bound for the original normalized assignment
value, suitable for global pressure and localization consumers. -/
theorem expected_assignmentValue_le_taggedHierarchy_uniform
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j)) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hquadratic : ∀ t, ∀ᵐ ξ ∂P, ∀ i j, (xs i ξ).1 = t → (ys j ξ).1 = t →
      cost ξ i j ≤ C * ‖dyadicCubePoint (xs i ξ).2 - dyadicCubePoint (ys j ξ).2‖ ^ 2) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (cost ξ) 0 0) P ∧
    ((n : ℝ) ^ (2 / (q : ℝ)) / n) * (∫ ξ, perturbedAssignmentValue (cost ξ) 0 0 ∂P) ≤
      C * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) +
      B * Real.sqrt (2 * Fintype.card T) := by
  have h := expected_assignmentValue_le_taggedHierarchy_rate hq hn P μ xs ys hx hy
    hxi hyi hxl hyl hxy cost hc hC hB hcn hbound hquadratic
  refine ⟨h.1, h.2.trans ?_⟩
  apply add_le_add le_rfl
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (highDimensional_count_power_le_one hq hn) (mul_nonneg hB (Real.sqrt_nonneg _))

end OTSelector.Reconstruction
