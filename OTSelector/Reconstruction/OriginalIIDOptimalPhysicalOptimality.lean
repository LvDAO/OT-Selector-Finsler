import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Finite.EmpiricalFractional

/-! The measurable original finite plan is a genuine optimal coupling, and
positive distance-slack normalization preserves that same selected plan. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass X] [MeasurableSingletonClass Y] {n : ℕ}

/-- The actual deterministic plan minimizes among every empirical coupling,
including fractional couplings and repeated observations. -/
theorem isOptimalCoupling_originalIIDOptimalPhysicalPlan [NeZero n]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (hcost0 : ∀ x y, 0 ≤ cost x y) {scale : ℝ} (hscale : 0 ≤ scale)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    IsOptimalCoupling (fun x y ↦ ENNReal.ofReal (scale * cost x y))
      (empiricalMeasure ξ.1) (empiricalMeasure ξ.2)
      (originalIIDOptimalPhysicalPlan cost scale ξ) := by
  refine ⟨⟨originalIIDOptimalPhysicalPlan_source cost scale ξ,
    originalIIDOptimalPhysicalPlan_target cost scale ξ⟩, ?_⟩
  intro Γ hΓ
  obtain ⟨W, hW, rfl⟩ := (isCoupling_empirical_iff_exists_doublyStochastic ξ.1 ξ.2 Γ).mp hΓ
  rw [couplingCost_fractionalEmpiricalMeasure ξ.1 ξ.2 W hW
    (fun x y ↦ scale * cost x y) (fun x y ↦ mul_nonneg hscale (hcost0 x y))]
  change (∫⁻ p, ENNReal.ofReal (scale * cost p.1 p.2)
    ∂originalIIDOptimalPhysicalPlan cost scale ξ) ≤ _
  rw [lintegral_originalIIDOptimalPhysicalPlan_cost cost hcost hcost0 hscale ξ]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  simpa only [perturbedEdgeCost_zero] using perturbedAssignmentValue_le_fractional
    (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) 0 W 0 hW

variable {M : Type*} [MeasurableSpace M] [PseudoMetricSpace M]

/-- Positive microscopic scaling and the potential subtraction retain the
same deterministic distance optimizer on every full original sample. -/
theorem originalIIDOptimalPhysicalPlan_distanceSlack_eq
    (u : M → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (ξ : (Fin n → M) × (Fin n → M)) :
    originalIIDOptimalPhysicalPlan (fun x y ↦ dist x y - u y + u x) scale ξ =
      originalIIDOptimalPhysicalPlan dist 1 ξ := by
  have heq : (fun i j ↦ scale * (dist (ξ.1 i) (ξ.2 j) - u (ξ.2 j) + u (ξ.1 i))) =
      (fun i j ↦ scale * dist (ξ.1 i) (ξ.2 j) + scale * u (ξ.1 i) +
        (-scale * u (ξ.2 j))) := by funext i j; ring
  unfold originalIIDOptimalPhysicalPlan
  rw [heq, firstOptimalAssignment_posScale_add_rowColumn _ scale hscale]
  simp only [one_mul]

/-- With a measurable distance, the actual slack-selected finite plan is a
genuine original distance-cost optimum, for an arbitrary potential. -/
theorem isOptimalCoupling_originalIIDOptimalPhysicalPlan_distanceSlack
    [MeasurableSingletonClass M] [NeZero n]
    (hmetric : Measurable (fun p : M × M ↦ dist p.1 p.2))
    (u : M → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (ξ : (Fin n → M) × (Fin n → M)) :
    IsOptimalCoupling edist (empiricalMeasure ξ.1) (empiricalMeasure ξ.2)
      (originalIIDOptimalPhysicalPlan (fun x y ↦ dist x y - u y + u x) scale ξ) := by
  rw [originalIIDOptimalPhysicalPlan_distanceSlack_eq u hscale ξ]
  have hm : Measurable (Function.uncurry (dist : M → M → ℝ)) := hmetric
  have h := isOptimalCoupling_originalIIDOptimalPhysicalPlan dist hm
    (fun _ _ ↦ dist_nonneg) (show (0 : ℝ) ≤ 1 by norm_num) ξ
  simpa only [one_mul, ← edist_dist] using h

end OTSelector.Reconstruction
