import OTSelector.Transport.CompactCalibrationSlack
import OTSelector.Finite.FractionalGauge

/-! # Distance slack controls distant edges of finite empirical plans -/

open scoped BigOperators
namespace OTSelector.Geometry

/-- The distant mass of any nonnegative finite plan is bounded by its original
empirical distance slack divided by the geometric gap. -/
theorem fractional_far_mass_le_distance_slack_cost
    {M : Type*} [PseudoMetricSpace M] {n : ℕ}
    (X Y : Fin n → M) (u : M → ℝ) (hu : LipschitzWith 1 u)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (far : Fin n → Fin n → Prop) [DecidablePred (fun p : Fin n × Fin n ↦ far p.1 p.2)]
    {gap : ℝ} (hgap : 0 < gap)
    (hbound : ∀ i j, far i j → gap ≤ distanceSlackEdgeCost X Y u i j) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n ↦ far p.1 p.2), P p.1 p.2) /
      (n : ℝ) ≤ (fractionalAssignmentCost (distanceSlackEdgeCost X Y u) P / n) / gap := by
  have h := distant_edge_weight_le_cost_div_gap Finset.univ
    (fun p : Fin n × Fin n ↦ far p.1 p.2) (fun p ↦ P p.1 p.2)
    (fun p ↦ distanceSlackEdgeCost X Y u p.1 p.2)
    (fun p _ ↦ hP p.1 p.2)
    (fun p _ ↦ distanceSlackEdgeCost_nonneg X Y u hu p.1 p.2)
    hgap (fun p _ ↦ hbound p.1 p.2)
  have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [Fintype.sum_prod_type, fractionalAssignmentCost, div_right_comm
    (∑ i, ∑ j, P i j * distanceSlackEdgeCost X Y u i j) gap (n : ℝ)] using hh

/-- A bound on the scaled empirical distance slack gives the exact inverse-scale
bound on the mass of distant edges. -/
theorem fractional_far_mass_le_of_scaled_distance_slack_cost
    {M : Type*} [PseudoMetricSpace M] {n : ℕ}
    (X Y : Fin n → M) (u : M → ℝ) (hu : LipschitzWith 1 u)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (far : Fin n → Fin n → Prop) [DecidablePred (fun p : Fin n × Fin n ↦ far p.1 p.2)]
    {gap scale budget : ℝ} (hgap : 0 < gap) (hscale : 0 < scale)
    (hbound : ∀ i j, far i j → gap ≤ distanceSlackEdgeCost X Y u i j)
    (hbudget : scale * (fractionalAssignmentCost (distanceSlackEdgeCost X Y u) P / n) ≤ budget) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n ↦ far p.1 p.2), P p.1 p.2) /
      (n : ℝ) ≤ budget / (scale * gap) := by
  have hb : fractionalAssignmentCost (distanceSlackEdgeCost X Y u) P / n ≤ budget / scale :=
    (le_div_iff₀ hscale).mpr (by simpa only [mul_comm scale] using hbudget)
  calc
    _ ≤ (fractionalAssignmentCost (distanceSlackEdgeCost X Y u) P / n) / gap :=
      fractional_far_mass_le_distance_slack_cost X Y u hu P hP far hgap hbound
    _ ≤ (budget / scale) / gap := div_le_div_of_nonneg_right hb hgap.le
    _ = budget / (scale * gap) := div_div _ _ _

end OTSelector.Geometry
