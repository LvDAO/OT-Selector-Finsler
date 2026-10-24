import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-! A small relative-density error preserves a signed finite-reference pressure bound. -/

open Filter
open scoped Topology

namespace OTSelector.Reconstruction

/-- The explicit density-error expression is continuous at zero, with value `P`.
The pressure, mass and lower-bound constant may be arbitrary real numbers. -/
theorem reference_density_pressure_error_continuousAt (P mass C : ℝ) :
    ContinuousAt (fun δ : ℝ ↦
      (P + (C + δ + δ) * mass) / (1 - δ) - C * mass / (1 + δ)) 0 := by
  apply ContinuousAt.sub
  · exact (continuousAt_const.add
      (((continuousAt_const.add continuousAt_id).add continuousAt_id).mul
        continuousAt_const)).div (continuousAt_const.sub continuousAt_id) (by norm_num)
  · exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)

/-- A positive density tolerance below any prescribed cap makes the signed pressure
error smaller than any prescribed positive accuracy. No bound on `P` is needed. -/
theorem exists_reference_density_pressure_error_lt
    (P mass C : ℝ) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      (P + (C + δ + δ) * mass) / (1 - δ) - C * mass / (1 + δ) < P + ε := by
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0,
      (P + (C + δ + δ) * mass) / (1 - δ) - C * mass / (1 + δ) < P + ε :=
    (reference_density_pressure_error_continuousAt P mass C).eventually_lt
      continuousAt_const (by simpa using hε)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ := min (min r cap) 1 / 2
  have hmin : 0 < min (min r cap) 1 := lt_min (lt_min hr hcap) zero_lt_one
  have hδ : 0 < δ := half_pos hmin
  have hδr : δ < r := by
    have := min_le_left r cap
    have := min_le_left (min r cap) 1
    dsimp only [δ]
    linarith
  have hδcap : δ < cap := by
    have := min_le_right r cap
    have := min_le_left (min r cap) 1
    dsimp only [δ]
    linarith
  have hδ1 : δ < 1 := by
    have := min_le_right (min r cap) 1
    dsimp only [δ]
    linarith
  refine ⟨δ, hδ, hδ1, hδcap, hball ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδr

/-- The same internally chosen density tolerance controls separate model and root
oscillation tolerances bounded by it. Only the original mass must be nonnegative. -/
theorem exists_reference_density_pressure_accuracy
    (P mass C : ℝ) (hmass : 0 ≤ mass) {ε cap : ℝ} (hε : 0 < ε)
    (hcap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      ∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        (P + (C + modelTolerance + oscillation) * mass) / (1 - δ) -
          C * mass / (1 + δ) < P + ε := by
  obtain ⟨δ, hδ, hδ1, hδcap, haccuracy⟩ :=
    exists_reference_density_pressure_error_lt P mass C hε hcap
  refine ⟨δ, hδ, hδ1, hδcap, ?_⟩
  intro modelTolerance oscillation _ hmodel _ hosc
  apply lt_of_le_of_lt (sub_le_sub_right ?_ _) haccuracy
  apply div_le_div_of_nonneg_right ?_ (sub_pos.mpr hδ1).le
  have hadd : C + modelTolerance + oscillation ≤ C + δ + δ := by linarith
  exact add_le_add (le_refl P) (mul_le_mul_of_nonneg_right hadd hmass)

end OTSelector.Reconstruction
