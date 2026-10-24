import OTSelector.Topology.MetricSpace.CanonicalMcShaneExtension
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.RoughMcShaneEverywhereLipschitz.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.RoughMcShaneEverywhereLipschitz`; the selected original proof blocks follow. -/
section

/-!
Conditions: A metric space, arbitrary node values and a nonnegative Lipschitz constant, with Lean’s actual real-infimum convention.

Objects: Everywhere Lipschitzness of the literal infimum-cone field, including environments where the family is unbounded below.

Proof detail: Transfer a lower bound between base points by the triangle inequality; in the unbounded-below case the totalized real infimum is identically zero.

Sources: Terence Tao, Section 1.10, Exercise 1.10.8, p. 139 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=148); Sheldon Axler, Section C, Definitions 0.32 and 0.35, pp. 18–19 (https://measure.axler.net/SupplementMIRA.pdf#page=18).
Relation: An explicit totalized-infimum extension of the McShane construction. Exact interpolation at nodes requires its separate compatibility hypotheses.
-/

/-!
# The literal McShane field is Lipschitz on every environment

If the real infimum is bounded below at one point, the Lipschitz distance terms imply
it is bounded below everywhere. If it is unbounded below, the literal real infimum is
zero everywhere. Thus the actual canonical field is Lipschitz even on ambient scenes
where the separate actual-node error estimate is unavailable.
-/

open Set Function
open scoped NNReal
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 800000

variable {I X : Type*} [Nonempty I] [PseudoMetricSpace X]

omit [Nonempty I] in
/-- A lower bound for the same actual McShane formula at one point transfers everywhere. -/
theorem roughMcShane_bddBelow_of_bddBelow_at
    (L : ℝ≥0) (z : I→X) (p : I→ℝ) {x₀ : X}
    (hb : BddBelow (range (fun i ↦ p i+L*dist x₀ (z i)))) (x : X) :
    BddBelow (range (fun i ↦ p i+L*dist x (z i))) := by
  obtain ⟨b,hb⟩ := hb
  refine ⟨b-L*dist x₀ x,?_⟩
  rintro y ⟨i,rfl⟩
  have hbi := hb (mem_range_self i)
  have htri := mul_le_mul_of_nonneg_left (dist_triangle x₀ x (z i)) L.coe_nonneg
  linarith

/-- The literal real-infimum canonical field is always Lipschitz, without any rough-node
or actual full-matching premise. Such premises are still needed for its node error bound. -/
theorem lipschitzWith_roughMcShane_everywhere
    (L : ℝ≥0) (z : I→X) (p : I→ℝ) : LipschitzWith L (roughMcShane L z p) := by
  by_cases hb : ∃x : X, BddBelow (range (fun i ↦ p i+L*dist x (z i)))
  · obtain ⟨x₀,hb⟩ := hb
    have hbound := roughMcShane_bddBelow_of_bddBelow_at L z p hb
    apply LipschitzWith.of_le_add_mul L
    intro x y
    rw [←sub_le_iff_le_add]
    apply le_ciInf
    intro i
    rw [sub_le_iff_le_add]
    calc
      roughMcShane L z p x ≤ p i+L*dist x (z i) := ciInf_le (hbound x) i
      _ ≤ p i+L*dist y (z i)+L*dist x y := by
        have htri := mul_le_mul_of_nonneg_left (dist_triangle x y (z i)) L.coe_nonneg
        linarith
  · have heq : roughMcShane L z p=fun _ ↦ 0 := by
      funext x
      exact Real.sInf_of_not_bddBelow (fun hx ↦ hb ⟨x,hx⟩)
    rw [heq]
    exact (LipschitzWith.const (0:ℝ)).weaken (bot_le : (0:ℝ≥0)≤L)

end OTSelector.Probability

end
end
