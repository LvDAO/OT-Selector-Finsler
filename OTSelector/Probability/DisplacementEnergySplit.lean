import OTSelector.Probability.CavitySemidiscreteDisplacementEnergy
import Mathlib.Order.Filter.Finite

/-!
# Near/far splitting for semidiscrete displacement energy

A local quadratic lower bound for the base edge cost, valid on a ball of radius
`r`, a positive slack `δ` on the complementary far set, and a diameter bound `D`
together upgrade to a global quadratic lower bound with constant
`min q (δ / D ^ 2) / 2`.  Plugging this bound into
`semidiscrete_displacement_energy_le` controls the expected squared displacement
of every feasible semidiscrete allocation by its base allocation cost.

The argument is optimizer-free: no optimality, uniqueness or compactness of the
allocation is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {S V : Type*} [MeasurableSpace S] [NormedAddCommGroup V] {m : ℕ}

/-- A local quadratic lower bound, a uniform positive gap on the far set, and a
diameter bound give a global quadratic lower bound with an explicit constant. -/
theorem displacement_sq_le_slack_of_local
    (μ : Measure S) (c : S → Fin (m + 1) → ℝ) (coord : S → V)
    (Y : Fin (m + 1) → V) (q δ r D : ℝ)
    (hq : 0 < q) (hδ : 0 < δ) (hD : 0 < D)
    (hnear : ∀ j, ∀ᵐ s ∂μ, ‖Y j - coord s‖ ≤ r → q * ‖Y j - coord s‖ ^ 2 ≤ c s j)
    (hfar : ∀ j, ∀ᵐ s ∂μ, r ≤ ‖Y j - coord s‖ → δ ≤ c s j)
    (hdiam : ∀ j, ∀ᵐ s ∂μ, ‖Y j - coord s‖ ≤ D) :
    ∀ᵐ s ∂μ, ∀ j, (min q (δ / D ^ 2) / 2) * ‖Y j - coord s‖ ^ 2 ≤ c s j := by
  have hmin_pos : 0 < min q (δ / D ^ 2) :=
    lt_min hq (div_pos hδ (pow_pos hD 2))
  have hδD_pos : 0 < δ / D ^ 2 := div_pos hδ (pow_pos hD 2)
  have hDD : δ / D ^ 2 * D ^ 2 = δ := by
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hD))]
  filter_upwards [Filter.eventually_all.mpr hnear, Filter.eventually_all.mpr hfar,
    Filter.eventually_all.mpr hdiam] with s hn hf hd
  intro j
  by_cases hsmall : ‖Y j - coord s‖ ≤ r
  · have hle : min q (δ / D ^ 2) / 2 ≤ q := by
      have := min_le_left q (δ / D ^ 2)
      linarith
    exact (mul_le_mul_of_nonneg_right hle (sq_nonneg _)).trans (hn j hsmall)
  · have hlarge : r ≤ ‖Y j - coord s‖ := le_of_lt (lt_of_not_ge hsmall)
    have hsq : ‖Y j - coord s‖ ^ 2 ≤ D ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) (hd j)
    have hcoef : min q (δ / D ^ 2) / 2 ≤ δ / D ^ 2 := by
      have := min_le_right q (δ / D ^ 2)
      linarith
    have hmul : δ / D ^ 2 * ‖Y j - coord s‖ ^ 2 ≤ δ := by
      have := mul_le_mul_of_nonneg_left hsq (le_of_lt hδD_pos)
      rwa [hDD] at this
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
      (hmul.trans (hf j hlarge))

/-- The near/far quadratic bound upgrades the semidiscrete displacement energy
estimate to the explicit constant `min q (δ / D ^ 2) / 2`. -/
theorem semidiscrete_displacement_energy_le_of_local
    (μ : Measure S) [IsProbabilityMeasure μ]
    (coord : S → V) (Y : Fin (m + 1) → V)
    (c : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hd : ∀ j, Integrable (fun s ↦ ‖Y j - coord s‖ ^ 2) μ)
    (q δ r D : ℝ) (hq : 0 < q) (hδ : 0 < δ) (hD : 0 < D)
    (hnear : ∀ j, ∀ᵐ s ∂μ, ‖Y j - coord s‖ ≤ r → q * ‖Y j - coord s‖ ^ 2 ≤ c s j)
    (hfar : ∀ j, ∀ᵐ s ∂μ, r ≤ ‖Y j - coord s‖ → δ ≤ c s j)
    (hdiam : ∀ j, ∀ᵐ s ∂μ, ‖Y j - coord s‖ ≤ D) :
    Integrable (fun s ↦ ∑ j, a s j * ‖Y j - coord s‖ ^ 2) μ ∧
      (min q (δ / D ^ 2) / 2) *
          (∫ s, ∑ j, a s j * ‖Y j - coord s‖ ^ 2 ∂μ) ≤
        semidiscreteAllocationCost μ c a :=
  semidiscrete_displacement_energy_le μ coord Y c a ha hc hd
    (displacement_sq_le_slack_of_local μ c coord Y q δ r D hq hδ hD hnear hfar hdiam)

end OTSelector.Probability
