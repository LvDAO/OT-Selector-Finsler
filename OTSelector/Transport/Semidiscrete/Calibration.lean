import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Probability.Independence.Integration
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteCalibration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteCalibration`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite semidiscrete allocations have nonnegative weights, pointwise unit sum and the indicated prescribed marginal masses; costs are integrable and calibration is explicit.

Objects: Price-shift invariance, optimality of calibrated allocations and uniqueness under strict calibration.

Proof detail: Add the same prices to competitors using their common masses, compare each weighted cost to its minimum and use strictness to force a single active target when total costs agree.

Sources: Gabriel Peyré, Section 5.2, equations (5.6)–(5.8), pp. 94–96 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=98); Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31).
Relation: Elementary semidiscrete dual calibration and equality-case argument, with the actual allocation definition included.
-/

/-!
# Semidiscrete calibration of the actual cavity allocation

A fractional allocation specifies nonnegative source-to-label weights summing to one,
with prescribed integrated label masses. Integrable costs give a finite objective.
The actual cavity cell indicators minimize this objective for their own masses, and
null score ties force every optimum to coincide with those indicators almost everywhere.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Fractional allocations with source law `μ` and the specified target-label masses. -/
structure IsSemidiscreteAllocation (μ : Measure S) (p : Fin (m + 1) → ℝ)
    (a : S → Fin (m + 1) → ℝ) : Prop where
  integrable : ∀ j, Integrable (fun s ↦ a s j) μ
  nonneg : ∀ᵐ s ∂μ, ∀ j, 0 ≤ a s j
  sum_one : ∀ᵐ s ∂μ, ∑ j, a s j = 1
  mass : ∀ j, ∫ s, a s j ∂μ = p j

/-- The cost of an allocation against the original source law. -/
def semidiscreteAllocationCost (μ : Measure S) (c a : S → Fin (m + 1) → ℝ) : ℝ :=
  ∫ s, ∑ j, a s j * c s j ∂μ

/-- Every feasible coefficient lies in the unit interval almost everywhere. -/
theorem IsSemidiscreteAllocation.ae_le_one {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a) :
    ∀ᵐ s ∂μ, ∀ j, a s j ≤ 1 := by
  filter_upwards [ha.nonneg, ha.sum_one] with s hn hs
  intro j
  rw [← hs]
  exact Finset.single_le_sum (fun k _ ↦ hn k) (Finset.mem_univ j)

/-- Integrable original costs remain integrable against any feasible allocation. -/
theorem IsSemidiscreteAllocation.integrable_mul {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (j : Fin (m + 1)) : Integrable (fun s ↦ a s j * c s j) μ := by
  apply (hc j).bdd_mul (ha.integrable j).aestronglyMeasurable
  filter_upwards [ha.nonneg, ha.ae_le_one] with s hn hu
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hn j)] using hu j

/-- Adding target prices changes every feasible objective by the same mass-weighted sum. -/
theorem IsSemidiscreteAllocation.cost_add_prices {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (β : Fin (m + 1) → ℝ) :
    semidiscreteAllocationCost μ (fun s j ↦ c s j + β j) a =
      semidiscreteAllocationCost μ c a + ∑ j, p j * β j := by
  have hi j := ha.integrable_mul c hc j
  have hp j := (ha.integrable j).mul_const (β j)
  unfold semidiscreteAllocationCost
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [integral_add (integrable_finsetSum _ (fun j _ ↦ hi j))
    (integrable_finsetSum _ (fun j _ ↦ hp j)), integral_finsetSum _ (fun j _ ↦ hp j)]
  simp_rw [integral_mul_const, ha.mass]

private theorem min_le_weighted_sum (b score : Fin (m + 1) → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hs : ∑ j, b j = 1) (k : Fin (m + 1))
    (hk : ∀ j, score k ≤ score j) : score k ≤ ∑ j, b j * score j := by
  calc
    score k = ∑ j, b j * score k := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hk j) (hb j)

private theorem eq_single_of_weighted_sum_eq_min (b score : Fin (m + 1) → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hs : ∑ j, b j = 1) (k : Fin (m + 1))
    (hk : ∀ j, j ≠ k → score k < score j)
    (heq : ∑ j, b j * score j = score k) : ∀ j, b j = if j = k then 1 else 0 := by
  classical
  have hnonneg j : 0 ≤ b j * (score j - score k) := by
    apply mul_nonneg (hb j)
    by_cases hj : j = k
    · simp [hj]
    · exact sub_nonneg.mpr (hk j hj).le
  have hz : ∑ j, b j * (score j - score k) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hs, one_mul, heq, sub_self]
  have hzj j : b j * (score j - score k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnonneg j)).mp hz j (Finset.mem_univ j)
  have hoff j (hj : j ≠ k) : b j = 0 :=
    (mul_eq_zero.mp (hzj j)).resolve_right (ne_of_gt (sub_pos.mpr (hk j hj)))
  have hon : b k = 1 := by
    rw [Finset.sum_eq_single k (fun j _ hj ↦ hoff j hj) (by simp)] at hs
    exact hs
  intro j
  split_ifs with hj
  · simpa only [hj] using hon
  · exact hoff j hj

/-- A measurable allocation calibrated by one source potential and target prices
minimizes the exact semidiscrete objective. -/
theorem semidiscreteAllocationCost_le_of_calibrated
    (μ : Measure S) [IsFiniteMeasure μ]
    (p : Fin (m + 1) → ℝ) (c a b : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) (hb : IsSemidiscreteAllocation μ p b)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) (β : Fin (m + 1) → ℝ)
    (hcal : ∀ᵐ s ∂μ, ∃ k, (∀ j, c s k + β k ≤ c s j + β j) ∧
      ∀ j, a s j = if j = k then 1 else 0) :
    semidiscreteAllocationCost μ c a ≤ semidiscreteAllocationCost μ c b := by
  classical
  have hshift j : Integrable (fun s ↦ c s j + β j) μ := (hc j).add (integrable_const _)
  have hle : (fun s ↦ ∑ j, a s j * (c s j + β j)) ≤ᵐ[μ]
      fun s ↦ ∑ j, b s j * (c s j + β j) := by
    filter_upwards [hcal, hb.nonneg, hb.sum_one] with s hs hn ht
    obtain ⟨k, hk, ha⟩ := hs
    simp_rw [ha]
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
      min_le_weighted_sum (b s) (fun j ↦ c s j + β j) hn ht k hk
  have hint := integral_mono_ae
    (integrable_finsetSum _ (fun j _ ↦ ha.integrable_mul _ hshift j))
    (integrable_finsetSum _ (fun j _ ↦ hb.integrable_mul _ hshift j)) hle
  change semidiscreteAllocationCost μ (fun s j ↦ c s j + β j) a ≤
    semidiscreteAllocationCost μ (fun s j ↦ c s j + β j) b at hint
  rw [ha.cost_add_prices c hc β, hb.cost_add_prices c hc β] at hint
  exact (add_le_add_iff_right _).mp hint

/-- Strict calibration identifies the entire optimal allocation face almost everywhere. -/
theorem semidiscreteAllocation_eq_of_cost_eq_of_strictly_calibrated
    (μ : Measure S) [IsFiniteMeasure μ]
    (p : Fin (m + 1) → ℝ) (c a b : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) (hb : IsSemidiscreteAllocation μ p b)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) (β : Fin (m + 1) → ℝ)
    (hcal : ∀ᵐ s ∂μ, ∃ k, (∀ j, j ≠ k → c s k + β k < c s j + β j) ∧
      ∀ j, a s j = if j = k then 1 else 0)
    (heq : semidiscreteAllocationCost μ c a = semidiscreteAllocationCost μ c b) :
    a =ᵐ[μ] b := by
  classical
  have hshift j : Integrable (fun s ↦ c s j + β j) μ := (hc j).add (integrable_const _)
  have hle : (fun s ↦ ∑ j, a s j * (c s j + β j)) ≤ᵐ[μ]
      fun s ↦ ∑ j, b s j * (c s j + β j) := by
    filter_upwards [hcal, hb.nonneg, hb.sum_one] with s hs hn ht
    obtain ⟨k, hk, ha⟩ := hs
    simp_rw [ha]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply min_le_weighted_sum (b s) (fun j ↦ c s j + β j) hn ht k
    intro j
    by_cases hj : j = k
    · simp [hj]
    · exact (hk j hj).le
  have hint : (∫ s, ∑ j, a s j * (c s j + β j) ∂μ) =
      ∫ s, ∑ j, b s j * (c s j + β j) ∂μ := by
    change semidiscreteAllocationCost μ (fun s j ↦ c s j + β j) a =
      semidiscreteAllocationCost μ (fun s j ↦ c s j + β j) b
    rw [ha.cost_add_prices c hc β, hb.cost_add_prices c hc β, heq]
  have hae := (integral_eq_iff_of_ae_le
    (integrable_finsetSum _ (fun j _ ↦ ha.integrable_mul _ hshift j))
    (integrable_finsetSum _ (fun j _ ↦ hb.integrable_mul _ hshift j)) hle).mp hint
  filter_upwards [hcal, hb.nonneg, hb.sum_one, hae] with s hs hn ht he
  obtain ⟨k, hk, ha⟩ := hs
  have he' : ∑ j, b s j * (c s j + β j) = c s k + β k := by
    rw [← he]
    simp [ha]
  funext j
  rw [ha, eq_single_of_weighted_sum_eq_min (b s) (fun j ↦ c s j + β j) hn ht k hk he']

end OTSelector.Probability

end
end
