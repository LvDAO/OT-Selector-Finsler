import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Sqrt

/-!
# Analysis.FiniteEnergyPowers

Conditions: A finite nonnegative energy family whose total is bounded by E.

Objects: Square-root and fourth-root sums bounded by powers of the cardinality and E.

Proof detail: Apply finite Hölder/Cauchy–Schwarz to the counting measure, then use monotonicity of roots.

## Mathematical sources

- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.3 (Hölder), p. 29.
- [Stephen Boyd, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=85): Section 3.1.5, powers and geometric mean examples, pp. 71–73.

Source relation: Counting-measure Hölder specialization; zero-cardinality and zero-energy conventions are handled explicitly.
-/

/-! The original disjoint-band energy budget controls the sums of square roots
and fourth roots used by the actual birth-traffic estimates. -/
open scoped BigOperators
noncomputable section
namespace OTSelector.Probability

/-- Cauchy-Schwarz over the actual finite source bands retains their total
original energy, without replacing each band by a separate full-energy bound. -/
theorem sum_sqrt_energy_le_card_sqrt_mul
    {ι : Type*} (s : Finset ι) (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    {E : ℝ} (hbudget : (∑ i ∈ s, e i) ≤ E) :
    (∑ i ∈ s, Real.sqrt (e i)) ≤ Real.sqrt (s.card : ℝ) * Real.sqrt E := by
  have h := Real.sum_sqrt_mul_sqrt_le s (f := fun _ ↦ (1 : ℝ)) (g := e)
    (fun _ ↦ zero_le_one) he
  simp only [Real.sqrt_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbudget) (Real.sqrt_nonneg _))

/-- The fourth-root band sum spends only the `N^(3/4)` Hölder factor and the
fourth root of the same total original energy. -/
theorem sum_fourthRoot_energy_le_card_rpow_mul
    {ι : Type*} (s : Finset ι) (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    {E : ℝ} (hbudget : (∑ i ∈ s, e i) ≤ E) :
    (∑ i ∈ s, (e i) ^ (1 / 4 : ℝ)) ≤
      (s.card : ℝ) ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) := by
  have hpow (i : ι) : ((e i) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = e i := by
    rw [← Real.rpow_mul (he i)]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (f := fun _ ↦ (1 : ℝ)) (g := fun i ↦ (e i) ^ (1 / 4 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      Real.HolderConjugate (4 / 3 : ℝ) 4)
    (fun _ _ ↦ zero_le_one) (fun i _ ↦ Real.rpow_nonneg (he i) _)
  simp only [one_mul, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one, hpow] at h
  norm_num only [show (1 : ℝ) / (4 / 3) = 3 / 4 by norm_num] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ ↦ he i)) hbudget (by norm_num))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end OTSelector.Probability
