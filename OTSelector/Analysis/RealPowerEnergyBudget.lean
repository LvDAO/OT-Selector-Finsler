import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analysis.RealPowerEnergyBudget

Conditions: Nonnegative energy and size budgets, with the explicit small parameter constrained to [0,1].

Objects: Two root-power pairs are bounded by the stated common energy/size budget.

Proof detail: Compare powers on [0,1], use the energy bound and combine the two nonnegative terms.

## Mathematical sources

- [Stephen Boyd, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=85): Section 3.1.5, powers and geometric mean examples, pp. 71–73.

Source relation: Elementary real-power arithmetic corollaries; the numerical factors are locally proved.
-/

/-! The original focal and full-momentum budgets share one finite energy.
Their exact physical powers yield the sharp birth-level dyadic decay. -/
noncomputable section
namespace OTSelector.Probability

/-- A genuinely higher physical endpoint power in the full-momentum term can
be bounded by the focal term's power on the same original finite energy budget. -/
theorem sqrt_energy_power_pair_le
    {t σ A E V a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (_hσ : 0 ≤ σ) (hA : 0 ≤ A) (hb : 0 ≤ b) (hVE : V ≤ E) :
    A * Real.sqrt σ * (t ^ a * Real.sqrt E + t ^ (a + b) * Real.sqrt V) ≤
      2 * A * Real.sqrt E * t ^ a * Real.sqrt σ := by
  have htb : t ^ b ≤ 1 := Real.rpow_le_one ht.le ht1 hb
  have hV : Real.sqrt V ≤ Real.sqrt E := Real.sqrt_le_sqrt hVE
  have hi : t ^ a * Real.sqrt E + t ^ (a + b) * Real.sqrt V ≤
      2 * (t ^ a * Real.sqrt E) := by
    rw [Real.rpow_add ht]
    calc
      _ ≤ t ^ a * Real.sqrt E + (t ^ a * 1) * Real.sqrt E := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ A * Real.sqrt σ * (2 * (t ^ a * Real.sqrt E)) :=
      mul_le_mul_of_nonneg_left hi (mul_nonneg hA (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- The same true energy budget above one controls both fourth-root moments,
while retaining the actual endpoint-time decay before interpolation. -/
theorem fourthRoot_energy_power_pair_le
    {t A E V a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hV0 : 0 ≤ V) (hVE : V ≤ E) (hE1 : 1 ≤ E) :
    A * (t ^ a * E ^ (1 / 4 : ℝ) + t ^ (a + b) * V ^ (1 / 4 : ℝ)) ≤
      2 * A * Real.sqrt E * t ^ a := by
  have htb : t ^ b ≤ 1 := Real.rpow_le_one ht.le ht1 hb
  have hEV : V ^ (1 / 4 : ℝ) ≤ E ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hV0 hVE (by norm_num)
  have hroot : E ^ (1 / 4 : ℝ) ≤ Real.sqrt E := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have hV : V ^ (1 / 4 : ℝ) ≤ Real.sqrt E := hEV.trans hroot
  have hi : t ^ a * E ^ (1 / 4 : ℝ) + t ^ (a + b) * V ^ (1 / 4 : ℝ) ≤
      2 * (t ^ a * Real.sqrt E) := by
    rw [Real.rpow_add ht]
    calc
      _ ≤ t ^ a * Real.sqrt E + (t ^ a * 1) * Real.sqrt E := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ A * (2 * (t ^ a * Real.sqrt E)) := mul_le_mul_of_nonneg_left hi hA
    _ = _ := by ring

end OTSelector.Probability
