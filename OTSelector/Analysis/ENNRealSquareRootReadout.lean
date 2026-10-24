import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Analysis.ENNRealSquareRootReadout

Conditions: Nonnegative extended-real quantities satisfy the stated energy upper bound by finite real parameters.

Objects: Finiteness and an exact real square-root readout bound.

Proof detail: Bound the ENNReal quantity by a finite expression, transport the inequality through toReal, and simplify the ofReal square root.

## Mathematical sources

- [Stephen Boyd, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=85): Section 3.1.5, powers and geometric mean examples, pp. 71–73.

Source relation: Lean extended-real encoding adapter for an elementary finite root inequality.
-/

/-! A genuine nonnegative first-moment energy bound gives both finiteness and
its real-valued square-root readout, without truncating an infinite quantity. -/
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Finite original energies make a bounded occupation moment finite before its
real readout is compared with the same energies. -/
theorem firstMoment_energy_toReal_bound
    {U E V : ℝ≥0∞} (hE : E ≠ ∞) (hV : V ≠ ∞) {C a b : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : U ≤ ENNReal.ofReal C *
      (ENNReal.ofReal a * E ^ (1 / 2 : ℝ) + ENNReal.ofReal b * V ^ (1 / 2 : ℝ))) :
    U ≠ ∞ ∧ U.toReal ≤ C * (a * Real.sqrt E.toReal + b * Real.sqrt V.toReal) := by
  have hEr := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hE
  have hVr := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hV
  have hAE := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := a)) hEr
  have hBV := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := b)) hVr
  have hsum := ENNReal.add_ne_top.mpr ⟨hAE, hBV⟩
  have hfin := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C)) hsum
  refine ⟨ne_top_of_le_ne_top hfin hbound, ?_⟩
  have hreal := ENNReal.toReal_mono hfin hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_add hAE hBV,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hreal
  simpa only [← Real.sqrt_eq_rpow] using hreal

end OTSelector.Probability
