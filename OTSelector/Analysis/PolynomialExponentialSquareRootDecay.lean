import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
## Lemma skeleton

* **Conditions:** Nonnegative prefactor and radius; a natural polynomial degree.
* **Objects:** A square-root fourth-moment polynomial times exp(-n/2).
* **Proof detail:** Bound the square root by a polynomial; use exponential domination of powers, then squeeze.

## Mathematical sources

* Terence Tao, *Analysis I*, Section 7.5, Corollary 7.5.3 (ratio test).
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_5.lean
* Terence Tao, *Analysis I*, Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).
  https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean

**Relationship to the sources:** The exact prefactor is a proved algebraic corollary; ratio-test decay is the classical method, while Lean uses its real-asymptotic equivalent.
-/

/-! # The actual polynomial fourth-moment prefactor is killed by exponential probability -/
open Filter Topology
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The square-root fourth-moment factor of a polynomially growing actual
envelope still vanishes against the square-root exponential bad probability. -/
theorem tendsto_polynomialFourthRoot_exp_neg_half_nat
    (q : ℕ) {C v r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ ↦
      (C * (1 + ((2 * (n : ℝ) + r) ^ q * v) ^ 4)) ^ (1 / 2 : ℝ) *
        Real.exp (-(n : ℝ) / 2)) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun n ↦ 2 * (n : ℝ) + r
  have hR (n : ℕ) : 0 ≤ R n := by dsimp [R]; positivity
  have hlarge : Tendsto R atTop atTop := tendsto_atTop_add_const_right atTop r
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun n ↦ Real.exp (-(1 / 4 : ℝ) * R n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_zero, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0
      (1 / 4) (by norm_num)).comp hlarge
  have hp : Tendsto (fun n ↦ R n ^ (2 * q) * Real.exp (-(1 / 4 : ℝ) * R n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * q : ℕ)
        (1 / 4) (by norm_num)).comp hlarge
  let b : ℕ → ℝ := fun n ↦ Real.sqrt C * Real.exp (r / 4) *
    (Real.exp (-(1 / 4 : ℝ) * R n) +
      v ^ 2 * (R n ^ (2 * q) * Real.exp (-(1 / 4 : ℝ) * R n)))
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (he.add (hp.const_mul (v ^ 2))).const_mul (Real.sqrt C * Real.exp (r / 4))
  apply squeeze_zero
    (fun n ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)) ?_ hb
  intro n
  let x := R n ^ q * v
  have hs : Real.sqrt (C * (1 + x ^ 4)) ≤ Real.sqrt C * (1 + x ^ 2) := by
    rw [Real.sqrt_mul hC]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg x]
  have hexp : Real.exp (-(n : ℝ) / 2) =
      Real.exp (r / 4) * Real.exp (-(1 / 4 : ℝ) * R n) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [R]
    ring
  have hx : x ^ 2 = R n ^ (2 * q) * v ^ 2 := by
    dsimp only [x]
    rw [mul_pow, ← pow_mul, Nat.mul_comm q 2]
  change (C * (1 + x ^ 4)) ^ (1 / 2 : ℝ) * Real.exp (-(n : ℝ) / 2) ≤ b n
  rw [← Real.sqrt_eq_rpow]
  calc
    _ ≤ (Real.sqrt C * (1 + x ^ 2)) * Real.exp (-(n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)
    _ = b n := by rw [hexp, hx]; dsimp only [b]; ring

end OTSelector.Probability
