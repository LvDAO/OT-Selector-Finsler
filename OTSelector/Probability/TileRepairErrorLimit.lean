import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Vanishing of the normalized tile-repair error

After division by the ambient intensity `R ^ q`, the discrepancy repair of the
finite-tile comparison contributes

`((R ^ (2/q) * A + |t| G) / R ^ q) * (sqrt (2 R ^ q n) / 2)`,

which is eventually equal to

`A (sqrt (2 n) / 2) R ^ (2/q - q/2) + |t| G (sqrt (2 n) / 2) R ^ (-q/2)`.

Both exponents are negative for `q > 2`, so the expression vanishes at
infinity.  The selector application uses `q > 4`.
-/

open Filter
open scoped Topology

noncomputable section
namespace OTSelector.Probability

/-- The normalized tile-repair error vanishes for `q > 2`. -/
theorem tendsto_tileRepairError_zero {q : ℕ} (hq : 2 < q) (A G t n : ℝ) (hn : 0 ≤ n) :
    Tendsto (fun R : ℝ =>
      ((R ^ (2 / (q : ℝ)) * A + |t| * G) / R ^ q) *
        (Real.sqrt (2 * R ^ q * n) / 2)) atTop (𝓝 0) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hq2 : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have ha : 2 / (q : ℝ) - (q : ℝ) / 2 < 0 := by
    have hlt : 2 / (q : ℝ) < (q : ℝ) / 2 := by
      rw [div_lt_iff₀ hq0]
      nlinarith
    linarith
  have hb : (0 : ℝ) < (q : ℝ) / 2 := by positivity
  have h1 : Tendsto (fun R : ℝ => R ^ (2 / (q : ℝ) - (q : ℝ) / 2)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := -(2 / (q : ℝ) - (q : ℝ) / 2)) (by linarith)
    simpa only [neg_neg] using h
  have h2 : Tendsto (fun R : ℝ => R ^ (-((q : ℝ) / 2))) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := (q : ℝ) / 2) hb
    simpa only [] using h
  have hlim : Tendsto (fun R : ℝ =>
      A * (Real.sqrt (2 * n) / 2) * R ^ (2 / (q : ℝ) - (q : ℝ) / 2) +
        |t| * G * (Real.sqrt (2 * n) / 2) * R ^ (-((q : ℝ) / 2)))
      atTop (𝓝 0) := by
    have h := (h1.const_mul (A * (Real.sqrt (2 * n) / 2))).add
      (h2.const_mul (|t| * G * (Real.sqrt (2 * n) / 2)))
    simpa only [mul_zero, add_zero] using h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  -- The square root factor.
  have hsqrt : Real.sqrt (2 * R ^ q * n) = Real.sqrt (2 * n) * R ^ ((q : ℝ) / 2) := by
    rw [show (2 * R ^ q * n : ℝ) = (2 * n) * R ^ (q : ℝ) by
      rw [Real.rpow_natCast]; ring]
    rw [Real.sqrt_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [hsqrt]
  -- Replace the natural power by the real power.
  rw [show (R : ℝ) ^ q = R ^ (q : ℝ) from (Real.rpow_natCast R q).symm]
  -- Split the quotient.
  have hsplit : (R ^ (2 / (q : ℝ)) * A + |t| * G) / R ^ (q : ℝ) =
      A * R ^ (2 / (q : ℝ) - (q : ℝ)) + |t| * G * R ^ (-(q : ℝ)) := by
    rw [add_div]
    have hA : R ^ (2 / (q : ℝ)) * A / R ^ (q : ℝ) =
        A * R ^ (2 / (q : ℝ) - (q : ℝ)) := by
      rw [show R ^ (2 / (q : ℝ)) * A / R ^ (q : ℝ) =
        (R ^ (2 / (q : ℝ)) / R ^ (q : ℝ)) * A by ring]
      rw [← Real.rpow_sub hR]
      ring
    have hB : |t| * G / R ^ (q : ℝ) = |t| * G * R ^ (-(q : ℝ)) := by
      rw [Real.rpow_neg hR.le]
      ring
    rw [hA, hB]
  rw [hsplit]
  -- Recombine the exponents.
  exact (calc (A * R ^ (2 / (q : ℝ) - (q : ℝ)) + |t| * G * R ^ (-(q : ℝ))) *
        (Real.sqrt (2 * n) * R ^ ((q : ℝ) / 2) / 2)
      = A * (Real.sqrt (2 * n) / 2) * (R ^ (2 / (q : ℝ) - (q : ℝ)) * R ^ ((q : ℝ) / 2)) +
          |t| * G * (Real.sqrt (2 * n) / 2) *
            (R ^ (-(q : ℝ)) * R ^ ((q : ℝ) / 2)) := by ring
    _ = A * (Real.sqrt (2 * n) / 2) * R ^ (2 / (q : ℝ) - (q : ℝ) / 2) +
          |t| * G * (Real.sqrt (2 * n) / 2) * R ^ (-((q : ℝ) / 2)) := by
        rw [← Real.rpow_add hR, ← Real.rpow_add hR]
        congr 2 <;> ring).symm


/-- The normalized tile-repair error with kinetic coefficient `R ^ 2` (the value
of `(R ^ q) ^ (2/q)`) vanishes for `q > 4`. -/
theorem tendsto_tileRepairError_scale_zero {q : ℕ} (hq : 4 < q)
    (A G t n : ℝ) (hn : 0 ≤ n) :
    Tendsto (fun R : ℝ =>
      ((R ^ 2 * A + |t| * G) / R ^ q) *
        (Real.sqrt (2 * R ^ q * n) / 2)) atTop (𝓝 0) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hq4 : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have ha : (2 : ℝ) - (q : ℝ) / 2 < 0 := by linarith
  have hb : (0 : ℝ) < (q : ℝ) / 2 := by positivity
  have h1 : Tendsto (fun R : ℝ => R ^ ((2 : ℝ) - (q : ℝ) / 2)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := -((2 : ℝ) - (q : ℝ) / 2)) (by linarith)
    simpa only [neg_neg] using h
  have h2 : Tendsto (fun R : ℝ => R ^ (-((q : ℝ) / 2))) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := (q : ℝ) / 2) hb
    simpa only [] using h
  have hlim : Tendsto (fun R : ℝ =>
      A * (Real.sqrt (2 * n) / 2) * R ^ ((2 : ℝ) - (q : ℝ) / 2) +
        |t| * G * (Real.sqrt (2 * n) / 2) * R ^ (-((q : ℝ) / 2)))
      atTop (𝓝 0) := by
    have h := (h1.const_mul (A * (Real.sqrt (2 * n) / 2))).add
      (h2.const_mul (|t| * G * (Real.sqrt (2 * n) / 2)))
    simpa only [mul_zero, add_zero] using h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hsqrt : Real.sqrt (2 * R ^ q * n) = Real.sqrt (2 * n) * R ^ ((q : ℝ) / 2) := by
    rw [show (2 * R ^ q * n : ℝ) = (2 * n) * R ^ (q : ℝ) by
      rw [Real.rpow_natCast]; ring]
    rw [Real.sqrt_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [hsqrt]
  rw [show (R : ℝ) ^ q = R ^ (q : ℝ) from (Real.rpow_natCast R q).symm]
  have hsplit : (R ^ 2 * A + |t| * G) / R ^ (q : ℝ) =
      A * R ^ ((2 : ℝ) - (q : ℝ)) + |t| * G * R ^ (-(q : ℝ)) := by
    rw [add_div]
    have hA : R ^ 2 * A / R ^ (q : ℝ) = A * R ^ ((2 : ℝ) - (q : ℝ)) := by
      rw [show R ^ 2 * A / R ^ (q : ℝ) = (R ^ 2 / R ^ (q : ℝ)) * A by ring]
      rw [show R ^ 2 = R ^ (2 : ℝ) from (Real.rpow_two R).symm]
      rw [← Real.rpow_sub hR]
      ring
    have hB : |t| * G / R ^ (q : ℝ) = |t| * G * R ^ (-(q : ℝ)) := by
      rw [Real.rpow_neg hR.le]
      ring
    rw [hA, hB]
  rw [hsplit]
  exact (calc (A * R ^ ((2 : ℝ) - (q : ℝ)) + |t| * G * R ^ (-(q : ℝ))) *
        (Real.sqrt (2 * n) * R ^ ((q : ℝ) / 2) / 2)
      = A * (Real.sqrt (2 * n) / 2) *
          (R ^ ((2 : ℝ) - (q : ℝ)) * R ^ ((q : ℝ) / 2)) +
          |t| * G * (Real.sqrt (2 * n) / 2) *
            (R ^ (-(q : ℝ)) * R ^ ((q : ℝ) / 2)) := by ring
    _ = A * (Real.sqrt (2 * n) / 2) * R ^ ((2 : ℝ) - (q : ℝ) / 2) +
          |t| * G * (Real.sqrt (2 * n) / 2) * R ^ (-((q : ℝ) / 2)) := by
        rw [← Real.rpow_add hR, ← Real.rpow_add hR]
        congr 2 <;> ring).symm


end OTSelector.Probability
