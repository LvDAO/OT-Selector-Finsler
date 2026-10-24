import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
Conditions: The actual Poisson probability law with any nonnegative rate, including zero.

Objects: Mean absolute deviation from its own rate bounded by sqrt(rate).

Proof detail: Expand the centered Poisson second moment to the rate and apply the probability L2/Jensen bound to the absolute deviation.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.2, p. 29.
Relation: A locally computed first absolute central moment bound, not an asserted exact formula for that absolute moment.
-/


/-!
# Mean absolute deviation of a single Poisson variable

A Poisson variable with rate `a` deviates from its mean `a` by at most `sqrt a`
in mean absolute value.  The proof expands the second moment of the centred
count `n ↦ n - a`, which equals `a`, and applies the elementary inequality
`(∫ |f|)² ≤ ∫ f²` on a probability space.

This single-cell estimate is the building block for the per-cell Poisson
discrepancy bounds used in the hierarchical matching argument.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

/-- The mean absolute deviation of a Poisson variable with rate `a` from its
mean `a` is at most `sqrt a`. -/
theorem integral_abs_sub_id_poissonMeasure_le (a : ℝ≥0) :
    ∫ n : ℕ, |(n : ℝ) - (a : ℝ)| ∂poissonMeasure a ≤ Real.sqrt (a : ℝ) := by
  classical
  let μ := poissonMeasure a
  let f : ℕ → ℝ := fun n => (n : ℝ) - (a : ℝ)
  have hsq : Integrable (fun n : ℕ => ((n : ℝ) ^ 2)) μ := by
    rw [integrable_poissonMeasure_iff]
    refine (poissonSecondMoment_hasSum a).summable.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [poissonMeasure_real_singleton]
    ring
  have hid : Integrable (fun n : ℕ => (n : ℝ)) μ := integrable_id_poissonMeasure a
  have hquad : Integrable (fun n : ℕ => ((n : ℝ) ^ 2 - 2 * (a : ℝ) * (n : ℝ))) μ :=
    hsq.sub (hid.const_mul (2 * (a : ℝ)))
  have hfint : Integrable f μ := by
    have h := hid.sub (integrable_const (a : ℝ) : Integrable (fun _ : ℕ => (a : ℝ)) μ)
    convert h using 1
    funext n
    simp only [f, Pi.sub_apply]
  have hf2 : Integrable (fun n : ℕ => (f n) ^ 2) μ := by
    have h := hquad.add
      (integrable_const ((a : ℝ) ^ 2) : Integrable (fun _ : ℕ => (a : ℝ) ^ 2) μ)
    refine h.congr (Filter.Eventually.of_forall fun n => ?_)
    simp only [f, Pi.add_apply]
    ring
  have hf_mem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hfint.aestronglyMeasurable).mpr hf2
  have habs_mem : MemLp (fun n => |f n|) 2 μ := hf_mem.abs
  have hjensen := integral_sq_le_integral_sq_of_prob μ habs_mem
  have habs_nonneg : 0 ≤ ∫ n, |f n| ∂μ := integral_nonneg fun n => abs_nonneg _
  have hstep : ∫ n, |f n| ∂μ ≤ Real.sqrt (∫ n, (f n) ^ 2 ∂μ) := by
    rw [← Real.sqrt_sq habs_nonneg]
    exact Real.sqrt_le_sqrt (by simpa only [sq_abs] using hjensen)
  have hval : ∫ n, (f n) ^ 2 ∂μ = (a : ℝ) := by
    have hpt : (fun n : ℕ => (f n) ^ 2) =
        ((fun n : ℕ => ((n : ℝ) ^ 2 - 2 * (a : ℝ) * (n : ℝ))) +
          fun _ : ℕ => (a : ℝ) ^ 2) := by
      funext n
      simp only [f, Pi.add_apply]
      ring
    rw [hpt]
    change ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (a : ℝ) * (n : ℝ)) + (a : ℝ) ^ 2 ∂μ =
      (a : ℝ)
    rw [integral_add hquad (integrable_const ((a : ℝ) ^ 2)),
      integral_sub hsq (hid.const_mul (2 * (a : ℝ))),
      integral_const_mul, integral_sq_id_poissonMeasure, integral_id_poissonMeasure,
      integral_const]
    simp [measureReal_def]
    ring
  rw [hval] at hstep
  simpa only [f, μ] using hstep

end OTSelector.Probability
