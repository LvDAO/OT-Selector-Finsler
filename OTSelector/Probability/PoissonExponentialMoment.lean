import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Basic

/-!
# Poisson Exponential Moment

Conditions: Actual Poisson measure with nonnegative intensity, or an explicit HasLaw to that measure; a nonnegative tilt is used for the upper-count tail.

Objects: Exponential summability/integrability, exact E exp(tN)=exp(r(exp t−1)) and a Chernoff upper-tail bound.

Proof detail: Sum the Poisson series, transport the integral along the supplied law identity and apply exponential Markov to the upper tail.

Relation to primary sources: The exact Poisson transform is standard. Law transport and the Chernoff consequence are local; later selection does not preserve this law automatically.

References:
* Gunter Last; Mathew Penrose, Lectures on the Poisson Process, author version 21 August 2017, Section 1.1, equations (1.8)–(1.10), p. 2. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=14
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
-/
/-!
# Exact original Poisson exponential count moments

These are moments of the original count law. Uniform candidate bounds below
use these full-input counts before any adaptive path or phase curve selection.
-/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 1200000

private theorem hasSum_poisson_exp (r : ℝ≥0) (t : ℝ) :
    HasSum (fun n : ℕ ↦ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial *
      Real.exp (t * (n : ℝ))) (Real.exp ((r : ℝ) * (Real.exp t - 1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp t)).mul_left
    (Real.exp (-(r : ℝ)))
  have hout : Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * Real.exp t) =
      Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← Real.exp_eq_exp_ℝ, hout] at h
  convert! h using 1
  funext n
  rw [mul_pow, ← Real.exp_nat_mul]
  rw [mul_comm (n : ℝ) t]
  ring

/-- Every real exponential tilt of the true original Poisson count is integrable. -/
theorem integrable_exp_mul_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    Integrable (fun n : ℕ ↦ Real.exp (t * (n : ℝ))) (poissonMeasure r) := by
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (hasSum_poisson_exp r t).summable

/-- The exact original Poisson count moment generating function. -/
theorem integral_exp_mul_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    (∫ n : ℕ, Real.exp (t * (n : ℝ)) ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  have h := hasSum_integral_poissonMeasure (integrable_exp_mul_poissonMeasure r t)
  simp only [smul_eq_mul] at h
  exact h.unique (hasSum_poisson_exp r t)

/-- An arbitrary original random count with a Poisson law has the same exact
exponential moment; the count need not be independent of later selections. -/
theorem integrable_and_integral_exp_mul_of_hasLaw_poisson
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → ℕ} {r : ℝ≥0} (hN : ProbabilityTheory.HasLaw N (poissonMeasure r) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * (N ω : ℝ))) P ∧
      (∫ ω, Real.exp (t * (N ω : ℝ)) ∂P) = Real.exp ((r : ℝ) * (Real.exp t - 1)) := by
  have hI := integrable_exp_mul_poissonMeasure r t
  have hImap : Integrable (fun n : ℕ ↦ Real.exp (t * (n : ℝ))) (P.map N) := by
    rwa [hN.map_eq]
  have hI' := (integrable_map_measure hImap.aestronglyMeasurable hN.aemeasurable).mp hImap
  refine ⟨hI', ?_⟩
  have he := hN.integral_comp hI.aestronglyMeasurable
  exact he.trans (integral_exp_mul_poissonMeasure r t)

/-- Original Poisson counts obey the literal exponential upper tail bound. -/
theorem measure_ge_poisson_count_le_exp_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {N : Ω → ℕ} {r : ℝ≥0} (hN : ProbabilityTheory.HasLaw N (poissonMeasure r) P)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | x ≤ (N ω : ℝ)} ≤ Real.exp ((r : ℝ) * (Real.exp t - 1) - t * x) := by
  have hm := integrable_and_integral_exp_mul_of_hasLaw_poisson hN t
  have h := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω ↦ (N ω : ℝ)) x ht hm.1
  rw [mgf, hm.2, ← Real.exp_add] at h
  convert! h using 1
  congr 1
  ring

end OTSelector.Probability
