import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Poisson Exponential Fourth Moment

Conditions: A.e.-measurable a.e.-nonnegative real observable with the full stated Poisson exponential upper bound and intensity r≥0; an exact Poisson law is not assumed.

Objects: A genuine integrable fourth power with bound 192 exp(e−1)(1+r⁴).

Proof detail: Choose tilt (1+r)⁻¹, bound r(exp tilt−1) by e−1 and dominate x⁴ by 24(1+r)⁴ exp(x/(1+r)); integrate and simplify constants.

Relation to primary sources: A local exponential-Taylor moment consequence of the standard Poisson transform; the deliberately coarse polynomial constant is not a textbook exact fourth moment.

References:
* Gunter Last; Mathew Penrose, Lectures on the Poisson Process, author version 21 August 2017, Section 1.1, equations (1.8)–(1.10), p. 2. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=14
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
-/
/-! Polynomial fourth moments from the full original Poisson exponential bound. -/
open Set MeasureTheory
noncomputable section
namespace OTSelector.Probability

/-- The exponential tilt scaled by the true mean has a uniform exponent. -/
theorem poisson_scaled_exponent_le {r : ℝ} (hr : 0 ≤ r) :
    r * (Real.exp ((1 + r)⁻¹) - 1) ≤ Real.exp 1 - 1 := by
  let t := (1 + r)⁻¹
  have hr1 : 0 < 1 + r := by linarith
  have ht : 0 ≤ t := (inv_pos.mpr hr1).le
  have ht1 : t ≤ 1 := (inv_le_one₀ hr1).mpr (by linarith)
  have he := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr ht1) ht (show (1 - t) + t = 1 by ring)
  have hexp : Real.exp t - 1 ≤ t * (Real.exp 1 - 1) := by
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at he
    linarith
  have he₀ : 0 ≤ Real.exp 1 - 1 := by
    have h := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    rw [Real.exp_zero] at h
    linarith
  have hrt : r * t ≤ 1 := by
    change r * (1 + r)⁻¹ ≤ 1
    rw [← div_eq_mul_inv, div_le_one hr1]
    linarith
  calc
    _ ≤ r * (t * (Real.exp 1 - 1)) := mul_le_mul_of_nonneg_left hexp hr
    _ = (r * t) * (Real.exp 1 - 1) := by ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hrt he₀

/-- The scaled exponential dominates the fourth power with its exact Taylor coefficient. -/
theorem fourth_pow_le_scaled_exp {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    x ^ 4 ≤ 24 * (1 + r) ^ 4 * Real.exp ((1 + r)⁻¹ * x) := by
  have hr1 : 0 < 1 + r := by linarith
  have h := Real.pow_div_factorial_le_exp (x / (1 + r)) (div_nonneg hx hr1.le) 4
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  rw [div_pow] at h
  have h' : x ^ 4 / (1 + r) ^ 4 ≤ 24 * Real.exp (x / (1 + r)) := by linarith
  have h'' := (div_le_iff₀ (pow_pos hr1 4)).mp h'
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h''

/-- The complete Poisson exponential bound implies the polynomial fourth-moment
bound used for original phase balls; no exact law of a selected count is assumed. -/
theorem integrable_fourth_pow_and_integral_le_of_poisson_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → ℝ} (hN : AEMeasurable N P) (hn : ∀ᵐ ω ∂P, 0 ≤ N ω)
    {r : ℝ} (hr : 0 ≤ r)
    (hI : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * N ω)) P)
    (hbound : ∀ t : ℝ, 0 ≤ t → (∫ ω, Real.exp (t * N ω) ∂P) ≤
      Real.exp (r * (Real.exp t - 1))) :
    Integrable (fun ω ↦ N ω ^ 4) P ∧
      (∫ ω, N ω ^ 4 ∂P) ≤ 192 * Real.exp (Real.exp 1 - 1) * (1 + r ^ 4) := by
  let t := (1 + r)⁻¹
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hdom := (hI t ht).const_mul (24 * (1 + r) ^ 4)
  have hpow : Integrable (fun ω ↦ N ω ^ 4) P := by
    apply hdom.mono_nonneg (hN.pow_const 4).aestronglyMeasurable
      (.of_forall (fun ω ↦ by positivity))
    filter_upwards [hn] with ω hω
    exact fourth_pow_le_scaled_exp hr hω
  refine ⟨hpow, ?_⟩
  have hpoly : (1 + r) ^ 4 ≤ 8 * (1 + r ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (r - 1))
      (show 0 ≤ 7 * r ^ 2 + 10 * r + 7 by positivity)]
  calc
    _ ≤ ∫ ω, 24 * (1 + r) ^ 4 * Real.exp (t * N ω) ∂P := by
      apply integral_mono_ae hpow hdom
      filter_upwards [hn] with ω hω
      exact fourth_pow_le_scaled_exp hr hω
    _ = 24 * (1 + r) ^ 4 * ∫ ω, Real.exp (t * N ω) ∂P := integral_const_mul _ _
    _ ≤ 24 * (1 + r) ^ 4 * Real.exp (r * (Real.exp t - 1)) :=
      mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)
    _ ≤ 24 * (1 + r) ^ 4 * Real.exp (Real.exp 1 - 1) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (poisson_scaled_exponent_le hr))
        (by positivity)
    _ ≤ _ := by
      have hscaled := mul_le_mul_of_nonneg_right hpoly
        (show 0 ≤ 24 * Real.exp (Real.exp 1 - 1) by positivity)
      nlinarith [hscaled]

end OTSelector.Probability
