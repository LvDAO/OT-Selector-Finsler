import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Analysis.InnerProductSpace.FiniteCoefficientCauchy

## Lemma skeleton

* **Conditions:** Real L2 functions or integrable measurable squares, or finite scalar coefficients with the stated square bounds.

* **Objects:** Integral and finite coefficient Cauchy–Schwarz inequalities with explicit cardinality factors.

* **Proof detail:** Identify the real L2 inner product with the integral product, apply Hilbert Cauchy–Schwarz and square it. For finite coefficients apply the finite version and sum the coefficient square bound.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.3 (Hölder), p. 29.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57): Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48.

Source relation (corollary): The arbitrary-measure L2 formulation and raw finite-subtype sums are local adapters of Cauchy–Schwarz.
-/

/-! Actual scalar L2 and finite-coefficient Cauchy bounds for cube pairings. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

private theorem real_L2_inner_toLp_eq_integral_mul
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

/-- Cauchy for the literal scalar product integral of two actual L2 functions. -/
theorem integral_mul_sq_le_of_memLp_two
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (∫ x, u x * v x ∂μ)^2 ≤
      (∫ x, (u x)^2 ∂μ) * (∫ x, (v x)^2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hu.toLp u) (hv.toLp v)
  rw [real_L2_inner_toLp_eq_integral_mul hu hv,
    real_L2_inner_toLp_eq_integral_mul hu hu,
    real_L2_inner_toLp_eq_integral_mul hv hv] at h
  simpa only [sq] using h

/-- Literal square-integrability interface for the actual scalar integral Cauchy bound. -/
theorem integral_mul_sq_le_of_integrable_sq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → ℝ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hu2 : Integrable (fun x ↦ (u x)^2) μ)
    (hv2 : Integrable (fun x ↦ (v x)^2) μ) :
    (∫ x, u x * v x ∂μ)^2 ≤
      (∫ x, (u x)^2 ∂μ) * (∫ x, (v x)^2 ∂μ) :=
  integral_mul_sq_le_of_memLp_two ((memLp_two_iff_integrable_sq hu).mpr hu2)
    ((memLp_two_iff_integrable_sq hv).mpr hv2)

/-- A finite actual coefficient bound gives a concrete common quadratic majorant. -/
theorem sum_mul_sq_le_card_mul_of_coeff_sq_le
    {ι : Type*} (s : Finset ι) (c a : ι → ℝ) {M : ℝ}
    (hc : ∀ j ∈ s, (c j)^2 ≤ M) :
    (∑ j ∈ s, c j * a j)^2 ≤ (s.card : ℝ) * M * ∑ j ∈ s, (a j)^2 := by
  have hsum : (∑ j ∈ s, (c j)^2) ≤ (s.card : ℝ) * M := by
    calc
      _ ≤ ∑ _j ∈ s, M := Finset.sum_le_sum hc
      _ = _ := by simp [nsmul_eq_mul]
  exact (Finset.sum_mul_sq_le_sq_mul_sq s c a).trans
    (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)))

/-- Fintype form with the literal number of finite-rank coefficients. -/
theorem sum_mul_sq_le_fintype_card_mul_of_coeff_sq_le
    {ι : Type*} [Fintype ι] (c a : ι → ℝ) {M : ℝ}
    (hc : ∀ j, (c j)^2 ≤ M) :
    (∑ j, c j * a j)^2 ≤ (Fintype.card ι : ℝ) * M * ∑ j, (a j)^2 := by
  simpa only [Finset.card_univ] using
    sum_mul_sq_le_card_mul_of_coeff_sq_le Finset.univ c a (fun j _ ↦ hc j)

end OTSelector.Reconstruction
