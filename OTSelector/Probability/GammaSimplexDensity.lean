import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential

/-!
Conditions: The actual mathlib gamma measure with any real shape/rate in the support and integral identities; the factorial density calculation uses integer shape n+1, rate one and s≥0.

Objects: A.e. positive total mass, the integer-shape gamma density times n!, and positive-half-line integration against the actual gamma measure.

Proof detail: Use the gamma density support; simplify Γ(n+1)=n! in the valid integer-shape density, and restrict the nonnegative integral to the density support.

References: Günter Last and Mathew Penrose: Section 1.4, equations (1.23), (1.27)–(1.28), p. 6; NIST Digital Library of Mathematical Functions: Section 5.12, Euler beta integral, equation (5.12.1).
Relation: The standard positive-shape/rate gamma density is the mathematical source. The all-real support identity also handles mathlib’s degenerate invalid-parameter measures; it does not assert those are probability laws.
-/


/-!
# The gamma total-mass density

The original mathlib gamma law is concentrated on positive total masses. Its
integer-shape density supplies exactly the scalar simplex dilation factor.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OTSelector.Probability

theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ s ∂gammaMeasure a r, 0 < s := by
  have hn : ∀ᵐ s ∂gammaMeasure a r, 0 ≤ s := by
    apply ae_iff.mpr
    simp only [not_le]
    change gammaMeasure a r (Iio 0) = 0
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have hz : ∀ᵐ s ∂gammaMeasure a r, s ≠ 0 :=
    (withDensity_absolutelyContinuous volume (gammaPDF a r)).ae_le (Measure.ae_ne volume 0)
  filter_upwards [hn, hz] with s hs hne
  exact lt_of_le_of_ne hs hne.symm

theorem gammaPDF_nat_succ_one_mul_factorial (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    gammaPDF ((n : ℝ) + 1) 1 s * (n.factorial : ℝ≥0∞) =
      ENNReal.ofReal (s ^ n) * ENNReal.ofReal (Real.exp (-s)) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [gammaPDF_of_nonneg hs]
  simp only [Real.one_rpow, Real.Gamma_nat_eq_factorial, add_sub_cancel_right,
    Real.rpow_natCast, one_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (pow_nonneg hs _)]
  congr 1
  field_simp

theorem lintegral_gammaMeasure_Ioi (a r : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s, f s ∂gammaMeasure a r) = ∫⁻ s in Ioi (0 : ℝ), gammaPDF a r s * f s := by
  conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem (s := Ioi (0 : ℝ)) (ae_pos_gammaMeasure a r)]
  have hpdf : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, restrict_withDensity measurableSet_Ioi,
    lintegral_withDensity_eq_lintegral_mul _ hpdf hf]
  rfl

end OTSelector.Probability
