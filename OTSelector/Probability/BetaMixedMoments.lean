import Mathlib.Probability.Distributions.Beta

/-!
## Lemma skeleton

* **Conditions:** For support only: a,b are arbitrary real numbers and betaMeasure is the existing density-based mathlib measure. For the density shift and mixed moments: a>0, b>0 and m,n are natural numbers; the pointwise density identity holds for every real x. For integer normalizers: m,n are natural numbers.
* **Objects:** The beta normalizer B(a,b), betaPDF a b and betaMeasure a b on the real line. The complementary monomial (ofReal x)^m (ofReal (1-x))^n with values in the extended nonnegative reals. The shifted beta parameters a+m,b+n and the scalar B(a+m,b+n)/B(a,b).
* **Proof detail:** Use the density definition to show that the complement of the open unit interval has zero measure. On the open interval combine exponents and cancel positive beta normalizers; outside it both density expressions vanish. Integrate the shifted-density identity and use normalization of the shifted beta law. Evaluate positive integer normalizers by the gamma-factorial identity.

## Mathematical sources

* NIST DLMF; Chapter 5 by R. A. Askey and R. Roy, *NIST Digital Library of Mathematical Functions, Chapter 5: Gamma Function*, Section 5.12, Euler beta integral, equation 5.12.1.
  https://dlmf.nist.gov/5.12.E1
* NIST DLMF; Chapter 5 by R. A. Askey and R. Roy, *NIST Digital Library of Mathematical Functions, Chapter 5: Gamma Function*, Section 5.4(i), equation 5.4.1.
  https://dlmf.nist.gov/5.4.E1

**Relationship to the sources:** Euler beta integration supplies the normalizer and moment computation; the density shift and support encoding are direct local consequences. The support theorem deliberately has weaker parameter assumptions than the probability interpretation.
-/

/-!
# Mixed moments of the existing beta probability law

Multiplying the actual beta density by powers of the two complementary weights
shifts its shape parameters. Its existing normalization theorem then gives the
exact mixed moments needed for the Dirichlet reference distribution.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Probability

/-- The existing beta density is carried by the open unit interval. -/
theorem ae_mem_Ioo_betaMeasure (a b : ℝ) :
    ∀ᵐ x ∂betaMeasure a b, x ∈ Set.Ioo (0 : ℝ) 1 := by
  apply ae_iff.mpr
  change betaMeasure a b (Set.Ioo (0 : ℝ) 1)ᶜ = 0
  rw [betaMeasure, withDensity_apply _ measurableSet_Ioo.compl]
  apply setLIntegral_eq_zero measurableSet_Ioo.compl
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_Ioo] at hx
  simp [betaPDF, betaPDFReal, hx]

/-- Multiplication by a monomial shifts both beta shape parameters. -/
theorem betaPDF_mul_nat_powers {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (m n : ℕ) (x : ℝ) :
    betaPDF a b x * ((ENNReal.ofReal x) ^ m * (ENNReal.ofReal (1 - x)) ^ n) =
      ENNReal.ofReal (beta (a + m) (b + n) / beta a b) * betaPDF (a + m) (b + n) x := by
  by_cases hx : 0 < x ∧ x < 1
  · have hx' : 0 < 1 - x := sub_pos.mpr hx.2
    have ham : 0 < a + m := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg m)
    have hbn : 0 < b + n := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)
    have hreal :
        (1 / beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1)) * (x ^ m * (1 - x) ^ n) =
        (beta (a + m) (b + n) / beta a b) *
          (1 / beta (a + m) (b + n) * x ^ (a + m - 1) * (1 - x) ^ (b + n - 1)) := by
      rw [show a + m - 1 = (a - 1) + m by ring,
        show b + n - 1 = (b - 1) + n by ring,
        Real.rpow_add hx.1, Real.rpow_add hx', Real.rpow_natCast, Real.rpow_natCast]
      field_simp [(beta_pos ha hb).ne', (beta_pos ham hbn).ne']
    have hpdf : 0 < 1 / beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1) := by
      simpa only [betaPDFReal, ite_eq_left hx] using betaPDFReal_pos hx.1 hx.2 ha hb
    simp only [betaPDF, betaPDFReal, ite_eq_left hx]
    rw [← ENNReal.ofReal_pow hx.1.le, ← ENNReal.ofReal_pow hx'.le,
      ← ENNReal.ofReal_mul (pow_nonneg hx.1.le m),
      ← ENNReal.ofReal_mul hpdf.le,
      ← ENNReal.ofReal_mul (le_of_lt (div_pos (beta_pos ham hbn) (beta_pos ha hb))), hreal]
  · simp [betaPDF, betaPDFReal, hx]

/-- The exact mixed moments of the original mathlib beta measure. -/
theorem lintegral_beta_nat_powers {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (m n : ℕ) :
    (∫⁻ x, (ENNReal.ofReal x) ^ m * (ENNReal.ofReal (1 - x)) ^ n ∂betaMeasure a b) =
      ENNReal.ofReal (beta (a + m) (b + n) / beta a b) := by
  have hpdf (u v : ℝ) : Measurable (betaPDF u v) :=
    (measurable_betaPDFReal u v).ennreal_ofReal
  rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ (hpdf a b) (by fun_prop)]
  simp_rw [Pi.mul_apply, betaPDF_mul_nat_powers ha hb]
  rw [lintegral_const_mul _ (hpdf (a + m) (b + n)),
    lintegral_betaPDF_eq_one
      (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg m))
      (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)), mul_one]

/-- Positive integer beta normalizers are explicit factorial ratios. -/
theorem beta_nat_succ_eq_factorial (m n : ℕ) :
    beta (m + 1) (n + 1) =
      (m.factorial : ℝ) * n.factorial / (m + n + 1).factorial := by
  unfold beta
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    show (m : ℝ) + 1 + (n + 1) = ((m + n + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]

end OTSelector.Probability
