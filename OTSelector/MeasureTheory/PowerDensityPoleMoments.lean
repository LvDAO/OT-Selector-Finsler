import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
## Lemma skeleton

* **Conditions:** On (0,delta), a nonnegative measurable density d<=A s^k and a measurable normed-group-valued f with norm<=B/s; delta>0, A,B>=0 and 0<=r<k+1.
* **Objects:** Integrability of the rth norm moment under the original density-weighted interval law.
* **Proof detail:** The weighted moment is bounded by A B^r s^(k-r). The exponent k-r is greater than -1, so the scalar power is integrable; transfer this comparison through withDensity.

## Mathematical sources

* NIST DLMF; Chapter 5 by R. A. Askey and R. Roy, *NIST Digital Library of Mathematical Functions, Chapter 5: Gamma Function*, Section 5.12, Euler beta integral, equation 5.12.1.
  https://dlmf.nist.gov/5.12.E1
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27

**Relationship to the sources:** Power-comparison corollary. The scalar power criterion follows from the Euler beta integral with parameters k-r+1 and 1, followed by dilation; no pole moment is assumed in advance.
-/

/-!
# Integrating a focal pole against its vanishing density

An order `k` density zero cancels every positive moment of a first-order pole
below `k + 1`. The estimate is a direct comparison with the integrable power
`s^(k-r)` on a finite inward interval. Neither the moment nor a finite integral
bound is assumed.
-/

open Set MeasureTheory

namespace OTSelector.Geometry

/-- A density bounded by `A s^k` makes every `r < k+1` moment of a `B/s` pole
integrable. The density is allowed to vanish on arbitrary measurable subsets. -/
theorem integrable_rpow_withDensity_of_power_bounds
    {E : Type*} [NormedAddCommGroup E]
    {d : ℝ → ℝ} {f : ℝ → E} {δ A B r : ℝ} {k : ℕ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr0 : 0 ≤ r)
    (hr : r < (k : ℝ) + 1)
    (hd : AEMeasurable d (volume.restrict (Ioo 0 δ)))
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo 0 δ)))
    (hd0 : ∀ s ∈ Ioo 0 δ, 0 ≤ d s)
    (hdb : ∀ s ∈ Ioo 0 δ, d s ≤ A * s ^ k)
    (hfb : ∀ s ∈ Ioo 0 δ, ‖f s‖ ≤ B / s) :
    Integrable (fun s ↦ ‖f s‖ ^ r)
      ((volume.restrict (Ioo 0 δ)).withDensity (fun s ↦ ENNReal.ofReal (d s))) := by
  apply (integrable_withDensity_iff_integrable_smul₀'
    hd.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
  have hpow : IntegrableOn (fun s : ℝ ↦ s ^ ((k : ℝ) - r)) (Ioo 0 δ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).2 (by linarith)
  apply (hpow.const_mul (A * B ^ r)).mono'
    (hd.ennreal_ofReal.ennreal_toReal.aestronglyMeasurable.smul
      (hf.norm.aemeasurable.pow_const r).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  change ‖(ENNReal.ofReal (d s)).toReal * ‖f s‖ ^ r‖ ≤
    (A * B ^ r) * s ^ ((k : ℝ) - r)
  rw [ENNReal.toReal_ofReal (hd0 s hs), Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hd0 s hs) (Real.rpow_nonneg (norm_nonneg _) _))]
  calc
    d s * ‖f s‖ ^ r ≤ (A * s ^ k) * (B / s) ^ r :=
      mul_le_mul (hdb s hs) (Real.rpow_le_rpow (norm_nonneg _) (hfb s hs) hr0)
        (Real.rpow_nonneg (norm_nonneg _) _) (mul_nonneg hA (pow_nonneg hs.1.le _))
    _ = (A * B ^ r) * s ^ ((k : ℝ) - r) := by
      rw [Real.div_rpow hB hs.1.le, Real.rpow_sub hs.1, Real.rpow_natCast]
      ring

end OTSelector.Geometry
