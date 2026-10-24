import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith

/-!
## Lemma skeleton

* **Conditions:** An almost-everywhere finite nonnegative density theta and real exponent a<1; the pressure specialization has q>2.
* **Objects:** Density-weighted integral and integrability identities replacing theta^(-a) under withDensity by theta^(1-a) under the original measure.
* **Proof detail:** Use the withDensity integral formula, then theta*theta^(-a)=theta^(1-a); treat theta=0 separately using 1-a>0.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27

**Relationship to the sources:** Change-of-density plus an elementary power identity including zero density. Equality of totalized real Bochner integrals is stated without adding an integrability hypothesis; integrability equivalences are separate.
-/

/-!
# Density powers under the unchanged original population measure

A population weight theta^(-a) becomes the Haar weight theta^(1-a) after
multiplication by the original density.  The identity includes zero density
when a<1 and never assumes a positive lower density bound.
-/
open MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Multiplication by the original density pays exactly one density power,
including at theta=0. -/
theorem density_mul_rpow_neg_weight {theta a : ℝ} (htheta : 0 ≤ theta) (ha : a < 1)
    (v : ℝ) : theta * (theta ^ (-a) * v) = theta ^ (1 - a) * v := by
  have hexp : 1 + -a ≠ 0 := by linarith
  have heq := Real.rpow_add' htheta hexp
  rw [Real.rpow_one] at heq
  calc
    _ = (theta * theta ^ (-a)) * v := by ring
    _ = theta ^ (1 + -a) * v := by rw [← heq]
    _ = _ := by rfl

/-- Original population and Haar integrals are the same integral after the
correct density power. No readout measurability or integrability is needed for
this Bochner-integral identity. -/
theorem integral_withDensity_rpow_weight
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (theta : X → ℝ≥0∞) (hm : AEMeasurable theta μ)
    (hfinite : ∀ᵐ x ∂μ, theta x < ∞) {a : ℝ} (ha : a < 1) (g : X → ℝ) :
    (∫ x, (theta x).toReal ^ (-a) * g x ∂μ.withDensity theta) =
      ∫ x, (theta x).toReal ^ (1 - a) * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm hfinite]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    simpa only [smul_eq_mul] using density_mul_rpow_neg_weight ENNReal.toReal_nonneg ha (g x)

/-- Integrability transfers in both directions through the same original
change of measure, without a positive lower density assumption. -/
theorem integrable_withDensity_rpow_weight_iff
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (theta : X → ℝ≥0∞) (hm : AEMeasurable theta μ)
    (hfinite : ∀ᵐ x ∂μ, theta x < ∞) {a : ℝ} (ha : a < 1) (g : X → ℝ) :
    Integrable (fun x ↦ (theta x).toReal ^ (-a) * g x) (μ.withDensity theta) ↔
      Integrable (fun x ↦ (theta x).toReal ^ (1 - a) * g x) μ := by
  rw [integrable_withDensity_iff_integrable_smul₀' hm hfinite]
  have heq : (fun x ↦ (theta x).toReal • ((theta x).toReal ^ (-a) * g x)) =
      fun x ↦ (theta x).toReal ^ (1 - a) * g x := by
    funext x
    simpa only [smul_eq_mul] using density_mul_rpow_neg_weight ENNReal.toReal_nonneg ha (g x)
  rw [heq]

/-- The exact pressure normalization at q>2: population exponent -2/q and
Haar exponent 1-2/q describe the same original signed pressure integral. -/
theorem integral_withDensity_pressure_scale
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (theta : X → ℝ≥0∞) (hm : AEMeasurable theta μ)
    (hfinite : ∀ᵐ x ∂μ, theta x < ∞) {q : ℝ} (hq : 2 < q)
    (I : X → ℝ → ℝ) (t : ℝ) :
    (∫ x, (theta x).toReal ^ (-2 / q) *
      I x (t * (theta x).toReal ^ (2 / q)) ∂μ.withDensity theta) =
      ∫ x, (theta x).toReal ^ (1 - 2 / q) *
        I x (t * (theta x).toReal ^ (2 / q)) ∂μ := by
  have hq0 : 0 < q := by linarith
  have ha : 2 / q < 1 := (div_lt_one hq0).mpr hq
  simpa only [neg_div] using integral_withDensity_rpow_weight μ theta hm hfinite ha
    (fun x ↦ I x (t * (theta x).toReal ^ (2 / q)))

/-- The corresponding exact integrability equivalence for the original
population pressure and its corrected Haar representation. -/
theorem integrable_withDensity_pressure_scale_iff
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (theta : X → ℝ≥0∞) (hm : AEMeasurable theta μ)
    (hfinite : ∀ᵐ x ∂μ, theta x < ∞) {q : ℝ} (hq : 2 < q)
    (I : X → ℝ → ℝ) (t : ℝ) :
    Integrable (fun x ↦ (theta x).toReal ^ (-2 / q) *
      I x (t * (theta x).toReal ^ (2 / q))) (μ.withDensity theta) ↔
      Integrable (fun x ↦ (theta x).toReal ^ (1 - 2 / q) *
        I x (t * (theta x).toReal ^ (2 / q))) μ := by
  have hq0 : 0 < q := by linarith
  have ha : 2 / q < 1 := (div_lt_one hq0).mpr hq
  simpa only [neg_div] using integrable_withDensity_rpow_weight_iff μ theta hm hfinite ha
    (fun x ↦ I x (t * (theta x).toReal ^ (2 / q)))

end OTSelector.Probability
