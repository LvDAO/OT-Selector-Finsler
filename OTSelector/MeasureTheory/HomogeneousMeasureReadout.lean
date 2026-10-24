import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
## Lemma skeleton

* **Conditions:** A measurable map e and observable F with exact homogeneity F(e x)=k F(x), under a scalar-multiplied pushforward measure.
* **Objects:** Signed and extended nonnegative homogeneous readout formulas.
* **Proof detail:** Apply scalar-measure integration and pushforward integration, substitute the homogeneity relation and pull out k.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27

**Relationship to the sources:** Direct map/measure-scaling identities. The signed statement uses the totalized real integral and a.toReal (including a=infinity); the nonnegative statement retains infinite moments.
-/

/-!
# Homogeneous readouts of the same scaled pushforward measure

A single change-of-variables calculation serves both kinetic and unchanged
probe readouts. The nonnegative version allows infinite moments.
-/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- A homogeneous real readout under the same scaled pushforward measure.
This is the Bochner readout identity; finite-value applications additionally
provide integrability on the actual measure. -/
theorem integral_smul_map_of_comp_eq_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : X → X) (he : Measurable e) (a : ℝ≥0∞)
    (F : X → ℝ) (hF : Measurable F) (k : ℝ)
    (hhom : ∀ x, F (e x) = k * F x) :
    (∫ x, F x ∂a • μ.map e) = a.toReal * k * ∫ x, F x ∂μ := by
  rw [integral_smul_measure,integral_map he.aemeasurable hF.aestronglyMeasurable]
  simp_rw [hhom]
  rw [integral_const_mul,smul_eq_mul,mul_assoc]

/-- The nonnegative homogeneous readout preserves the exact scaling even at
infinite energy; no moment-finiteness hypothesis is present. -/
theorem lintegral_smul_map_of_comp_eq_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : X → X) (he : Measurable e) (a : ℝ≥0∞)
    (F : X → ℝ≥0∞) (hF : Measurable F) (k : ℝ≥0∞)
    (hhom : ∀ x, F (e x) = k * F x) :
    (∫⁻ x, F x ∂a • μ.map e) = a * k * ∫⁻ x, F x ∂μ := by
  rw [lintegral_smul_measure,lintegral_map hF he]
  simp_rw [hhom]
  rw [lintegral_const_mul _ hF,smul_eq_mul,mul_assoc]

end OTSelector.Probability
