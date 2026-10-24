import Mathlib.Probability.Kernel.CompProdEqIff
import OTSelector.Probability.ConditionalScalarAbsoluteContinuity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LabelClockConditionalDensity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LabelClockConditionalDensity`; the selected original proof blocks follow. -/
section

/-!
# Probability.LabelClockConditionalDensity

## Lemma skeleton

* **Conditions:** A finite original measure and measurable density representation of its joint label-clock law relative to its actual label marginal times volume.
* **Objects:** Entire actual conditional clock measure equals the section density measure almost everywhere in the label.
* **Proof detail:** Use an equivalent finite scalar reference and uniqueness of disintegration/RN densities to identify the two conditional kernels as measures.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (composition): Conditional density identification; arbitrary exceptional sections need not satisfy a uniform finite-kernel bound.
-/

/-!
# Identifying the original scalar conditional density

A measurable density of the original joint label-clock law gives the actual
conditional clock measures almost everywhere. An equivalent finite reference
and the existing finite-kernel Radon–Nikodym theorem identify entire measures,
without imposing a global finite-kernel bound on arbitrary exceptional sections.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- Any measurable density of the original joint label-clock law is the density
of its existing scalar conditional distribution at almost every original label. -/
theorem ae_withDensity_clock_eq_condDistrib
    {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
    (eta : Measure M) [IsFiniteMeasure eta]
    {a : M → Z} {u : M → ℝ} (hu : Measurable u)
    {h : Z × ℝ → ℝ≥0∞} (hh : Measurable h)
    (hden : ((eta.map a).prod (volume : Measure ℝ)).withDensity h =
      eta.map (fun x ↦ (a x, u x))) :
    ∀ᵐ z ∂eta.map a,
      (volume : Measure ℝ).withDensity (fun s ↦ h (z, s)) = condDistrib u a eta z := by
  let lambda := eta.map a
  let nu := (volume : Measure ℝ)
  let tau := nu.toFinite
  let kappa := condDistrib u a eta
  let beta := Kernel.const Z tau
  let w := kappa.rnDeriv beta
  let kappaAC := beta.withDensity w
  let r := tau.rnDeriv nu
  let k := fun y : Z × ℝ ↦ r y.2 * w y.1 y.2
  have hw : Measurable (Function.uncurry w) := kappa.measurable_rnDeriv beta
  have hr : Measurable r := Measure.measurable_rnDeriv tau nu
  have hk : Measurable k := (hr.comp measurable_snd).mul hw
  have hAC : eta.map (fun x ↦ (a x, u x)) ≪ (eta.map a).prod volume := by
    rw [← hden]
    exact withDensity_absolutelyContinuous _ _
  have hcond : ∀ᵐ z ∂lambda, kappa z ≪ beta z := by
    filter_upwards [ae_condDistrib_clock_absolutelyContinuous_of_joint eta hu hAC] with z hz
    exact hz.trans (absolutelyContinuous_toFinite nu)
  have hkernel : kappaAC =ᵐ[lambda] kappa := hcond.mono fun z hz ↦
    Kernel.withDensity_rnDeriv_eq hz
  have htau : nu.withDensity r = tau :=
    Measure.withDensity_rnDeriv_eq tau nu (toFinite_absolutelyContinuous nu)
  have hsection (z : Z) : nu.withDensity (fun s ↦ k (z, s)) = kappaAC z := by
    change nu.withDensity (r * w z) = beta.withDensity w z
    have hwz : Measurable (w z) := hw.comp measurable_prodMk_left
    rw [withDensity_mul nu hr hwz, htau,
      Kernel.withDensity_apply beta hw, Kernel.const_apply]
  have hkdensity : (lambda.prod nu).withDensity k =
      eta.map (fun x ↦ (a x, u x)) := by
    calc
      (lambda.prod nu).withDensity k =
          ((lambda.prod nu).withDensity (fun y ↦ r y.2)).withDensity
            (Function.uncurry w) :=
        withDensity_mul _ (hr.comp measurable_snd) hw
      _ = (lambda.prod tau).withDensity (Function.uncurry w) := by
        rw [← prod_withDensity_right hr, htau]
      _ = lambda ⊗ₘ kappaAC := by
        rw [Measure.compProd_withDensity hw, Measure.compProd_const]
        rfl
      _ = lambda ⊗ₘ kappa := Measure.compProd_congr hkernel
      _ = _ := compProd_map_condDistrib hu.aemeasurable
  have heq : h =ᵐ[lambda.prod nu] k :=
    (withDensity_eq_iff_of_sigmaFinite hh.aemeasurable hk.aemeasurable).mp
      (hden.trans hkdensity.symm)
  filter_upwards [Measure.ae_ae_of_ae_prod heq, hkernel] with z hz hzk
  exact (withDensity_congr_ae hz).trans ((hsection z).trans hzk)

end OTSelector.Reconstruction

end
