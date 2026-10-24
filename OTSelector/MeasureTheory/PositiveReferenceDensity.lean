import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
## Lemma skeleton

* **Conditions:** Two sigma-finite measures beta,lambda; a measurable region on which beta.rnDeriv(lambda) is nonzero. The final map identity only requires measurable map and density.
* **Objects:** lambda restricted to that region is absolutely continuous relative to beta, with positive finite reciprocal RN density; density pullback commutes with pushforward.
* **Proof detail:** Use the Lebesgue decomposition and positivity of the absolutely continuous density on the region; apply the RN chain/reciprocal identities there. Prove the map identity by integration over preimages.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Localized reverse absolute continuity, not global mutual absolute continuity. A singular component of beta is allowed and the reciprocal equality is only lambda-restricted almost everywhere.
-/

/-!
# Recovering a measure where a fixed reference has positive density

A measurable region on which the reference Radon--Nikodym derivative is nonzero
is absolutely continuous with respect to that reference. Its reverse density is
the reciprocal of the original factor almost everywhere on the original region.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

/-- The part of a measure where a reference has nonzero Radon--Nikodym density
is absolutely continuous with respect to that same reference. -/
theorem restrict_absolutelyContinuous_of_rnDeriv_ne_zero
    (beta lambda : Measure Z) [SigmaFinite beta] [SigmaFinite lambda]
    {s : Set Z} (hs : MeasurableSet s) (hpos : ∀ z ∈ s, beta.rnDeriv lambda z ≠ 0) :
    lambda.restrict s ≪ beta := by
  apply Measure.AbsolutelyContinuous.mk
  intro t _ ht
  apply measure_eq_zero_iff_ae_notMem.mpr
  have h := Measure.ae_rnDeriv_ne_zero_imp_of_ae lambda
    (measure_eq_zero_iff_ae_notMem.mp ht)
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hs] with z hz hzs
  exact hz (hpos z hzs)

/-- The reverse density on a positive-reference region is the reciprocal of the
original fixed reference factor; it is finite and positive under the original law. -/
theorem ae_restricted_reference_density_inv
    (beta lambda : Measure Z) [SigmaFinite beta] [SigmaFinite lambda]
    {s : Set Z} (hs : MeasurableSet s) (hpos : ∀ z ∈ s, beta.rnDeriv lambda z ≠ 0) :
    ∀ᵐ z ∂lambda.restrict s,
      0 < (lambda.restrict s).rnDeriv beta z ∧
      (lambda.restrict s).rnDeriv beta z < ∞ ∧
      (lambda.restrict s).rnDeriv beta z = (beta.rnDeriv lambda z)⁻¹ := by
  have hac := restrict_absolutelyContinuous_of_rnDeriv_ne_zero beta lambda hs hpos
  have hmul := Measure.rnDeriv_mul_rnDeriv (κ := lambda) hac
  filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le ((lambda.restrict s).rnDeriv_lt_top beta),
    ae_restrict_of_ae hmul, ae_restrict_of_ae (Measure.rnDeriv_restrict_self lambda hs),
    ae_restrict_mem hs] with z hzpos hzfinite hchain hrestrict hzs
  refine ⟨hzpos, hzfinite, ENNReal.eq_inv_of_mul_eq_one_left ?_⟩
  calc
    (lambda.restrict s).rnDeriv beta z * beta.rnDeriv lambda z =
      (lambda.restrict s).rnDeriv lambda z := hchain
    _ = 1 := by simpa only [indicator_of_mem hzs, Pi.one_apply] using hrestrict

/-- Pushing forward a composed density preserves its exact original weight. -/
theorem map_withDensity_comp_measurable (μ : Measure W) {f : W → Z} (hf : Measurable f)
    {g : Z → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (fun w ↦ g (f w))).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hf]

end OTSelector.Reconstruction
