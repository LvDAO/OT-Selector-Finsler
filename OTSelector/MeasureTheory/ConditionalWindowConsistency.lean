import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.CondDistrib
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConditionalWindowConsistency.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConditionalWindowConsistency`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ConditionalWindowConsistency

Conditions: Measurable nested seed subsets and a measurable label embedding; sigma-finiteness is required exactly for the reference-density statements, and the gluing theorem uses a countable measurable cover.
Objects: Pushforward label references, their restricted Radon–Nikodym factors, and a global measure assembled from equal local density restrictions.
Proof detail: Push the smaller seed inclusion through the label embedding, apply restriction of a Radon–Nikodym derivative, and detect measure equality on the countable cover.

## Mathematical sources

- D. H. Fremlin, *Measure Theory, Volume 2*: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure. https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
- D. H. Fremlin, *Measure Theory, Volume 2*: Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40. https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27
- D. H. Fremlin, *Measure Theory, Volume 4*: Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106

Source relation: Derived restriction and countable-patching identities. No summability of moment estimates and no positive population-density bound are introduced.
-/

/-!
# One label reference across a countable geometric window cover

Restricting a fixed seed Haar reference only restricts its label pushforward. Its
Radon--Nikodym factor is consequently unchanged on every retained label. Exact
conditional densities then glue over a countable cover without summing moments.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {W Z X : Type*} [MeasurableSpace W] [MeasurableSpace Z] [MeasurableSpace X]

/-- The same original label map applied to the reference on a measurable seed subset. -/
def labelReferenceOn (κ : Measure W) (a : W → Z) (S : Set W) : Measure Z :=
  (κ.comap ((↑) : S → W)).map (fun w : S ↦ a w)

/-- Passing to a smaller set of the same seed only restricts its label reference. -/
theorem labelReferenceOn_eq_restrict (κ : Measure W) {a : W → Z} {S L : Set W}
    (hS : MeasurableSet S) (hL : MeasurableSet L) (hLS : L ⊆ S)
    (ha : MeasurableEmbedding (fun w : S ↦ a w)) :
    labelReferenceOn κ a L = (labelReferenceOn κ a S).restrict (a '' L) := by
  let i : L → S := fun w ↦ ⟨w.val, hLS w.property⟩
  have hi : Measurable i := measurable_subtype_coe.subtype_mk
  have hinc : (κ.comap ((↑) : L → W)).map i =
      (κ.comap ((↑) : S → W)).restrict {w : S | w.val ∈ L} := by
    apply (MeasurableEmbedding.subtype_coe hS).map_injective
    rw [Measure.map_map measurable_subtype_coe hi]
    change (κ.comap ((↑) : L → W)).map ((↑) : L → W) =
      ((κ.comap ((↑) : S → W)).restrict (((↑) : S → W) ⁻¹' L)).map ((↑) : S → W)
    rw [← Measure.restrict_map measurable_subtype_coe hL,
      map_comap_subtype_coe hS, Measure.restrict_restrict_of_subset hLS]
    exact map_comap_subtype_coe hL κ
  have hpre : (fun w : S ↦ a w) ⁻¹' (a '' L) = {w : S | w.val ∈ L} := by
    ext w
    constructor
    · rintro ⟨v, hv, heq⟩
      have hw : (⟨v, hLS hv⟩ : S) = w := ha.injective heq
      change w.val ∈ L
      rw [← hw]
      exact hv
    · intro hw
      exact ⟨w.val, hw, rfl⟩
  unfold labelReferenceOn
  rw [ha.restrict_map, hpre, ← hinc, Measure.map_map ha.measurable hi]
  rfl

/-- The full seed label reference is sigma-finite whenever its Haar reference is. -/
theorem sigmaFinite_labelReferenceOn (κ : Measure W) [SigmaFinite κ]
    {a : W → Z} {S : Set W} (hS : MeasurableSet S)
    (ha : MeasurableEmbedding (fun w : S ↦ a w)) : SigmaFinite (labelReferenceOn κ a S) := by
  have hκ : SigmaFinite (κ.comap ((↑) : S → W)) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by
      rw [map_comap_subtype_coe hS]
      infer_instance)
  exact ha.sigmaFinite_map

/-- Every retained label has the same fixed seed Radon--Nikodym factor; the
statement does not require positivity of either physical population density. -/
theorem ae_rnDeriv_labelReferenceOn_eq (κ : Measure W) [SigmaFinite κ]
    (lambda : Measure Z) [SigmaFinite lambda] {a : W → Z} {S L : Set W}
    (hS : MeasurableSet S) (hL : MeasurableSet L) (hLS : L ⊆ S)
    (ha : MeasurableEmbedding (fun w : S ↦ a w)) :
    ∀ᵐ z ∂lambda, z ∈ a '' L →
      (labelReferenceOn κ a L).rnDeriv lambda z =
        (labelReferenceOn κ a S).rnDeriv lambda z := by
  have : SigmaFinite (labelReferenceOn κ a S) := sigmaFinite_labelReferenceOn κ hS ha
  have hImage : MeasurableSet (a '' L) := by
    have h := ha.measurableSet_image.mpr (hL.preimage measurable_subtype_coe)
    convert h using 1
    ext z
    simp only [mem_image, mem_preimage, Subtype.exists]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hLS hw, hw, rfl⟩
    · rintro ⟨w, _, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [labelReferenceOn_eq_restrict κ hS hL hLS ha]
  filter_upwards [Measure.rnDeriv_restrict (labelReferenceOn κ a S) lambda hImage]
    with z hz
  intro hzL
  rwa [indicator_of_mem hzL] at hz

/-- Exact density restrictions glue on a countable cover. No summability of
local integral bounds is needed or asserted. -/
theorem restrict_eq_withDensity_of_countable_cover {ι : Type*} [Countable ι]
    (μ ν : Measure X) {U : Set X} {I : ι → Set X} (hI : ∀ i, MeasurableSet (I i))
    (hcover : (⋃ i, I i) = U) (d : X → ℝ≥0∞)
    (hlocal : ∀ i, μ.restrict (I i) = (ν.restrict (I i)).withDensity d) :
    μ.restrict U = (ν.restrict U).withDensity d := by
  have hU : MeasurableSet U := hcover ▸ MeasurableSet.iUnion hI
  rw [← restrict_withDensity hU, ← hcover]
  apply Measure.restrict_iUnion_congr.mpr
  intro i
  rw [restrict_withDensity (hI i)]
  exact hlocal i

end OTSelector.Reconstruction

end
end
