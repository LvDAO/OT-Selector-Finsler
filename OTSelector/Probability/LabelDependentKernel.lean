import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Label Dependent Kernel

Conditions: An s-finite kernel κ and base law Λ; a jointly measurable label-dependent coordinate map b. For preservation of probability, κ is Markov.

Objects: The actual fiberwise pushforward z ↦ (κ z).map (x ↦ b(z,x)), its mixture, and its nonnegative iterated-integral identity.

Proof detail: Retain the label with Kernel.id×κ, map the pair through b, and use kernel composition/product integration identities.

Relation to primary sources: This is a local coordinate-change construction from measurable families. The definition is totalized; its evaluation, probability, and mixture identities explicitly require joint measurability. The s-finite extended-integral form is a mathlib generalization of the finite source statement.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
-/
/-!
# Measurable changes of coordinates depending on a conditioning label

A jointly measurable coordinate map pushes forward each conditional measure using
its own label. The construction preserves probability kernels and makes the resulting
mixture equal to the pushforward of the original joint label-coordinate measure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]

/-- Push a conditional kernel forward by a jointly measurable, label-dependent map. -/
def mapWithLabel (κ : Kernel Z A) (b : Z × A → B) : Kernel Z B :=
  (Kernel.id ×ₖ κ).map b

/-- The constructed kernel is the actual pushforward at each original label. -/
theorem mapWithLabel_apply (κ : Kernel Z A) [IsSFiniteKernel κ]
    {b : Z × A → B} (hb : Measurable b) (z : Z) :
    mapWithLabel κ b z = (κ z).map (fun x ↦ b (z, x)) := by
  rw [mapWithLabel, Kernel.map_apply _ hb, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hb measurable_prodMk_left]
  rfl

/-- Label-dependent measurable coordinate changes preserve conditional probability laws. -/
theorem isMarkovKernel_mapWithLabel (κ : Kernel Z A) [IsMarkovKernel κ]
    {b : Z × A → B} (hb : Measurable b) : IsMarkovKernel (mapWithLabel κ b) := by
  unfold mapWithLabel
  exact Kernel.IsMarkovKernel.map _ hb

/-- Mixing after the label-dependent coordinate change pushes forward the actual joint law. -/
theorem mapWithLabel_comp (κ : Kernel Z A) [IsSFiniteKernel κ]
    (Λ : Measure Z) [SFinite Λ] {b : Z × A → B} (hb : Measurable b) :
    mapWithLabel κ b ∘ₘ Λ = (Λ ⊗ₘ κ).map b := by
  rw [mapWithLabel, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hb]

/-- The same coordinate change gives the exact iterated-integral reconstruction. -/
theorem lintegral_mapWithLabel_comp (κ : Kernel Z A) [IsSFiniteKernel κ]
    (Λ : Measure Z) [SFinite Λ] {b : Z × A → B} (hb : Measurable b)
    {f : B → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂mapWithLabel κ b ∘ₘ Λ) = ∫⁻ z, ∫⁻ x, f (b (z, x)) ∂κ z ∂Λ := by
  rw [mapWithLabel_comp κ Λ hb, lintegral_map hf hb]
  exact Measure.lintegral_compProd (hf.comp hb)

end OTSelector.Reconstruction
