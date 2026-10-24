import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
## Lemma skeleton

* **Conditions:** Joint label-scalar absolute continuity and a measurable target event with countable scalar sections; carrier versions supply measurable embeddings to ensure image measurability.
* **Objects:** Nullity of the target event and its original-space preimages, with single-clock-per-label as a special case.
* **Proof detail:** Countable real sections are Lebesgue-null; apply the null-section product principle and absolute continuity. For images, use the measurable embedding and pull back the null image event.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Corollary 252F, p. 24.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=24
* D. H. Fremlin, *Measure Theory, Volume 4*, Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
  https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Null sections plus measurable-image transport. Infinite measures are permitted; the measurable embedding is essential for the stated image measurability route.
-/

/-!
# Null sets with countable clock sections under joint absolute continuity

A measure absolutely continuous with respect to a label measure times Lebesgue
measure vanishes on measurable sets with countable scalar sections. Applying this
to the actual label-clock image gives nullity for the same original measure. A
measurable embedding on a carrier supplies the image measurability. All measures
may be infinite; an application to Haar measure must explicitly use that measure.
-/

open Set Filter MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- Joint absolute continuity makes every measurable set with countable Lebesgue
sections null, for an arbitrary label measure and arbitrary total mass. -/
theorem measure_eq_zero_of_countable_scalar_sections
    (ρ : Measure (Z × ℝ)) (η : Measure Z) (hac : ρ ≪ η.prod volume)
    {B : Set (Z × ℝ)} (hB : MeasurableSet B)
    (hsections : ∀ z, (Prod.mk z ⁻¹' B).Countable) : ρ B = 0 := by
  apply hac
  apply Measure.measure_prod_null_of_ae_null hB
  exact Filter.Eventually.of_forall (fun z ↦ (hsections z).measure_zero volume)

/-- A measurable label-clock image with countable sections is null for the same
original measure. Only almost-everywhere measurability of the actual pair is needed. -/
theorem measure_eq_zero_of_countable_labelClock_image_sections
    (ν : Measure M) {a : M → Z} {u : M → ℝ}
    (hpair : AEMeasurable (fun x ↦ (a x, u x)) ν)
    (hac : ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume)
    {S : Set M} (himage : MeasurableSet ((fun x ↦ (a x, u x)) '' S))
    (hsections : ∀ z, (Prod.mk z ⁻¹' ((fun x ↦ (a x, u x)) '' S)).Countable) :
    ν S = 0 := by
  have hnull := measure_eq_zero_of_countable_scalar_sections
    (ν.map (fun x ↦ (a x, u x))) (ν.map a) hac himage hsections
  rw [Measure.map_apply_of_aemeasurable hpair himage] at hnull
  exact measure_mono_null (subset_preimage_image _ _) hnull

private theorem measurableSet_labelClock_image_of_embedding
    {a : M → Z} {u : M → ℝ} {N S : Set M} (hS : MeasurableSet S) (hSN : S ⊆ N)
    (hemb : MeasurableEmbedding (fun x : N ↦ (a x.val, u x.val))) :
    MeasurableSet ((fun x ↦ (a x, u x)) '' S) := by
  have heq : (fun x ↦ (a x, u x)) '' S =
      (fun x : N ↦ (a x.val, u x.val)) '' ((↑) : N → M) ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSN hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
  rw [heq]
  exact hemb.measurableSet_image.mpr (hS.preimage measurable_subtype_coe)

/-- A measurable embedding on a regular carrier supplies the measurable image
needed to remove every measurable subset with countable clock sections. -/
theorem measure_eq_zero_of_countable_labelClock_sections
    (ν : Measure M) {a : M → Z} {u : M → ℝ}
    (ha : AEMeasurable a ν) (hu : AEMeasurable u ν)
    (hac : ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume)
    {S N : Set M} (hS : MeasurableSet S) (hSN : S ⊆ N)
    (hemb : MeasurableEmbedding (fun x : N ↦ (a x.val, u x.val)))
    (hsections : ∀ z, (Prod.mk z ⁻¹' ((fun x ↦ (a x, u x)) '' S)).Countable) :
    ν S = 0 :=
  measure_eq_zero_of_countable_labelClock_image_sections ν (ha.prodMk hu) hac
    (measurableSet_labelClock_image_of_embedding hS hSN hemb) hsections

/-- A measurable subset with at most one actual clock value per label is null for
the given measure. The conclusion preserves that measure, including Haar restrictions. -/
theorem measure_eq_zero_of_single_clock_per_label
    (ν : Measure M) {a : M → Z} {u : M → ℝ}
    (ha : AEMeasurable a ν) (hu : AEMeasurable u ν)
    (hac : ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume)
    {S N : Set M} (hS : MeasurableSet S) (hSN : S ⊆ N)
    (hemb : MeasurableEmbedding (fun x : N ↦ (a x.val, u x.val)))
    (hclock : ∀ x ∈ S, ∀ y ∈ S, a x = a y → u x = u y) : ν S = 0 := by
  apply measure_eq_zero_of_countable_labelClock_sections ν ha hu hac hS hSN hemb
  intro z
  apply Set.Subsingleton.countable
  intro s hs t ht
  obtain ⟨x, hx, hxs⟩ := hs
  obtain ⟨y, hy, hyt⟩ := ht
  have hxy : a x = a y := (congrArg Prod.fst hxs).trans (congrArg Prod.fst hyt).symm
  exact (congrArg Prod.snd hxs).symm.trans
    ((hclock x hx y hy hxy).trans (congrArg Prod.snd hyt))

end OTSelector.Reconstruction
