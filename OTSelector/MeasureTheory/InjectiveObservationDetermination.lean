import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular

/-!
## Lemma skeleton

* **Conditions:** Measurable observation injective on a common full-measure measurable carrier, under the inherited Polish/Borel setup; compact-test version uses finite measures and the locally compact observed target.
* **Objects:** Equality of original measures from equal observed laws, countably localized restriction equality, or equal compact-test observations.
* **Proof detail:** Lusin–Souslin makes carrier-piece images measurable; pushforward equality then identifies every original measurable event modulo the null carrier complement. Compact tests determine the observed laws by RMK; countable restrictions are assembled modulo a null cover complement.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
  https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Observation-determination and countable gluing corollaries. Global injectivity outside the full carrier is unnecessary.
-/

/-!
# Recovery of finite measures from an injective observation on a full carrier

The observation can fail to be injective away from the common measurable carrier. Lusin–Souslin
makes the image of each measurable carrier piece measurable, so equality of observed measures
recovers the original measures. Compact tests determine the observed finite measures by RMK.
-/

open MeasureTheory Set TopologicalSpace
open scoped CompactlySupported

namespace OTSelector.Reconstruction

variable {S T : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace T] [MeasurableSpace.CountablySeparated T]

/-- Equal pushforwards recover measures supported on a common measurable injectivity carrier.
Finiteness of the original measures is unnecessary for this implication. -/
theorem measure_eq_of_map_eq_of_injOn_ae
    {f : S → T} {D : Set S} (hf : Measurable f) (hD : MeasurableSet D)
    (hinj : InjOn f D) {π₀ π₁ : Measure S}
    (hπ₀ : ∀ᵐ x ∂π₀, x ∈ D) (hπ₁ : ∀ᵐ x ∂π₁, x ∈ D)
    (hmap : π₀.map f = π₁.map f) : π₀ = π₁ := by
  ext A hA
  have hImage : MeasurableSet (f '' (A ∩ D)) :=
    (hA.inter hD).image_of_measurable_injOn hf (hinj.mono inter_subset_right)
  have hpreimage (π : Measure S) (hπ : ∀ᵐ x ∂π, x ∈ D) :
      π (f ⁻¹' (f '' (A ∩ D))) = π A := by
    apply measure_congr
    filter_upwards [hπ] with x hx
    apply propext
    change (f x ∈ f '' (A ∩ D)) ↔ x ∈ A
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := hinj hy.2 hx hyx
      simpa only [hyx'] using hy.1
    · intro hxA
      exact ⟨x, ⟨hxA, hx⟩, rfl⟩
  calc
    π₀ A = π₀ (f ⁻¹' (f '' (A ∩ D))) := (hpreimage π₀ hπ₀).symm
    _ = π₀.map f (f '' (A ∩ D)) := (Measure.map_apply hf hImage).symm
    _ = π₁.map f (f '' (A ∩ D)) := congrArg (fun μ : Measure T ↦ μ _) hmap
    _ = π₁ (f ⁻¹' (f '' (A ∩ D))) := Measure.map_apply hf hImage
    _ = π₁ A := hpreimage π₁ hπ₁

omit [StandardBorelSpace S] in
/-- Equality on countably many restrictions covering both measures almost everywhere recovers
both measures. No disjointness, measurability, or finiteness assumptions on the pieces are needed. -/
theorem measure_eq_of_restrict_eq_on_ae_iUnion
    {ι : Type*} [Countable ι] {D : ι → Set S} {π₀ π₁ : Measure S}
    (hπ₀ : ∀ᵐ x ∂π₀, x ∈ ⋃ j, D j) (hπ₁ : ∀ᵐ x ∂π₁, x ∈ ⋃ j, D j)
    (hrestrict : ∀ j, π₀.restrict (D j) = π₁.restrict (D j)) : π₀ = π₁ := by
  calc
    π₀ = π₀.restrict (⋃ j, D j) := (Measure.restrict_eq_self_of_ae_mem hπ₀).symm
    _ = π₁.restrict (⋃ j, D j) := Measure.restrict_iUnion_congr.mpr hrestrict
    _ = π₁ := Measure.restrict_eq_self_of_ae_mem hπ₁

variable [TopologicalSpace T] [T2Space T] [LocallyCompactSpace T]
  [PseudoMetrizableSpace T] [SigmaCompactSpace T] [BorelSpace T]

/-- Equality of all compact continuous observation tests recovers finite measures supported on a
common measurable carrier where the observation is injective. -/
theorem measure_eq_of_compactProbe_integral_eq_of_injOn_ae
    {f : S → T} {D : Set S} (hf : Measurable f) (hD : MeasurableSet D)
    (hinj : InjOn f D) {π₀ π₁ : Measure S} [IsFiniteMeasure π₀] [IsFiniteMeasure π₁]
    (hπ₀ : ∀ᵐ x ∂π₀, x ∈ D) (hπ₁ : ∀ᵐ x ∂π₁, x ∈ D)
    (htest : ∀ g : C_c(T, ℝ), ∫ x, g (f x) ∂π₀ = ∫ x, g (f x) ∂π₁) :
    π₀ = π₁ := by
  apply measure_eq_of_map_eq_of_injOn_ae hf hD hinj hπ₀ hπ₁
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  calc
    ∫ x, g x ∂π₀.map f = ∫ x, g (f x) ∂π₀ :=
      integral_map (f := fun x ↦ g x) hf.aemeasurable g.continuous.aestronglyMeasurable
    _ = ∫ x, g (f x) ∂π₁ := htest g
    _ = ∫ x, g x ∂π₁.map f :=
      (integral_map (f := fun x ↦ g x) hf.aemeasurable
        g.continuous.aestronglyMeasurable).symm

end OTSelector.Reconstruction
