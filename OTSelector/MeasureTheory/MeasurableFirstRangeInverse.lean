import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Map

/-!
## Lemma skeleton

* **Conditions:** Countably many measurable embeddings e_n into a common label space; the coverage transfer also has a measurable label map and seed maps carrying the stated label identity.
* **Objects:** Conull label-range coverage and a measurable inverse into the first eligible embedded range, including empty domains.
* **Proof detail:** Push the almost-everywhere window cover to labels. Disjointify the countable measurable embedded ranges and restrict each embedding’s measurable inverse to its first-range piece.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4, Appendix*, Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
  https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32
* D. H. Fremlin, *Measure Theory, Volume 4*, Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
  https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Explicit countable first-index selection, using already supplied measurable embeddings. It requires no general measurable-selection theorem or analytic-set projection.
-/

/-!
# Measurable selection of seeds on existing label classes

Countable window coverage transfers to the original label law when every window
point has an eligible seed of the same label. Disjointing the seed-label ranges
then selects their first eligible index. Each selected piece has a measurable
inverse into its seed domain, including when some seed domains are empty.
-/

open Set MeasureTheory Filter

noncomputable section
namespace OTSelector.Reconstruction

/-- An almost-everywhere window cover and its label identity cover the original
label law by the measurable seed-label ranges. Window parameters need no measurable space. -/
theorem ae_mem_label_ranges_of_ae_window_cover
    {ι M Z : Type*} [Countable ι] [MeasurableSpace M] [MeasurableSpace Z]
    {W : ι → Type*} [∀ i, MeasurableSpace (W i)] {D : ι → Type*}
    (μ : Measure M) (a : M → Z) (ha : Measurable a)
    (f : ∀ i, D i → M) (r : ∀ i, D i → W i) (e : ∀ i, W i → Z)
    (he : ∀ i, MeasurableEmbedding (e i))
    (hlabel : ∀ i z, a (f i z) = e i (r i z))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, Set.range (f i)) :
    ∀ᵐ z ∂μ.map a, z ∈ ⋃ i, Set.range (e i) := by
  have hC : MeasurableSet (⋃ i, Set.range (e i)) :=
    MeasurableSet.iUnion fun i ↦ (he i).measurableSet_range
  apply (ae_map_iff ha.aemeasurable hC).mpr
  filter_upwards [hcover] with x hx
  obtain ⟨i, z, rfl⟩ := mem_iUnion.mp hx
  rw [hlabel]
  exact mem_iUnion.mpr ⟨i, mem_range_self _⟩

/-- The first eligible measurable seed range gives a disjoint label partition
and a measurable inverse on each piece, without requiring nonempty seed domains. -/
theorem exists_measurable_first_range_inverse
    {Z : Type*} [MeasurableSpace Z]
    {W : ℕ → Type*} [∀ n, MeasurableSpace (W n)]
    (e : ∀ n, W n → Z) (he : ∀ n, MeasurableEmbedding (e n)) :
    let B : ℕ → Set Z := disjointed (fun n ↦ Set.range (e n))
    (∀ n, MeasurableSet (B n)) ∧
    Pairwise (fun n k ↦ Disjoint (B n) (B k)) ∧
    (∀ n, B n ⊆ Set.range (e n)) ∧
    (⋃ n, B n) = (⋃ n, Set.range (e n)) ∧
    ∃ w : ∀ n, B n → W n,
      (∀ n, Measurable (w n)) ∧ ∀ n z, e n (w n z) = z.val := by
  dsimp only
  have hsub := disjointed_subset (fun n ↦ Set.range (e n))
  refine ⟨MeasurableSet.disjointed (fun n ↦ (he n).measurableSet_range),
    disjoint_disjointed _, hsub, iUnion_disjointed, ?_⟩
  refine ⟨fun n z ↦ (he n).equivRange.symm ⟨z.val, hsub n z.property⟩, ?_, ?_⟩
  · intro n
    exact (he n).equivRange.symm.measurable.comp measurable_subtype_coe.subtype_mk
  · intro n z
    simpa only [MeasurableEmbedding.equivRange_apply] using
      congrArg Subtype.val ((he n).equivRange.apply_symm_apply ⟨z.val, hsub n z.property⟩)

end OTSelector.Reconstruction
