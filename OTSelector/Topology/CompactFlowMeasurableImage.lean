import OTSelector.MeasureTheory.HaarLipschitzDistortion
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CompactFlowMeasurableImage.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CompactFlowMeasurableImage`; the selected original proof blocks follow. -/
section

/-!
Conditions: A compact time/seed domain, continuous skew flow retaining the time coordinate and injective time slices; a small-displacement variant gives slice injectivity.

Objects: Closed and measurable compact flow images and measurable embeddings.

Proof detail: Use equality of the retained time coordinate to reduce injectivity to each slice, then compact-to-Hausdorff closed embedding; derive injectivity from the stated Lipschitz perturbation bound.

Sources: Terence Tao, Section 1.8.1, Lemma 1.8.1 and Corollary 1.8.2, p. 102 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=111); D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30).
Relation: Compact embedding corollary; no ODE existence or uniqueness is asserted.
-/

/-!
# Measurable images of compact flow slabs

A continuous family injective on each compact spatial slice gives a closed embedding
when the time coordinate is retained. Its Borel image and measurable inverse then
follow from the existing closed-embedding theorem. A half-Lipschitz displacement is
one sufficient source of the required slice injectivity.
-/

open Set MeasureTheory Topology

noncomputable section
namespace OTSelector.Geometry

section Topological

variable {E : Type*} [TopologicalSpace E] [T2Space E]

/-- Retaining time turns a continuous family of injective compact slices into an
actual closed embedding of the compact time-space slab. -/
theorem isClosedEmbedding_compact_skewFlow {I : Set ℝ} {K : Set E}
    (hI : IsCompact I) (hK : IsCompact K) {T : ℝ → E → E}
    (hT : ContinuousOn (fun q : ℝ × E ↦ (q.1, T q.1 q.2)) (I ×ˢ K))
    (hinj : ∀ t ∈ I, InjOn (T t) K) :
    IsClosedEmbedding (fun q : I × K ↦ ((q.1 : ℝ), T q.1 q.2)) := by
  let _instCompactSkewTime : CompactSpace I := isCompact_iff_compactSpace.mp hI
  let _instCompactSkewSpace : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun q : I × K ↦ ((q.1 : ℝ), T q.1 q.2)) :=
    hT.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun q ↦ ⟨q.1.property, q.2.property⟩)
  apply hc.isClosedEmbedding
  rintro ⟨s, x⟩ ⟨t, y⟩ h
  have hst : s = t := Subtype.ext (congrArg Prod.fst h)
  subst t
  have hxy : x = y :=
    Subtype.ext (hinj s s.property x.property y.property (congrArg Prod.snd h))
  exact Prod.ext rfl hxy

variable [MeasurableSpace E] [BorelSpace E]

/-- The same genuine compact flow slab has a measurable image and measurable inverse
onto its image, with no separate measurability assumption on the image. -/
theorem measurableEmbedding_compact_skewFlow {I : Set ℝ} {K : Set E}
    (hI : IsCompact I) (hK : IsCompact K) {T : ℝ → E → E}
    (hT : ContinuousOn (fun q : ℝ × E ↦ (q.1, T q.1 q.2)) (I ×ˢ K))
    (hinj : ∀ t ∈ I, InjOn (T t) K) :
    MeasurableEmbedding (fun q : I × K ↦ ((q.1 : ℝ), T q.1 q.2)) :=
  (isClosedEmbedding_compact_skewFlow hI hK hT hinj).measurableEmbedding

end Topological

section Normed

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Half-Lipschitz displacement on an ambient domain supplies slice injectivity on
every compact subset, hence the measurable embedding needed for flow-image integration. -/
theorem measurableEmbedding_compact_skewFlow_of_half_lipschitz_displacement
    {I : Set ℝ} {K S : Set E} (hI : IsCompact I) (hK : IsCompact K) (hKS : K ⊆ S)
    {T : ℝ → E → E}
    (hT : ContinuousOn (fun q : ℝ × E ↦ (q.1, T q.1 q.2)) (I ×ˢ K))
    (hres : ∀ t ∈ I, LipschitzOnWith (1 / 2) (fun x ↦ T t x - x) S) :
    MeasurableEmbedding (fun q : I × K ↦ ((q.1 : ℝ), T q.1 q.2)) := by
  apply measurableEmbedding_compact_skewFlow hI hK hT
  intro t ht
  exact (injOn_iff_injective.mpr
    (antilipschitzWith_of_half_lipschitz_displacement (hres t ht)).injective).mono hKS

end Normed
end OTSelector.Geometry

end
end
