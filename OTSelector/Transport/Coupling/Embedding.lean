import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import OTSelector.Probability.EmpiricalMeasure
import OTSelector.Transport.Coupling.CostEquivalence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CompactSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CompactSupport`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two measurable embeddings, actual coupling marginals and a cost preserved on their images; continuity is explicit only for weak-limit transport.

Objects: Unique coupling lift, exact cost/optimal-face transport, subtype support lifting and empirical pushforward identities.

Proof detail: Use marginal support to confine the coupling to the product image, map/comap through the embeddings, change variables in cost and transport the entire competitor set; continuous pushforward gives the weak adapter.

Sources: Gabriel Peyré, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf); D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation (https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61).
Relation: General coupling/measure-embedding consequences, including all 14 selected declarations. The three empirical selector corollaries from the original mixed file are excluded.
-/

/-!
# Compact carriers and the entire ambient optimal-coupling set

A coupling of marginals pushed forward by measurable embeddings is concentrated on the product
of their ranges. Pullback therefore gives a unique coupling of the original marginals. This
establishes a correspondence of all feasible couplings and, under pointwise cost preservation,
of the entire optimal face. Extended costs may be infinite; no optimizer is selected and no
measurability or integrability hypothesis on the cost is added.

For measurable subsets, the pullback represents the original supported probability without
renormalization. Inclusion preserves empirical measures, including repeated observations, and
the subtype distance is exactly the restricted ambient distance. Continuous inclusion transports
weak convergence of entire optimal faces under the same filter. The final theorem transfers a
selector from a compact carrier, such as the union of compact source and target supports, to a
possibly noncompact second-countable metric Borel ambient space.

The compact theorem takes subtype samples and their proved selector convergence as inputs; it
neither supplies the pressure limits nor constructs almost-everywhere versions of ambient random
samples in the subtype. Every ambient coupling of the represented marginals is covered by the
proved inverse, including fractional couplings and ties. No intrinsic path metric on the carrier
is substituted for the ambient distance.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace OTSelector.Reconstruction

variable {α β α' β' : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace α'] [MeasurableSpace β']

/-- Product embeddings preserve and reflect the prescribed marginal constraints. -/
theorem isCoupling_map_embedding_iff {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    {μ : Measure α} {ν : Measure β} {π : Measure (α × β)} :
    Vlasov.IsCoupling (π.map (Prod.map f g)) (μ.map f) (ν.map g) ↔
      Vlasov.IsCoupling π μ ν := by
  constructor
  · intro hπ
    constructor
    · apply hf.map_injective
      calc
        (π.map Prod.fst).map f = (π.map (Prod.map f g)).map Prod.fst := by
          rw [Measure.map_map hf.measurable measurable_fst,
            Measure.map_map measurable_fst (hf.measurable.prodMap hg.measurable)]
          rfl
        _ = μ.map f := hπ.1
    · apply hg.map_injective
      calc
        (π.map Prod.snd).map g = (π.map (Prod.map f g)).map Prod.snd := by
          rw [Measure.map_map hg.measurable measurable_snd,
            Measure.map_map measurable_snd (hf.measurable.prodMap hg.measurable)]
          rfl
        _ = ν.map g := hπ.2
  · exact fun hπ ↦ hπ.map f g hf.measurable hg.measurable

/-- Every ambient coupling is concentrated on the product of the marginal embedding ranges. -/
theorem ae_mem_range_prodMap_of_isCoupling {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    {μ : Measure α} {ν : Measure β} {κ : Measure (α' × β')}
    (hκ : Vlasov.IsCoupling κ (μ.map f) (ν.map g)) :
    ∀ᵐ z ∂κ, z ∈ range (Prod.map f g) := by
  have hleft : ∀ᵐ x ∂μ.map f, x ∈ range f :=
    hf.ae_map_iff.mpr (Eventually.of_forall fun x ↦ mem_range_self x)
  have hright : ∀ᵐ y ∂ν.map g, y ∈ range g :=
    hg.ae_map_iff.mpr (Eventually.of_forall fun y ↦ mem_range_self y)
  rw [← hκ.1] at hleft
  rw [← hκ.2] at hright
  have hleft' := ae_of_ae_map measurable_fst.aemeasurable hleft
  have hright' := ae_of_ae_map measurable_snd.aemeasurable hright
  filter_upwards [hleft', hright'] with z hz₁ hz₂
  rcases hz₁ with ⟨x, hx⟩
  rcases hz₂ with ⟨y, hy⟩
  exact ⟨(x, y), Prod.ext hx hy⟩

/-- Pullback under the product embedding recovers every ambient coupling exactly. -/
theorem map_comap_of_isCoupling {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    {μ : Measure α} {ν : Measure β} {κ : Measure (α' × β')}
    (hκ : Vlasov.IsCoupling κ (μ.map f) (ν.map g)) :
    (κ.comap (Prod.map f g)).map (Prod.map f g) = κ := by
  rw [(hf.prodMap hg).map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (ae_mem_range_prodMap_of_isCoupling hf hg hκ)

/-- All ambient couplings, including fractional couplings, have a unique embedded lift. -/
theorem existsUnique_coupling_lift {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    {μ : Measure α} {ν : Measure β} {κ : Measure (α' × β')}
    (hκ : Vlasov.IsCoupling κ (μ.map f) (ν.map g)) :
    ∃! π : Measure (α × β), Vlasov.IsCoupling π μ ν ∧
      π.map (Prod.map f g) = κ := by
  have heq := map_comap_of_isCoupling hf hg hκ
  refine ⟨κ.comap (Prod.map f g), ⟨?_, heq⟩, ?_⟩
  · apply (isCoupling_map_embedding_iff hf hg).mp
    rwa [heq]
  · intro π hπ
    exact (hf.prodMap hg).map_injective (hπ.2.trans heq.symm)

/-- A pointwise cost identity preserves arbitrary extended-valued costs under embeddings. -/
theorem couplingCost_map_embedding {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (f x) (g y) = cost x y) (π : Measure (α × β)) :
    couplingCost cost' (π.map (Prod.map f g)) = couplingCost cost π := by
  rw [couplingCost, (hf.prodMap hg).lintegral_map]
  exact lintegral_congr fun z ↦ hcost z.1 z.2

/-- Ambient optimality compares against every coupling, all of which lift uniquely. -/
theorem isOptimalCoupling_map_embedding_iff {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (f x) (g y) = cost x y)
    {μ : Measure α} {ν : Measure β} {π : Measure (α × β)} :
    IsOptimalCoupling cost' (μ.map f) (ν.map g) (π.map (Prod.map f g)) ↔
      IsOptimalCoupling cost μ ν π := by
  constructor
  · rintro ⟨hπ, hmin⟩
    refine ⟨(isCoupling_map_embedding_iff hf hg).mp hπ, fun κ hκ ↦ ?_⟩
    have h := hmin (κ.map (Prod.map f g)) ((isCoupling_map_embedding_iff hf hg).mpr hκ)
    simpa only [couplingCost_map_embedding hf hg cost cost' hcost] using h
  · rintro ⟨hπ, hmin⟩
    refine ⟨(isCoupling_map_embedding_iff hf hg).mpr hπ, fun κ hκ ↦ ?_⟩
    obtain ⟨κ₀, ⟨hκ₀, heq⟩, _⟩ := existsUnique_coupling_lift hf hg hκ
    rw [← heq, couplingCost_map_embedding hf hg cost cost' hcost,
      couplingCost_map_embedding hf hg cost cost' hcost]
    exact hmin κ₀ hκ₀

/-- Product pushforward maps the entire optimal face onto the ambient optimal face. -/
theorem image_optimalCouplings_embedding {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (f x) (g y) = cost x y)
    (μ : Measure α) (ν : Measure β) :
    Measure.map (Prod.map f g) '' {π | IsOptimalCoupling cost μ ν π} =
      {κ | IsOptimalCoupling cost' (μ.map f) (ν.map g) κ} := by
  ext κ
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact (isOptimalCoupling_map_embedding_iff hf hg cost cost' hcost).mpr hπ
  · intro hκ
    obtain ⟨π, ⟨_, heq⟩, _⟩ := existsUnique_coupling_lift hf hg hκ.1
    refine ⟨π, ?_, heq⟩
    apply (isOptimalCoupling_map_embedding_iff hf hg cost cost' hcost).mp
    rwa [heq]


/-- Bundled probability couplings have the same entire-face correspondence. -/
theorem image_optimalProbabilityCouplings_embedding {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (f x) (g y) = cost x y)
    (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    (fun π : ProbabilityMeasure (α × β) ↦
      π.map (hf.measurable.prodMap hg.measurable).aemeasurable) ''
        {π | IsOptimalCoupling cost (μ : Measure α) (ν : Measure β) (π : Measure (α × β))} =
      {κ : ProbabilityMeasure (α' × β') |
        IsOptimalCoupling cost' ((μ : Measure α).map f) ((ν : Measure β).map g)
          (κ : Measure (α' × β'))} := by
  ext κ
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact (isOptimalCoupling_map_embedding_iff hf hg cost cost' hcost).mpr hπ
  · intro hκ
    obtain ⟨π, ⟨hπ, heq⟩, _⟩ := existsUnique_coupling_lift hf hg hκ.1
    have : IsProbabilityMeasure (π.map Prod.fst) := by rw [hπ.1]; infer_instance
    have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
    refine ⟨⟨π, inferInstance⟩, ?_, ProbabilityMeasure.toMeasure_injective heq⟩
    apply (isOptimalCoupling_map_embedding_iff hf hg cost cost' hcost).mp
    change IsOptimalCoupling cost' ((μ : Measure α).map f) ((ν : Measure β).map g)
      (π.map (Prod.map f g))
    rwa [heq]

/-- A measure carried by a measurable subset is exactly the pushforward of its subtype pullback. -/
theorem map_comap_subtype_of_ae_mem {s : Set α} (hs : MeasurableSet s)
    {μ : Measure α} (hμ : ∀ᵐ x ∂μ, x ∈ s) :
    (μ.comap ((↑) : s → α)).map ((↑) : s → α) = μ := by
  rw [map_comap_subtype_coe hs]
  exact Measure.restrict_eq_self_of_ae_mem hμ

/-- The same probability on its measurable carrier, without restriction renormalization. -/
noncomputable def probabilityOnSubset (μ : ProbabilityMeasure α) (s : Set α)
    (hs : MeasurableSet s) (hμ : ∀ᵐ x ∂(μ : Measure α), x ∈ s) : ProbabilityMeasure s := by
  let μ₀ := (μ : Measure α).comap ((↑) : s → α)
  have : IsProbabilityMeasure (μ₀.map ((↑) : s → α)) := by
    rw [show μ₀.map ((↑) : s → α) = (μ : Measure α) from
      map_comap_subtype_of_ae_mem hs hμ]
    infer_instance
  exact ⟨μ₀, Measure.isProbabilityMeasure_of_map ((↑) : s → α)⟩



/-- Every ambient coupling of supported marginals has a unique coupling on the two subspaces. -/
theorem existsUnique_subtype_coupling_lift {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    {μ : Measure α} {ν : Measure β}
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ y ∂ν, y ∈ t)
    {κ : Measure (α × β)} (hκ : Vlasov.IsCoupling κ μ ν) :
    ∃! π : Measure (s × t),
      Vlasov.IsCoupling π (μ.comap ((↑) : s → α)) (ν.comap ((↑) : t → β)) ∧
        π.map (Prod.map ((↑) : s → α) ((↑) : t → β)) = κ := by
  apply existsUnique_coupling_lift (MeasurableEmbedding.subtype_coe hs)
    (MeasurableEmbedding.subtype_coe ht)
  rwa [map_comap_subtype_of_ae_mem hs hμ, map_comap_subtype_of_ae_mem ht hν]

/-- Empirical probability measures commute with every measurable map, including inclusion. -/
theorem map_empiricalProbabilityMeasure {n : ℕ} [NeZero n]
    (x : Fin n → α) (f : α → β) (hf : Measurable f) :
    (empiricalProbabilityMeasure x).map hf.aemeasurable =
      empiricalProbabilityMeasure (f ∘ x) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact map_empiricalMeasure x f hf

section Topology
variable [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace α'] [TopologicalSpace β']
  [OpensMeasurableSpace (α × β)] [BorelSpace (α' × β')]

/-- Continuous cost-preserving embeddings transport convergence of entire optimal faces.
No measurable choice of an optimizer, compactness, or finite-cost hypothesis is required. -/
theorem tendsto_optimalProbabilityCouplings_embedding
    {f : α → α'} {g : β → β'}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (hfc : Continuous f) (hgc : Continuous g)
    (cost : α → β → ℝ≥0∞) (cost' : α' → β' → ℝ≥0∞)
    (hcost : ∀ x y, cost' (f x) (g y) = cost x y)
    {ι : Type*} {l : Filter ι}
    (μ : ι → ProbabilityMeasure α) (ν : ι → ProbabilityMeasure β)
    (π : ProbabilityMeasure (α × β))
    (hface : Tendsto
      (fun i ↦ {γ : ProbabilityMeasure (α × β) |
        IsOptimalCoupling cost (μ i : Measure α) (ν i : Measure β) (γ : Measure (α × β))})
      l (𝓝 π).smallSets) :
    Tendsto (fun i ↦ {κ : ProbabilityMeasure (α' × β') |
      IsOptimalCoupling cost' ((μ i : Measure α).map f) ((ν i : Measure β).map g)
        (κ : Measure (α' × β'))}) l
      (𝓝 (π.map (hf.measurable.prodMap hg.measurable).aemeasurable)).smallSets := by
  have hcont := ProbabilityMeasure.continuous_map (hfc.prodMap hgc)
  have h := hcont.continuousAt.image_smallSets.comp hface
  simpa only [Function.comp_def, image_optimalProbabilityCouplings_embedding hf hg cost cost'
    hcost] using h
end Topology


section Distance
variable {M : Type*} [MetricSpace M] [MeasurableSpace M]

/-- The subtype metric is the restricted ambient distance, and preserves every optimal coupling. -/
theorem isOptimalCoupling_map_subtype_edist_iff {s : Set M} (hs : MeasurableSet s)
    {μ ν : Measure s} {π : Measure (s × s)} :
    IsOptimalCoupling edist (μ.map ((↑) : s → M)) (ν.map ((↑) : s → M))
      (π.map (Prod.map ((↑) : s → M) ((↑) : s → M))) ↔
        IsOptimalCoupling edist μ ν π :=
  isOptimalCoupling_map_embedding_iff (MeasurableEmbedding.subtype_coe hs)
    (MeasurableEmbedding.subtype_coe hs) edist edist (fun _ _ ↦ rfl)


end Distance



end OTSelector.Reconstruction

end
