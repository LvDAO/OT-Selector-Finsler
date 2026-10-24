import OTSelector.Transport.Coupling.Embedding
import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Limit.EmpiricalPressureSelector
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Order.Filter.SmallSets

/-!
Conditions: Subtype/compact carrier support and cost-preserving inclusion; carrier selector convergence and population optimality are explicit inputs.

Objects: Image and whole-face convergence of empirical optima under inclusion, and transport of the supplied carrier optimum to the original ambient space.

Proof detail: Apply generic coupling lift, cost and whole-competitor-set identities, simplify empirical pushforwards and use continuity of inclusion under the same filter.

Sources: Gabriel Peyré; Marco Cuturi, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation (https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61).
Relation: Derived empirical adapters for generic coupling transport. They transfer a supplied carrier selector; they do not independently prove selector existence or a pressure theorem.
-/


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






















/-- Inclusion returns the original ambient probability exactly. -/
@[simp] theorem map_probabilityOnSubset (μ : ProbabilityMeasure α) (s : Set α)
    (hs : MeasurableSet s) (hμ : ∀ᵐ x ∂(μ : Measure α), x ∈ s) :
    (probabilityOnSubset μ s hs hμ).map measurable_subtype_coe.aemeasurable = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  exact map_comap_subtype_of_ae_mem hs hμ





section Topology
variable [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace α'] [TopologicalSpace β']
  [OpensMeasurableSpace (α × β)] [BorelSpace (α' × β')]


end Topology


section Distance
variable {M : Type*} [MetricSpace M] [MeasurableSpace M]



/-- Every optimal empirical probability coupling in the ambient space comes from the subtype.
Repeated observations are allowed; the image equality concerns the entire fractional face. -/
theorem image_empiricalOptimalFace_subtype {s : Set M} (hs : MeasurableSet s)
    {n : ℕ} [NeZero n] (X Y : Fin n → s) :
    (fun π : ProbabilityMeasure (s × s) ↦
      π.map (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable) ''
        Pressure.empiricalOptimalFace X Y =
      Pressure.empiricalOptimalFace (fun i ↦ (X i : M)) (fun i ↦ (Y i : M)) := by
  have h := image_optimalProbabilityCouplings_embedding
    (MeasurableEmbedding.subtype_coe hs) (MeasurableEmbedding.subtype_coe hs)
    edist edist (fun _ _ ↦ rfl) (empiricalProbabilityMeasure X) (empiricalProbabilityMeasure Y)
  simpa only [Pressure.empiricalOptimalFace, empiricalProbabilityMeasure_toMeasure,
    map_empiricalMeasure _ _ measurable_subtype_coe, Function.comp_def] using h
end Distance

section Metric
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Inclusion transports convergence of every empirical optimum to the ambient metric space,
under the same filter (in particular the original row-probability filter). -/
theorem tendsto_empiricalOptimalFace_subtype {s : Set M} (hs : MeasurableSet s)
    {ι : Type*} {l : Filter ι} (n : ι → ℕ) [∀ i, NeZero (n i)]
    (X Y : ∀ i, Fin (n i) → s) (π : ProbabilityMeasure (s × s))
    (hface : Tendsto (fun i ↦ Pressure.empiricalOptimalFace (X i) (Y i))
      l (𝓝 π).smallSets) :
    Tendsto
      (fun i ↦ Pressure.empiricalOptimalFace
        (fun j ↦ (X i j : M)) (fun j ↦ (Y i j : M))) l
      (𝓝 (π.map
        (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable)).smallSets := by
  have h := tendsto_optimalProbabilityCouplings_embedding
    (MeasurableEmbedding.subtype_coe hs) (MeasurableEmbedding.subtype_coe hs)
    continuous_subtype_val continuous_subtype_val edist edist (fun _ _ ↦ rfl)
    (fun i ↦ empiricalProbabilityMeasure (X i)) (fun i ↦ empiricalProbabilityMeasure (Y i))
    π hface
  simpa only [Pressure.empiricalOptimalFace, empiricalProbabilityMeasure_toMeasure,
    map_empiricalMeasure _ _ measurable_subtype_coe, Function.comp_def] using h

/-- A selector proved on a compact carrier gives population optimality and convergence of the
entire empirical optimal set in the original, possibly noncompact ambient space. The carrier
may be the union of two compact supports and always uses the restricted ambient distance. -/
theorem compact_support_selector_transport (K : Set M) (hK : IsCompact K)
    (μ ν : ProbabilityMeasure M)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} {l : Filter ι} (n : ι → ℕ) [∀ i, NeZero (n i)]
    (X Y : ∀ i, Fin (n i) → K) (π : ProbabilityMeasure (K × K))
    (hπ : IsOptimalCoupling edist
      (probabilityOnSubset μ K hK.measurableSet hμ : Measure K)
      (probabilityOnSubset ν K hK.measurableSet hν : Measure K) (π : Measure (K × K)))
    (hface : Tendsto (fun i ↦ Pressure.empiricalOptimalFace (X i) (Y i))
      l (𝓝 π).smallSets) :
    IsOptimalCoupling edist (μ : Measure M) (ν : Measure M)
        ((π.map (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable :
          ProbabilityMeasure (M × M)) : Measure (M × M)) ∧
      Tendsto
        (fun i ↦ Pressure.empiricalOptimalFace
          (fun j ↦ (X i j : M)) (fun j ↦ (Y i j : M))) l
        (𝓝 (π.map
        (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable)).smallSets := by
  constructor
  · have h := (isOptimalCoupling_map_subtype_edist_iff hK.measurableSet).mpr hπ
    change IsOptimalCoupling edist
      (((μ : Measure M).comap ((↑) : K → M)).map ((↑) : K → M))
      (((ν : Measure M).comap ((↑) : K → M)).map ((↑) : K → M))
      ((π : Measure (K × K)).map (Prod.map ((↑) : K → M) ((↑) : K → M))) at h
    rw [map_comap_subtype_of_ae_mem hK.measurableSet hμ,
      map_comap_subtype_of_ae_mem hK.measurableSet hν] at h
    exact h
  · exact tendsto_empiricalOptimalFace_subtype hK.measurableSet n X Y π hface
end Metric

end OTSelector.Reconstruction
