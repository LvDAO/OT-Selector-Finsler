import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
## Lemma skeleton

* **Conditions:** Compact ambient space, continuous probes, eventually nonempty faces and uniform readout limits.
* **Objects:** A point or probability measure realizing all limiting readouts.
* **Proof detail:** Choose a compact cluster point of the faces, identify its probes, then use continuous-integral uniqueness.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=68
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47

**Relationship to the sources:** The arbitrary-filter uniform-face theorem is a locally proved compactness corollary; measure existence/uniqueness uses the cited compactness and Riesz principles.
-/

/-!
# Constructing a probability measure from uniform readouts

On a compact space, uniform limits of continuous probes on eventually nonempty sets are
realized by an actual point. Applying this fact to probability measures constructs a measure
from its bounded-continuous integral readouts; the target measure is not an input. Uniqueness
uses `HasOuterApproxClosed`, which holds in particular on metrizable spaces. The index filter
is arbitrary and nontrivial; no sequential or countable-generation assumption is used.
-/

open Filter MeasureTheory Set
open BoundedContinuousFunction
open scoped Topology

namespace OTSelector.Reconstruction

/-- Uniform limits of continuous real probes on eventually nonempty subsets of a compact space
are simultaneously attained at an actual point. No separation of points by probes is assumed. -/
theorem exists_point_of_uniform_readout
    {X ι Probe : Type*} [TopologicalSpace X] [CompactSpace X]
    {l : Filter ι} [NeBot l] (face : ι → Set X) (probe : Probe → X → ℝ)
    (hcontinuous : ∀ f, Continuous (probe f)) (readout : Probe → ℝ)
    (hnonempty : ∀ᶠ z in l, (face z).Nonempty)
    (hreadout : ∀ f ε, 0 < ε → ∀ᶠ z in l,
      ∀ x ∈ face z, |probe f x - readout f| < ε) :
    ∃ x : X, ∀ f, probe f x = readout f := by
  obtain ⟨select, hselect⟩ := hnonempty.choice
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace (Filter.map select l)
  refine ⟨x, fun f ↦ ?_⟩
  have hlimit : Tendsto (probe f ∘ select) l (𝓝 (readout f)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hselect, hreadout f ε hε] with z hz hbound
    simpa only [Function.comp_apply, Real.dist_eq] using hbound (select z) hz
  have hcluster : MapClusterPt (probe f x) l (probe f ∘ select) :=
    (show MapClusterPt x l select from hx).continuousAt_comp (hcontinuous f).continuousAt
  exact eq_of_nhds_neBot (hcluster.clusterPt.mono hlimit)

/-- On a compact Hausdorff Borel space, uniform limits of all bounded-continuous integrals
on eventually nonempty faces are represented by a probability measure. No representing measure
or algebraic properties of the readout functional are assumed in advance. -/
theorem exists_probabilityMeasure_of_uniform_readout
    {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E] [T2Space E] [BorelSpace E]
    [CompactSpace E] {l : Filter ι} [NeBot l]
    (face : ι → Set (ProbabilityMeasure E)) (readout : (E →ᵇ ℝ) → ℝ)
    (hnonempty : ∀ᶠ z in l, (face z).Nonempty)
    (hreadout : ∀ (f : E →ᵇ ℝ) ε, 0 < ε → ∀ᶠ z in l,
      ∀ μ ∈ face z, |(∫ x, f x ∂(μ : Measure E)) - readout f| < ε) :
    ∃ μ : ProbabilityMeasure E, ∀ f : E →ᵇ ℝ,
      ∫ x, f x ∂(μ : Measure E) = readout f := by
  exact exists_point_of_uniform_readout face
    (fun f μ ↦ ∫ x, f x ∂(μ : Measure E))
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction readout hnonempty hreadout

/-- If closed sets admit bounded-continuous outer approximations, the probability measure
constructed from uniform readouts is unique. This extra separation hypothesis is automatic on
metrizable spaces, including compact support subtypes in metric manifolds. -/
theorem existsUnique_probabilityMeasure_of_uniform_readout
    {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E] [T2Space E] [BorelSpace E]
    [CompactSpace E] [HasOuterApproxClosed E] {l : Filter ι} [NeBot l]
    (face : ι → Set (ProbabilityMeasure E)) (readout : (E →ᵇ ℝ) → ℝ)
    (hnonempty : ∀ᶠ z in l, (face z).Nonempty)
    (hreadout : ∀ (f : E →ᵇ ℝ) ε, 0 < ε → ∀ᶠ z in l,
      ∀ μ ∈ face z, |(∫ x, f x ∂(μ : Measure E)) - readout f| < ε) :
    ∃! μ : ProbabilityMeasure E, ∀ f : E →ᵇ ℝ,
      ∫ x, f x ∂(μ : Measure E) = readout f := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_uniform_readout face readout hnonempty hreadout
  refine ⟨μ, hμ, fun ν hν ↦ ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact (hν f).trans (hμ f).symm

end OTSelector.Reconstruction
