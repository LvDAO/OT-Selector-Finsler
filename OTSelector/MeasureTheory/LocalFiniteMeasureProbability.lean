import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.MeasureTheory.LocalFiniteMeasureTightness

/-!
## Lemma skeleton

* **Conditions:** For the generic result: a Hausdorff separable pseudometrizable Borel carrier and tight probability laws. For locally finite measures: the established locally compact sigma-compact metrizable base and uniform finite local first moments on covering open windows or a compact exhaustion.
* **Objects:** A probability-law limit and a strictly increasing weakly convergent subsequence on the same constructed carrier.
* **Proof detail:** Use tightness for relative compactness, metrizability for sequential compactness, then apply the existing local-mass tightness theorem. Exhaustion interiors supply windows covering every compact set.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Proposition 437P(a)–(b), pp. 66–67, and Theorem 437R(g)–(h), p. 68 and following proof.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=66
* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4
* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37

**Relationship to the sources:** Forward Prokhorov compactness plus previously proved vague-carrier tightness. The first generic theorem does not assume a complete metric on the original carrier.
-/

/-!
# Weak subsequences of diffuse transport-plan laws

The proved Polish compact-test carrier and actual local mass moments supply
Prokhorov compactness. Tightness is derived from the original moment bounds;
no limiting law or compactness oracle is introduced.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

/-- Mathlib's Prokhorov theorem supplies subsequences on a metrizable law space. -/
theorem exists_tendsto_subseq_probabilityMeasure_of_isTight
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [T2Space S] [PseudoMetrizableSpace S] [SeparableSpace S]
    (P : ℕ → ProbabilityMeasure S)
    (htight : IsTightMeasureSet (range (fun n ↦ (P n : Measure S)))) :
    ∃ Q : ProbabilityMeasure S, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (P ∘ φ) atTop (𝓝 Q) := by
  have htight' : IsTightMeasureSet
      {((Q : ProbabilityMeasure S) : Measure S) | Q ∈ range P} := by
    convert htight using 1
    ext ν
    simp
  have hcompact := isCompact_closure_of_isTightMeasureSet htight'
  obtain ⟨Q, _, φ, hφ, hlim⟩ := hcompact.isSeqCompact
    (fun n ↦ subset_closure (mem_range_self n))
  exact ⟨Q, φ, hφ, hlim⟩

namespace LocalFiniteMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

/-- Original local mass bounds imply an actual weakly convergent subsequence of
the laws of diffuse plans. -/
theorem exists_tendsto_subseq_of_lintegral_localMass_le
    (P : ℕ → ProbabilityMeasure (LocalFiniteMeasure X))
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hcover : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ U n)
    (b : ℕ → ℝ≥0∞) (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ i n, ∫⁻ μ, (μ : Measure X) (U n)
      ∂(P i : Measure (LocalFiniteMeasure X)) ≤ b n) :
    ∃ Q : ProbabilityMeasure (LocalFiniteMeasure X), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (P ∘ φ) atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_probabilityMeasure_of_isTight P
  apply isTightMeasureSet_of_lintegral_localMass_le U hU hcover _ b hb
  rintro _ ⟨i, rfl⟩ n
  exact hbound i n

/-- A fixed compact exhaustion gives the windows, so only actual local moments
remain in the probability-law subsequence statement. -/
theorem exists_tendsto_subseq_of_lintegral_exhaustionMass_le
    (P : ℕ → ProbabilityMeasure (LocalFiniteMeasure X)) (K : CompactExhaustion X)
    (b : ℕ → ℝ≥0∞) (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ i n, ∫⁻ μ, (μ : Measure X) (interior (K n))
      ∂(P i : Measure (LocalFiniteMeasure X)) ≤ b n) :
    ∃ Q : ProbabilityMeasure (LocalFiniteMeasure X), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (P ∘ φ) atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_of_lintegral_localMass_le P _ (fun _ ↦ isOpen_interior) _ b hb hbound
  intro A hA
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
  exact ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩

end LocalFiniteMeasure
end OTSelector.Probability
