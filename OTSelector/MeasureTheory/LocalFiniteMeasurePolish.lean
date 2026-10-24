import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCompactness
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests

/-!
## Lemma skeleton

* **Conditions:** The locally compact second-countable metrizable/exhaustible carrier hypotheses in the file.
* **Objects:** A closed embedding of locally finite measures into a countable real product.
* **Proof detail:** Code convergence bounds local masses, yields compact containment and closes the image; inherit Polishness.

## Mathematical sources

* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=68

**Relationship to the sources:** Kallenberg Chapter 4 describes Polish vague measure spaces. This file supplies a separate compact-test proof and its measurable-readout criterion, with its own hypotheses.
-/

/-!
# The compact-test topology on diffuse measures is Polish

The countable code includes nonnegative cutoffs of every compact exhaustion
window. Convergence of the code bounds all local masses, hence gives actual vague
compactness. This makes the code a closed embedding into a countable real product.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace OTSelector.Probability.LocalFiniteMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

/-- Convergent compact-test codes force the original diffuse measures into one
genuine compact family. -/
theorem exists_isCompact_of_separatingTestCode_tendsto
    (K : CompactExhaustion X) (μ : ℕ → LocalFiniteMeasure X)
    {a : ℕ ⊕ (ℕ × ℕ) → ℝ}
    (h : Tendsto (separatingTestCode K ∘ μ) atTop (𝓝 a)) :
    ∃ A : Set (LocalFiniteMeasure X), IsCompact A ∧ ∀ n, μ n ∈ A := by
  have hb : ∀ j, ∃ b : ℝ, ∀ n, testIntegral (μ n) (exhaustionCutoff K j) ≤ b := by
    intro j
    have hj := ((continuous_apply (.inl j)).tendsto a).comp h
    obtain ⟨b, hb⟩ := hj.bddAbove_range
    exact ⟨b, fun n ↦ hb (mem_range_self n)⟩
  choose b hb using hb
  let C : ℕ → ℝ≥0 := fun j ↦ ⟨max (b j) 0, le_max_right _ _⟩
  refine ⟨{ν | ∀ j, (ν : Measure X) (interior (K j)) ≤ C j},
    isCompact_exhaustionMass_le K C, fun n j ↦ ?_⟩
  have hmass : (μ n : Measure X) (K j) ≤
      ENNReal.ofReal (testIntegral (μ n) (exhaustionCutoff K j)) := by
    apply (exhaustionCutoff K j).integrable.measure_le_integral
    · exact Eventually.of_forall (fun x ↦ (exhaustionCutoff_bounds K j x).1)
    · intro x hx
      exact (exhaustionCutoff_eq_one K j hx).ge
  have hreal : testIntegral (μ n) (exhaustionCutoff K j) ≤ (C j : ℝ) :=
    (hb j n).trans (le_max_left _ _)
  exact (measure_mono interior_subset).trans (hmass.trans
    (by simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hreal))

/-- Closed families of actual measures have closed images in the countable code. -/
theorem isClosedMap_separatingTestCode (K : CompactExhaustion X) :
    IsClosedMap (separatingTestCode K : LocalFiniteMeasure X → (ℕ ⊕ (ℕ × ℕ) → ℝ)) := by
  intro A hA
  apply IsSeqClosed.isClosed
  intro a b ha hb
  choose μ hμ hcode using ha
  have heq : separatingTestCode K ∘ μ = a := funext hcode
  have hcodeLim : Tendsto (separatingTestCode K ∘ μ) atTop (𝓝 b) := by
    rw [heq]
    exact hb
  obtain ⟨D, hD, hμD⟩ := exists_isCompact_of_separatingTestCode_tendsto K μ hcodeLim
  obtain ⟨ν, _, φ, hφ, hlim⟩ := isSeqCompact_of_isCompact hD hμD
  have hν : ν ∈ A := hA.mem_of_tendsto hlim (Eventually.of_forall (fun n ↦ hμ (φ n)))
  refine ⟨ν, hν, ?_⟩
  exact tendsto_nhds_unique ((continuous_separatingTestCode K).tendsto ν |>.comp hlim)
    (hcodeLim.comp hφ.tendsto_atTop)

/-- The countable compact-test code is an actual closed topological embedding. -/
theorem isClosedEmbedding_separatingTestCode (K : CompactExhaustion X) :
    IsClosedEmbedding (separatingTestCode K : LocalFiniteMeasure X → (ℕ ⊕ (ℕ × ℕ) → ℝ)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_separatingTestCode K) (separatingTestCode_injective K)
    (isClosedMap_separatingTestCode K)

/-- The diffuse measure carrier has a proved Polish topology, not an assumed one. -/
instance : PolishSpace (LocalFiniteMeasure X) :=
  (isClosedEmbedding_separatingTestCode (CompactExhaustion.choice X)).polishSpace

/-- A random diffuse measure is measurable once its actual compact-test integrals
are measurable. No separately supplied scene Borel structure is needed. -/
theorem measurable_of_testIntegral {Ω : Type*} [MeasurableSpace Ω]
    (measure : Ω → LocalFiniteMeasure X)
    (h : ∀ f : C_c(X, ℝ), Measurable (fun sample ↦ testIntegral (measure sample) f)) :
    Measurable measure := by
  let K := CompactExhaustion.choice X
  apply (isClosedEmbedding_separatingTestCode K).measurableEmbedding.measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun i ↦ h (separatingTest K i))

end OTSelector.Probability.LocalFiniteMeasure
