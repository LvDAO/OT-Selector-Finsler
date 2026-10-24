import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.MeasureTheory.LocalFiniteMeasureProbability
import OTSelector.MeasureTheory.LocalFiniteMeasureTightness

/-!
## Lemma skeleton

* **Conditions:** Probability spaces may vary with the index. Measurable locally finite random measures have integrable local-mass squares uniformly bounded on a compact exhaustion. The scalar helper also assumes nonnegativity almost everywhere.
* **Objects:** A finite first-moment bound (C+1)/2, tight families of original pushforward laws, and an actual weak subsequence.
* **Proof detail:** Use L2 to get L1, integrate 2f <= f^2+1, and transfer to extended nonnegative local masses. Feed the resulting first moments into local-mass tightness and Prokhorov.

## Mathematical sources

* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.1, Theorem 1.6.3 (Hölder), p. 29.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6, Theorem 1.6.1, p. 29 (linearity and monotonicity of expectation).
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
* D. H. Fremlin, *Measure Theory, Volume 4*, Proposition 437P(a)–(b), pp. 66–67, and Theorem 437R(g)–(h), p. 68 and following proof.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=66
* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4

**Relationship to the sources:** Elementary moment comparison combined with Markov compact containment and forward Prokhorov. The changing sample spaces are handled by their pushforward laws and require no independence.
-/

/-!
# Original second moments give tight laws of diffuse measures

The actual local-mass second moments proved for rooted target clouds feed the
compact-test carrier directly, including changing original sample spaces.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

/-- A real second-moment bound gives a finite first-moment bound on a probability
space. This elementary estimate avoids choosing a square-root normalization. -/
theorem lintegral_ofReal_le_of_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hm : Measurable f)
    (hsq : Integrable (fun sample ↦ (f sample) ^ 2) P)
    (hpos : ∀ᵐ sample ∂P, 0 ≤ f sample)
    {C : ℝ} (hb : (∫ sample, (f sample) ^ 2 ∂P) ≤ C) :
    (∫⁻ sample, ENNReal.ofReal (f sample) ∂P) ≤ ENNReal.ofReal ((C + 1) / 2) := by
  have hi : Integrable f P := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hsq)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hpos]
  apply ENNReal.ofReal_le_ofReal
  have h := integral_mono hi ((hsq.add (integrable_const (1 : ℝ))).div_const 2)
    (fun sample ↦ show f sample ≤ ((f sample) ^ 2 + 1) / 2 by
      nlinarith [sq_nonneg (f sample - 1)])
  rw [integral_div] at h
  simp only [Pi.add_apply] at h
  rw [integral_add hsq (integrable_const (1 : ℝ)), integral_const] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  linarith

namespace LocalFiniteMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

omit [SecondCountableTopology X] in
/-- Second moments of actual open-exhaustion masses imply tightness on the
original sample-size-dependent probability spaces. -/
theorem isTightMeasureSet_map_of_integral_exhaustionMass_sq_le
    {I : Type*} {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (measure : ∀ i, Ω i → LocalFiniteMeasure X) (hmeasure : ∀ i, Measurable (measure i))
    (K : CompactExhaustion X) (C : ℕ → ℝ)
    (hsq : ∀ i n, Integrable (fun sample ↦
      ((measure i sample : Measure X).real (interior (K n))) ^ 2) (P i))
    (hbound : ∀ i n, (∫ sample,
      ((measure i sample : Measure X).real (interior (K n))) ^ 2 ∂P i) ≤ C n) :
    IsTightMeasureSet (range (fun i ↦ (P i).map (measure i))) := by
  refine isTightMeasureSet_map_of_lintegral_localMass_le P measure hmeasure
    (fun n ↦ interior (K n)) (fun _ ↦ isOpen_interior) ?_
    (fun n ↦ ENNReal.ofReal ((C n + 1) / 2)) (fun _ ↦ ENNReal.ofReal_ne_top) ?_
  · intro A hA
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
    exact ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩
  · intro i n
    have hm : Measurable (fun sample ↦
        (measure i sample : Measure X).real (interior (K n))) :=
      ((measurable_measure_open isOpen_interior).comp (hmeasure i)).ennreal_toReal
    have hb := lintegral_ofReal_le_of_second_moment hm (hsq i n)
      (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) (hbound i n)
    convert hb using 1
    apply lintegral_congr
    intro sample
    exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top (K.isCompact n).measure_ne_top
      (measure_mono interior_subset))).symm

/-- Original random measures with uniform local second moments have a common
weak law subsequence, even though their original sample spaces vary with size. -/
theorem exists_tendsto_subseq_original_of_second_moments
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (measure : ∀ i, Ω i → LocalFiniteMeasure X) (hmeasure : ∀ i, Measurable (measure i))
    (K : CompactExhaustion X) (C : ℕ → ℝ)
    (hsq : ∀ i n, Integrable (fun sample ↦
      ((measure i sample : Measure X).real (interior (K n))) ^ 2) (P i))
    (hbound : ∀ i n, (∫ sample,
      ((measure i sample : Measure X).real (interior (K n))) ^ 2 ∂P i) ≤ C n) :
    let laws : ℕ → ProbabilityMeasure (LocalFiniteMeasure X) := fun i ↦
      ProbabilityMeasure.map (⟨P i, inferInstance⟩ : ProbabilityMeasure (Ω i))
        (f := measure i) (hmeasure i).aemeasurable
    ∃ Q : ProbabilityMeasure (LocalFiniteMeasure X), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (laws ∘ φ) atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_probabilityMeasure_of_isTight
  exact isTightMeasureSet_map_of_integral_exhaustionMass_sq_le P measure hmeasure K C hsq hbound

end LocalFiniteMeasure
end OTSelector.Probability
