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

/-!
Conditions: A countable coordinate family with compact coordinate ranges in first-countable spaces; the probability version supplies tightness and the displayed carrier hypotheses for compactness.

Objects: One common increasing inner subsequence at each outer index and one common increasing outer subsequence, convergent in every coordinate.

Proof detail: Apply compactness of the countable product once for each inner sequence and again to the sequence of coordinate limits; translate product convergence into every coordinate.

References: D. H. Fremlin: Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability; D. H. Fremlin: 4A1F(a–b), p. 3; 4A2G(f)(i–iii), p. 16.
Relation: A two-stage common compactness argument. It produces iterated limits with the inner threshold allowed to depend on the fixed outer index, not a uniform joint two-parameter limit.
-/


/-!
# Common two-stage subsequences for original countable root laws

Coordinate compactness supplies one inner sample subsequence at each tilt and
one outer tilt subsequence for every original root law simultaneously. No new
joint input experiment or coupling of physical samples is introduced.
-/
open Set Function Filter MeasureTheory Topology TopologicalSpace
open scoped Topology
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Countably many compact coordinate ranges have common inner and outer
subsequences. Both original indices are retained separately. -/
theorem exists_common_iterated_subseq_of_compact_ranges
    {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, FirstCountableTopology (X i)]
    (K : ∀ i, Set (X i)) (hK : ∀ i, IsCompact (K i))
    (P : ∀ i, ℕ → ℕ → X i) (hP : ∀ i ℓ n, P i ℓ n ∈ K i) :
    ∃ Q : ∀ i, ℕ → X i, ∃ φ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (φ ℓ)) ∧
      (∀ i ℓ, Tendsto (fun n ↦ P i ℓ (φ ℓ n)) atTop (𝓝 (Q i ℓ))) ∧
      ∃ R : ∀ i, X i, ∃ ψ : ℕ → ℕ,
        StrictMono ψ ∧ ∀ i, Tendsto (fun ℓ ↦ Q i (ψ ℓ)) atTop (𝓝 (R i)) := by
  have hc : IsCompact (Set.pi univ K) := isCompact_univ_pi hK
  have hi (ℓ : ℕ) : ∃ Q : ∀ i, X i, Q ∈ Set.pi univ K ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n i ↦ P i ℓ (φ n)) atTop (𝓝 Q) := by
    obtain ⟨Q, hQ, φ, hφ, hlim⟩ := hc.isSeqCompact (fun n i _ ↦ hP i ℓ n)
    exact ⟨Q, hQ, φ, hφ, hlim⟩
  choose Q hQ φ hφ hinner using hi
  obtain ⟨R, _, ψ, hψ, houter⟩ := hc.isSeqCompact hQ
  refine ⟨fun i ℓ ↦ Q ℓ i, φ, hφ, ?_, R, ψ, hψ, ?_⟩
  · intro i ℓ
    exact ((continuous_apply i).tendsto (Q ℓ)).comp (hinner ℓ)
  · intro i
    exact ((continuous_apply i).tendsto R).comp houter

/-- Original tight law families admit one common sample-then-tilt extraction
for every countable root box, without changing any original marginal law. -/
theorem exists_common_iterated_probabilityMeasure_subseq_of_isTight
    {I : Type*} [Countable I] {S : I → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    [∀ i, T2Space (S i)] [∀ i, PseudoMetrizableSpace (S i)] [∀ i, SeparableSpace (S i)]
    (P : ∀ i, ℕ → ℕ → ProbabilityMeasure (S i))
    (htight : ∀ i, IsTightMeasureSet (range (fun v : ℕ × ℕ ↦ (P i v.1 v.2 : Measure (S i))))) :
    ∃ Q : ∀ i, ℕ → ProbabilityMeasure (S i), ∃ φ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (φ ℓ)) ∧
      (∀ i ℓ, Tendsto (fun n ↦ P i ℓ (φ ℓ n)) atTop (𝓝 (Q i ℓ))) ∧
      ∃ R : ∀ i, ProbabilityMeasure (S i), ∃ ψ : ℕ → ℕ,
        StrictMono ψ ∧ ∀ i, Tendsto (fun ℓ ↦ Q i (ψ ℓ)) atTop (𝓝 (R i)) := by
  let K (i : I) := closure (range (fun v : ℕ × ℕ ↦ P i v.1 v.2))
  have hK (i : I) : IsCompact (K i) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight i using 1
    ext μ
    simp
  exact exists_common_iterated_subseq_of_compact_ranges K hK P
    (fun i ℓ n ↦ subset_closure ⟨(ℓ, n), rfl⟩)

end OTSelector.Probability
