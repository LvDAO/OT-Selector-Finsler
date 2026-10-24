import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.MeasureTheory.LocalFiniteMeasure
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitMassTail.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitMassTail`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakMassTail

## Lemma skeleton

* **Conditions:** Two successive weak probability limits and uniform finite first-moment bounds for lower-semicontinuous mass readouts; countably many open source windows cover compact sets.
* **Objects:** Finite limiting mass readouts almost surely and local finiteness of full source projections.
* **Proof detail:** Markov bounds the open superlevel events, apply open-set Portmanteau at both distinct limits, send the threshold to infinity and intersect the countable window events.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=59): Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).

Source relation (composition): Iterated open-tail argument; the two approximation indices are not merged into an unproved diagonal limit.
-/

/-!
# Finite mass tails through successive actual weak limits

Uniform original first moments bound open superlevel tails. Passing those same
tails first through the sample-size weak limit and then through the tilt-index
weak limit keeps lower-semicontinuous mass readouts finite almost surely. A
countable source exhaustion gives local finiteness of the full nonproper source
projection. The two limit indices remain separate.
-/

open MeasureTheory Set Filter Topology TopologicalSpace OTSelector.Probability
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- Open superlevel tail bounds survive each successive actual weak limit. -/
theorem measure_open_le_of_weak_uniform_bound
    (Q : ProbabilityMeasure Ω) (P : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto P atTop (𝓝 Q)) {U : Set Ω} (hU : IsOpen U)
    (C : ℝ≥0∞) (hbound : ∀ n, (P n : Measure Ω) U ≤ C) :
    (Q : Measure Ω) U ≤ C := by
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU).trans
  exact liminf_le_of_frequently_le' (Filter.Eventually.frequently
    (Filter.Eventually.of_forall hbound))

/-- Uniform original first moments control a lower-semicontinuous mass readout
through both sample-size and tilt-index weak limits, in that order. -/
theorem ae_lt_top_of_iterated_weak_uniform_lintegral_bound
    (P : ℕ → ℕ → ProbabilityMeasure Ω) (Q : ℕ → ProbabilityMeasure Ω)
    (hinner : ∀ k, Tendsto (P k) atTop (𝓝 (Q k)))
    (R : ProbabilityMeasure Ω) (ψ : ℕ → ℕ)
    (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R))
    (W : Ω → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ k n, (∫⁻ ω, W ω ∂(P k n : Measure Ω)) ≤ C) :
    ∀ᵐ ω ∂(R : Measure Ω), W ω < ⊤ := by
  have htail (r : ℝ≥0∞) (hr : r ≠ 0) (hrt : r ≠ ⊤) :
      (R : Measure Ω) {ω | r < W ω} ≤ C / r := by
    apply measure_open_le_of_weak_uniform_bound R (Q ∘ ψ) houter (hW.isOpen_preimage r)
    intro k
    apply measure_open_le_of_weak_uniform_bound (Q (ψ k)) (P (ψ k))
      (hinner (ψ k)) (hW.isOpen_preimage r)
    intro n
    calc
      _ ≤ (P (ψ k) n : Measure Ω) {ω | r ≤ W ω} :=
        measure_mono fun _ h ↦ le_of_lt (show r < W _ from h)
      _ ≤ (∫⁻ ω, W ω ∂(P (ψ k) n : Measure Ω)) / r :=
        meas_ge_le_lintegral_div hW.measurable.aemeasurable hr hrt
      _ ≤ C / r := by gcongr; exact hbound (ψ k) n
  have hb (n : ℕ) : (R : Measure Ω) {ω | W ω = ⊤} ≤ C / (n + 1 : ℝ≥0∞) := by
    apply (measure_mono (show {ω | W ω = ⊤} ⊆ {ω | (n + 1 : ℝ≥0∞) < W ω} from
      fun ω h ↦ by change (n + 1 : ℝ≥0∞) < W ω; rw [show W ω = ⊤ from h]; finiteness)).trans
    exact htail _ (by positivity) (by finiteness)
  have hdiv : Tendsto (fun n : ℕ ↦ C / (n + 1 : ℝ≥0∞)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ≥0∞)) atTop (𝓝 ⊤) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat 1)
    simpa only [ENNReal.div_top] using ENNReal.Tendsto.const_div hn (Or.inr hC)
  have hzero : (R : Measure Ω) {ω | W ω = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto hdiv (Filter.Eventually.of_forall hb)) bot_le
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun _ h ↦ lt_top_iff_ne_top.mpr h

section Marginal
variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

omit [SecondCountableTopology X] [T2Space Y] in
/-- Uniform original window bounds produce local finiteness of the full
nonproper source marginal after both actual weak-limit stages. -/
theorem ae_locallyFinite_fst_of_iterated_weak_source_window_bounds
    (P : ℕ → ℕ → ProbabilityMeasure Ω) (Q : ℕ → ProbabilityMeasure Ω)
    (hinner : ∀ k, Tendsto (P k) atTop (𝓝 (Q k)))
    (R : ProbabilityMeasure Ω) (ψ : ℕ → ℕ)
    (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R))
    (π : Ω → LocalFiniteMeasure (X × Y)) (hπ : Continuous π)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k))
    (hcover : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ U k)
    (C : ℕ → ℝ≥0∞) (hC : ∀ k, C k ≠ ⊤)
    (hbound : ∀ k n m, (∫⁻ ω, (π ω : Measure (X × Y)) (U m ×ˢ univ)
      ∂(P k n : Measure Ω)) ≤ C m) :
    ∀ᵐ ω ∂(R : Measure Ω), IsFiniteMeasureOnCompacts (π ω : Measure (X × Y)).fst := by
  have hall : ∀ᵐ ω ∂(R : Measure Ω), ∀ m,
      (π ω : Measure (X × Y)) (U m ×ˢ univ) < ⊤ := by
    apply ae_all_iff.mpr
    intro m
    exact ae_lt_top_of_iterated_weak_uniform_lintegral_bound P Q hinner R ψ houter _
      ((LocalFiniteMeasure.lowerSemicontinuous_measure_open ((hU m).prod isOpen_univ)).comp hπ)
      (C m) (hC m) (fun k n ↦ hbound k n m)
  filter_upwards [hall] with ω hω
  constructor
  intro K hK
  obtain ⟨m, hm⟩ := hcover K hK
  rw [Measure.fst, Measure.map_apply measurable_fst hK.measurableSet]
  exact (measure_mono (show Prod.fst ⁻¹' K ⊆ U m ×ˢ (univ : Set Y) from
    fun e he ↦ ⟨hm he, mem_univ _⟩)).trans_lt (hω m)

end Marginal
end OTSelector.Reconstruction

end
end
