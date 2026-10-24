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

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteMarginalLocalFinite.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteMarginalLocalFinite`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.NonproperMarginalLocalFiniteness

## Lemma skeleton

* **Conditions:** Weakly converging probability laws and uniform finite lower-integral bounds for a lower-semicontinuous readout; open source windows cover every compact source set.
* **Objects:** Almost-everywhere finiteness of limiting readouts and local finiteness of nonproper source projections.
* **Proof detail:** Apply the nonnegative Portmanteau inequality, deduce finite readout almost everywhere, intersect countably many open-window events and dominate each compact source set by one window.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Local finiteness is produced by actual marginal-window bounds; the projection need not be proper.
-/

/-!
# Local finiteness of noncompact marginal projections in actual weak limits

Uniform original first moments of source-window masses imply that the weak-limit
source projections are locally finite almost surely. The projections need not be
proper maps.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- A lower-semicontinuous mass readout remains finite almost surely in every weak
limit when its original first moments are uniformly finite. -/
theorem ae_lt_top_of_weak_uniform_lintegral_bound
    (Q : ProbabilityMeasure Ω) (P : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto P atTop (𝓝 Q)) (W : Ω → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ n, (∫⁻ ω, W ω ∂(P n : Measure Ω)) ≤ C) :
    ∀ᵐ ω ∂(Q : Measure Ω), W ω < ⊤ := by
  have htail (r : ℝ≥0∞) (hr : r ≠ 0) (hrt : r ≠ ⊤) :
      (Q : Measure Ω) {ω | r < W ω} ≤ C / r := by
    apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
      (hW.isOpen_preimage r)).trans
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ (P n : Measure Ω) {ω | r ≤ W ω} :=
        measure_mono fun ω h ↦ le_of_lt (show r < W ω from h)
      _ ≤ (∫⁻ ω, W ω ∂(P n : Measure Ω)) / r :=
        meas_ge_le_lintegral_div hW.measurable.aemeasurable hr hrt
      _ ≤ C / r := by gcongr; exact hbound n
  have hb (n : ℕ) : (Q : Measure Ω) {ω | W ω = ⊤} ≤ C / (n + 1 : ℝ≥0∞) := by
    apply (measure_mono (show {ω | W ω = ⊤} ⊆ {ω | (n + 1 : ℝ≥0∞) < W ω} from
      fun ω h ↦ by change (n + 1 : ℝ≥0∞) < W ω; rw [show W ω = ⊤ from h]; finiteness)).trans
    exact htail _ (by positivity) (by finiteness)
  have hdiv : Tendsto (fun n : ℕ ↦ C / (n + 1 : ℝ≥0∞)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ≥0∞)) atTop (𝓝 ⊤) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat 1)
    simpa only [ENNReal.div_top] using ENNReal.Tendsto.const_div hn (Or.inr hC)
  have hzero : (Q : Measure Ω) {ω | W ω = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto hdiv (Filter.Eventually.of_forall hb)) bot_le
  exact (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun ω h ↦ lt_top_iff_ne_top.mpr h

section Projection
variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

omit [SecondCountableTopology X] [T2Space Y] in
/-- A countable source exhaustion turns the proved finite-window property into
local finiteness of the actual limiting source marginal. -/
theorem ae_locallyFinite_fst_of_weak_source_window_bounds
    (Q : ProbabilityMeasure Ω) (P : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto P atTop (𝓝 Q))
    (π : Ω → LocalFiniteMeasure (X × Y)) (hπ : Continuous π)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k))
    (hcover : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ U k)
    (C : ℕ → ℝ≥0∞) (hC : ∀ k, C k ≠ ⊤)
    (hbound : ∀ k n, (∫⁻ ω, (π ω : Measure (X × Y)) (U k ×ˢ univ)
      ∂(P n : Measure Ω)) ≤ C k) :
    ∀ᵐ ω ∂(Q : Measure Ω), IsFiniteMeasureOnCompacts (π ω : Measure (X × Y)).fst := by
  have hall : ∀ᵐ ω ∂(Q : Measure Ω), ∀ k,
      (π ω : Measure (X × Y)) (U k ×ˢ univ) < ⊤ := by
    apply ae_all_iff.mpr
    intro k
    exact ae_lt_top_of_weak_uniform_lintegral_bound Q P hweak _
      ((LocalFiniteMeasure.lowerSemicontinuous_measure_open ((hU k).prod isOpen_univ)).comp hπ)
      (C k) (hC k) (hbound k)
  filter_upwards [hall] with ω hω
  constructor
  intro K hK
  obtain ⟨k, hk⟩ := hcover K hK
  rw [Measure.fst, Measure.map_apply measurable_fst hK.measurableSet]
  exact (measure_mono (show Prod.fst ⁻¹' K ⊆ U k ×ˢ (univ : Set Y) from
    fun e he ↦ ⟨hk he, mem_univ _⟩)).trans_lt (hω k)

end Projection
end OTSelector.Probability

end
end
