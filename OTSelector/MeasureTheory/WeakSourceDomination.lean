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
import OTSelector.Probability.WeakClosedConstraint
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteSourceDomination.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteSourceDomination`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.WeakSourceDomination

## Lemma skeleton

* **Conditions:** A continuous possibly nonproper observation and a fixed outer-regular dominating measure; plan-valued maps are continuous and scene laws converge weakly.
* **Objects:** Closedness and weak-limit persistence of whole observed-measure domination and resulting absolute continuity.
* **Proof detail:** Characterize domination by open target preimages using outer regularity, use lower semicontinuity of open-set evaluation to show closedness and apply weak closed-set carrying.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (composition): Nonproper map domination survives without assuming projected local finiteness.
-/

/-!
# Fixed source domination survives vague and weak scene limits

A continuous nonproper projection preserves domination by a fixed outer-regular
measure under vague limits. The proof uses all open preimages and lower
semicontinuity, so it does not assume that the projected limit is locally finite.
-/

open Function Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [LocallyCompactSpace X]
  [BorelSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] in
/-- Open preimage bounds characterize domination by a fixed outer-regular measure. -/
theorem map_le_fixed_iff_open_preimage (μ : Measure X) (ν : Measure Y) [ν.OuterRegular]
    (f : X → Y) (hf : Continuous f) :
    μ.map f ≤ ν ↔ ∀ U : Set Y, IsOpen U → μ (f ⁻¹' U) ≤ ν U := by
  constructor
  · intro h U hU
    rw [← Measure.map_apply hf.measurable hU.measurableSet]
    exact h U
  · intro h
    apply Measure.le_iff'.mpr
    intro S
    rw [S.measure_eq_iInf_isOpen ν]
    refine le_iInf (fun U ↦ le_iInf (fun hSU ↦ le_iInf (fun hU ↦ ?_)))
    calc
      μ.map f S ≤ μ.map f U := measure_mono hSU
      _ = μ (f ⁻¹' U) := Measure.map_apply hf.measurable hU.measurableSet
      _ ≤ ν U := h U hU

/-- Fixed marginal domination is a closed condition on the actual vague carrier. -/
theorem isClosed_map_le_fixed (ν : Measure Y) [ν.OuterRegular]
    (f : X → Y) (hf : Continuous f) :
    IsClosed {μ : LocalFiniteMeasure X | (μ : Measure X).map f ≤ ν} := by
  have heq : {μ : LocalFiniteMeasure X | (μ : Measure X).map f ≤ ν} =
      {μ : LocalFiniteMeasure X | ∀ U : Set Y, IsOpen U → (μ : Measure X) (f ⁻¹' U) ≤ ν U} :=
    Set.ext (fun μ ↦ map_le_fixed_iff_open_preimage (μ : Measure X) ν f hf)
  rw [heq]
  simp only [ofPred_forall]
  exact isClosed_iInter (fun U ↦ isClosed_iInter (fun hU ↦
    (LocalFiniteMeasure.lowerSemicontinuous_measure_open (hU.preimage hf)).isClosed_preimage (ν U)))

section Laws
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- Almost-sure fixed domination survives the original correlated weak scene laws. -/
theorem ae_map_le_fixed_of_weak_tendsto
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (ν : Measure Y) [ν.OuterRegular] (f : X → Y) (hf : Continuous f)
    (μ : Ω → LocalFiniteMeasure X) (hμ : Continuous μ)
    (hs : ∀ n, ∀ᵐ ω ∂(Pn n : Measure Ω), (μ ω : Measure X).map f ≤ ν) :
    ∀ᵐ ω ∂(P : Measure Ω), (μ ω : Measure X).map f ≤ ν := by
  exact OTSelector.Probability.ae_mem_closed_of_tendsto P Pn hweak _
    ((isClosed_map_le_fixed ν f hf).preimage hμ) hs

/-- The limiting original source marginal is absolutely continuous with respect
to the same fixed reference law; the assertion is pathwise, not merely averaged. -/
theorem ae_map_absolutelyContinuous_fixed_of_weak_tendsto
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (ν : Measure Y) [ν.OuterRegular] (f : X → Y) (hf : Continuous f)
    (μ : Ω → LocalFiniteMeasure X) (hμ : Continuous μ)
    (hs : ∀ n, ∀ᵐ ω ∂(Pn n : Measure Ω), (μ ω : Measure X).map f ≤ ν) :
    ∀ᵐ ω ∂(P : Measure Ω), (μ ω : Measure X).map f ≪ ν :=
  (ae_map_le_fixed_of_weak_tendsto P Pn hweak ν f hf μ hμ hs).mono
    (fun _ h ↦ Measure.absolutelyContinuous_of_le h)

end Laws
end OTSelector.Probability

end
end
