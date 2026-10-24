import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
## Lemma skeleton

* **Conditions:** Finite measure; a distance-valued family and an index filter.
* **Objects:** Convergence in probability and bounded-continuous integral probes.
* **Proof detail:** Unfold convergence in measure, then use bounded-continuous readouts for the weak interface.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 245, especially 245A–245E, convergence in measure and its topology.
  https://www1.essex.ac.uk/maths/people/fremlin/chap24.pdf
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61

**Relationship to the sources:** The alias and arbitrary-filter real-distance equivalence are Lean interfaces, not additional probabilistic theorems in the references.
-/

/-!
# Probability-convergence interfaces

Mathlib calls convergence in probability `TendstoInMeasure`.  This file gives the project a stable
name and fixes the real-distance formulation used throughout `main.tex`.
-/

open MeasureTheory

namespace OTSelector

/-- Project name for mathlib's convergence-in-measure notion on a probability space. -/
abbrev TendstoInProbability {Ω ι E : Type*} [MeasurableSpace Ω] [EDist E]
    (P : Measure Ω) (X : ι → Ω → E) (l : Filter ι) (Z : Ω → E) : Prop :=
  TendstoInMeasure P X l Z

theorem tendstoInProbability_iff_measureReal_dist {Ω ι E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace E] {P : Measure Ω} [IsFiniteMeasure P]
    {X : ι → Ω → E} {l : Filter ι} {Z : Ω → E} :
    TendstoInProbability P X l Z ↔
      ∀ ε, 0 < ε →
        Filter.Tendsto (fun i ↦ P.real {ω | ε ≤ dist (X i ω) (Z ω)}) l (nhds 0) :=
  tendstoInMeasure_iff_measureReal_dist

/-- Weak convergence in probability for random probability measures, expressed through bounded
continuous test integrals.  This avoids choosing a particular compatible metric on the weak
topology. -/
def WeakTendstoInProbability {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] (P : Measure Ω)
    (M : ι → Ω → ProbabilityMeasure E) (l : Filter ι) (ν : ProbabilityMeasure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    TendstoInProbability P
      (fun i ω ↦ ∫ x, f x ∂(M i ω : Measure E)) l
      (fun _ ↦ ∫ x, f x ∂(ν : Measure E))

end OTSelector
