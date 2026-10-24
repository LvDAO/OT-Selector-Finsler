import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Martingale.OptionalSampling
import OTSelector.Probability.CountingProcess.Core
import OTSelector.Probability.CountingProcess.StoppingMasks

/-!
# Probability.CountingProcess.StoppingEvaluation

**Conditions:** A strongly adapted real process is evaluated at a finite-range stopping coordinate; the occupation-event consumer has a simple counting process and the stated survival stopping time.

**Objects:** Measurable stopped values and stopped lower-occupation events.

**Proof detail:** Split the evaluation into finitely many stopping-coordinate atoms, each multiplying an adapted deterministic section; combine measurable count increments and the stopping survival event.

**Sources:** [Richard D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124 (1980)](https://ir.cwi.nl/pub/11499/11499D.pdf#page=13), Section 2.1, pp. 8–9 (PDF pages 13–14), stochastic basis, stopping-time sigma-field, predictable processes and counting paths; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited primary sections give the mathematical principles used here. The exact source statement, endpoint convention, measure generality and finite encoding are local corollaries or Lean adapters rather than a claim that the book states the Lean theorem verbatim.
-/


/-!
# Evaluation on finite stopping grids

Finite-valued stopping coordinates can be evaluated without a progressive-measurability theorem:
the stopped value is a finite sum over the measurable stopping atoms.  This module records that
elementary argument for real-valued adapted processes and applies it to counting increments.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Evaluation of a real adapted process at a finite-valued stopping coordinate is measurable in
the ambient sigma algebra. -/
theorem stronglyMeasurable_eval_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0}
    (hX : StronglyAdapted ℱ X)
    (hσ : IsStoppingTime ℱ (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    (hσ_range : (Set.range σ).Finite) :
    StronglyMeasurable (fun ω ↦ X (σ ω) ω) := by
  classical
  let S : Finset ℝ≥0 := hσ_range.toFinset
  have hAtom : ∀ s : ℝ≥0, MeasurableSet {ω | σ ω = s} := by
    intro s
    have hs : {ω | σ ω = s} = {ω | (σ ω : WithTop ℝ≥0) = s} := by
      ext ω
      constructor
      · exact fun h ↦ congrArg (fun u : ℝ≥0 ↦ (u : WithTop ℝ≥0)) h
      · exact fun h ↦ WithTop.coe_eq_coe.mp h
    rw [hs]
    exact ℱ.le s _ (MeasureTheory.IsStoppingTime.measurableSet_eq hσ s)
  have hsum : StronglyMeasurable
      (∑ s ∈ S, {ω' | σ ω' = s}.indicator (X s)) := by
    exact Finset.stronglyMeasurable_sum S fun s _ ↦
      ((hX s).mono (ℱ.le s)).indicator (hAtom s)
  have heq :
      (∑ s ∈ S, {ω' | σ ω' = s}.indicator (X s)) =
        (fun ω ↦ X (σ ω) ω) := by
    funext ω
    have hmem : σ ω ∈ S := by
      simp [S, Set.Finite.mem_toFinset]
    calc
      (∑ s ∈ S, {ω' | σ ω' = s}.indicator (X s)) ω =
          {ω' | σ ω' = σ ω}.indicator (X (σ ω)) ω := by
            simp only [Finset.sum_apply]
            apply Finset.sum_eq_single_of_mem (σ ω) hmem
            intro s hs hne
            simp [Ne.symm hne]
      _ = X (σ ω) ω := by simp
  rw [← heq]
  exact hsum

/-- The event that a finite-grid counting increment is small and its endpoint precedes a stopping
coordinate. -/
def stoppedLowerOccupationEvent (N : ℝ≥0 → Ω → ℕ) (σ : Ω → ℝ≥0)
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (r : ℝ≥0) : Set Ω :=
  {ω | (N (σ ω + r) ω : ℝ) - N (σ ω) ω ≤ a * (r : ℝ) ∧
    ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω}

omit [MeasurableSpace Ω] in
/-- The finite-grid stopped lower-occupation event is measurable. -/
theorem measurableSet_stoppedLowerOccupationEvent_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℕ} {σ : Ω → ℝ≥0}
    {τ : Ω → WithTop ℝ≥0} {a : ℝ} {r : ℝ≥0}
    (hN : IsSimpleCountingProcess ℱ N)
    (hσ : IsStoppingTime ℱ (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    (hσ_range : (Set.range σ).Finite) (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet (stoppedLowerOccupationEvent N σ τ a r) := by
  have hρ := IsStoppingTime.coe_add_const_finiteRange hσ hσ_range r
  have hNs : StronglyMeasurable (fun ω ↦ (N (σ ω) ω : ℝ)) :=
    stronglyMeasurable_eval_finiteRange hN.stronglyAdapted hσ hσ_range
  have hNr : StronglyMeasurable (fun ω ↦ (N (σ ω + r) ω : ℝ)) := by
    apply stronglyMeasurable_eval_finiteRange hN.stronglyAdapted hρ.1
    refine (hσ_range.image fun s ↦ s + r).subset ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  have hcount : MeasurableSet
      {ω | (N (σ ω + r) ω : ℝ) - N (σ ω) ω ≤ a * (r : ℝ)} :=
    (hNr.sub hNs).measurableSet_le stronglyMeasurable_const
  have hsurvival : MeasurableSet
      {ω | ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω} :=
    hρ.1.measurableSpace_le _ (hρ.1.measurableSet_le_stopping_time hτ)
  exact hcount.inter hsurvival

end OTSelector.CountingProcess
