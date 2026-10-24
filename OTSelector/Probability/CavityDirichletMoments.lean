import OTSelector.Probability.Dirichlet.CavityMoments
import OTSelector.Probability.CavityCells
import OTSelector.Probability.Dirichlet.CavityWordCount
import OTSelector.Finite.CapacityAssignment
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact finite insertion-count probabilities for cavity moments

For the actual retained-data law and an independent finite iid complement, a prescribed
word of cavity labels has probability equal to the corresponding product of cell masses.
Atomless pairwise differences make different words almost everywhere disjoint. Consequently
the probability of prescribed target counts is the number of feasible words times the mixed
moment of the actual cavity masses. This is the conditional multinomial step of the
Dirichlet moment argument; the target-tree uniqueness of a successful retained subset is
a separate combinatorial input and is not assumed here as a distributional law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n : ℕ} {κ W S : Type*} [Fintype κ]
  [MeasurableSpace W] [MeasurableSpace S]















/-- The conditional multinomial identity for the actual cavity masses. Pairwise atomless
original row differences give the no-tie premise, and the word multiplicity is computed
as the exact multinomial coefficient, including zero prescribed counts. -/
theorem measure_cavityAllocationCounts_atomless {K : ℕ}
    (ν : Measure W) [SFinite ν] (μ : Measure S) [IsProbabilityMeasure μ]
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (n + 1))
    (hatom : ∀ᵐ w ∂ν, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ row (w, s) j - row (w, s) l)))
    (r : Fin (n + 1) → ℕ) (hr : ∑ j, r j = K) :
    (ν.prod (Measure.pi (fun _ : Fin K ↦ μ)))
      (cavityAllocationCounts retained row i r) =
      (Nat.multinomial Finset.univ r : ℝ≥0∞) *
        ∫⁻ w, ∏ j, cavityCellMass μ retained row i j w ^ r j ∂ν := by
  rw [← card_capacityFeasible_eq_multinomial r hr]
  apply measure_cavityAllocationCounts ν μ retained row hret hrow i
  filter_upwards [hatom] with w hw
  intro j l hjl
  have := hw j l hjl
  exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow i j l w

end OTSelector.Probability
