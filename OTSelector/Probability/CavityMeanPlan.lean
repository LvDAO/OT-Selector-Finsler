import OTSelector.Transport.Semidiscrete.MeanPlan
import OTSelector.Probability.CavityCells

/-!
Conditions: An actual optimal fractional row, a unique cavity cell and the stated independent environment/row law and integrable readouts.

Objects: Indicator identification of that row and its exact expected cavity readout.

Proof detail: Positive row entries must lie in cavity minima, uniqueness makes the row a single indicator; integrate the same indicator against the product law.

Sources: Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Rick Durrett, Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56); Project manuscript, Section “Exact iid cavity disintegration”, Theorem thm:iid-cavity-dirichlet and Proposition prop:iid-cavity-mean, equation eq:iid-cavity-mean-plan (main.tex).
Relation: Local row/mean-plan identity; main.tex prop:iid-cavity-mean is the project-level assembly, not a textbook assertion about arbitrary selected plans.
-/

/-!
# Exact mean readouts of the full optimal face through cavity cells

An independent original source is inserted into its actual retained assignment problem.
Whenever the inserted cavity cell is unique, every optimal fractional matrix has the same
unit row. Fubini then identifies expectations of arbitrary integrable endpoint tests with
the mean of the actual cell allocations. No measurable optimizer selection is needed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n : ℕ} {W S Ω : Type*}
  [MeasurableSpace W] [MeasurableSpace S] [MeasurableSpace Ω]









/-- Averaging the exact original-row formulas gives the normalized mean empirical plan.
Each retained input is independent of its own inserted row; the retained inputs for different
rows need not be independent. The same arbitrary optimal fractional matrix appears in every row.
This applies to the original iid cloud with each row removed in turn. -/
theorem integral_optimalFractional_mean_eq_mean_cavity
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S) [SFinite μ]
    (W₀ : Fin (n + 1) → Ω → W) (X : Fin (n + 1) → Ω → S)
    (hW : ∀ i, Measurable (W₀ i)) (hX : ∀ i, Measurable (X i))
    (hindep : ∀ i, IndepFun (W₀ i) (X i) P) (hlaw : ∀ i, P.map (X i) = μ)
    (retained : Fin (n + 1) → W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : Fin (n + 1) → W × S → Fin (n + 1) → ℝ)
    (hret : ∀ i k l, Measurable (fun w ↦ retained i w k l))
    (hrow : ∀ i j, Measurable (fun z ↦ row i z j))
    (hatom : ∀ i, ∀ᵐ w ∂P.map (W₀ i), ∀ j k, j ≠ k →
      NullSingletonClass (μ.map (fun s ↦ row i (w, s) j - row i (w, s) k)))
    (cost A : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hcost : ∀ i, ∀ᵐ ω ∂P,
      Function.update (retained i (W₀ i ω)) i (row i (W₀ i ω, X i ω)) = cost ω)
    (hA : ∀ᵐ ω ∂P, OptimalFractionalAssignment (cost ω) (A ω))
    (g : Fin (n + 1) → W × S → Fin (n + 1) → ℝ)
    (hg : ∀ i j, Integrable (fun z ↦ g i z j) ((P.map (W₀ i)).prod μ)) :
    (∫ ω, (∑ i, ∑ j, A ω i j * g i (W₀ i ω, X i ω) j) / (n + 1 : ℝ) ∂P) =
      (∑ i, ∫ w, cavityMeanReadout μ (retained i) (row i) i (g i) w
        ∂P.map (W₀ i)) / (n + 1 : ℝ) := by
  have hrowA i : ∀ᵐ ω ∂P, OptimalFractionalAssignment
      (Function.update (retained i (W₀ i ω)) i (row i (W₀ i ω, X i ω))) (A ω) := by
    filter_upwards [hA, hcost i] with ω hAω hcω
    simpa only [hcω] using hAω
  have hmean i := integral_optimalFractional_row_eq_cavityMeanReadout P μ
    (W₀ i) (X i) (hW i) (hX i) (hindep i) (hlaw i)
    (retained i) (row i) (hret i) (hrow i) i (hatom i) A (hrowA i) (g i) (hg i)
  rw [integral_div, integral_finsetSum _ (fun i _ ↦ (hmean i).1)]
  congr 1
  exact Finset.sum_congr rfl (fun i _ ↦ (hmean i).2)

end OTSelector.Probability
