import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
import OTSelector.Probability.BinomialPoissonExpectation

/-!
Conditions: An actual Poisson count independent of any sigma-finite sequence carrier, and an integrable real function of both coordinates.

Objects: The genuine product integral written as a Poisson-pmf-weighted sum of sequence integrals.

Proof detail: Apply Fubini to the integrable product function and evaluate the remaining count integral against the genuine Poisson pmf.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38.
Relation: A count-layer product-integration identity. The module makes no separate stochastic pressure-limit claim despite its original application-oriented name.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.MarkedCountLayer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.MarkedCountLayer`; the selected original proof blocks follow. -/
section

/-!
# Count layers of the marked Poisson pressure

The marked Poisson cloud is a product of a Poisson count and an iid position/mark
sequence.  Integrating a function of the count and the sequence therefore gives
a Poisson-weighted sum of the sequence integrals.  For the marked pressure this
expresses the global pressure as the Poisson-weighted double sum of the
fixed-size block expectations.

The identity is the link between the global marked pressure limit and the local
tile blocks.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

variable {X : Type*} [MeasurableSpace X]

/-- Integration over a Poisson count times an independent measure. -/
theorem integral_poissonMeasure_prod (ν : Measure X) [SFinite ν] (R : ℝ≥0)
    (f : ℕ → X → ℝ)
    (hf : Integrable (fun z : ℕ × X => f z.1 z.2) ((poissonMeasure R).prod ν)) :
    ∫ z : ℕ × X, f z.1 z.2 ∂((poissonMeasure R).prod ν) =
      ∑' n, poissonMass R n * ∫ x, f n x ∂ν := by
  rw [integral_prod _ hf, integral_poissonMeasure]
  apply tsum_congr
  intro n
  rw [smul_eq_mul]
  simp only [Prod.fst, Prod.snd]
  rfl

end OTSelector.Probability

end
end
