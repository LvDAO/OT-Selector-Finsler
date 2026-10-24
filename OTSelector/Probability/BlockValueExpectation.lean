import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.BlockMatchingComparison
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Finite.PartialMatching

/-!
Conditions: Actual finite random clouds with bounded-above edge cost and explicitly integrable total optimal value, block optimal values and total block count discrepancy.

Objects: An expectation upper bound by the sum of actual expected block values plus B/2 times the expected count discrepancy.

Proof detail: Apply the already proved deterministic maximum-cardinality block matching inequality pointwise, integrate by monotonicity and exchange only the finite sum of integrable block terms.

References: Rick Durrett: Section 1.4, Theorem 1.4.7, p. 23; Section 1.6, positive/negative parts p. 28 and Theorem 1.6.1, p. 29; Reinhard Diestel: Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
Relation: An integration adapter for a deterministic finite matching bound. The graph source supplies matching terminology; the specific block cost inequality is proved locally and is not attributed to a textbook stochastic theorem.
-/


/-!
# Expected block decomposition of maximum-cardinality values

The deterministic block bound is integrated over a random point process.  The
clouds and their block labels may have random sizes.  The only stochastic data
are the total value, the per-block values and the per-block count discrepancy;
all integrability requirements are explicit.

The conclusion is the finite-volume block step:

`E maxCardValue ≤ ∑_b E (block value b) + B/2 * E ∑_b |#S_b - #T_b|`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

open OTSelector

/-- Integration of the deterministic block bound for maximum-cardinality matching
values, with random cloud sizes and random block labels. -/
theorem integral_maxCardValue_le_sum_block_add_discrepancy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Np Nm : Ω → ℕ)
    (blockS : (ω : Ω) → Fin (Np ω) → ι)
    (blockT : (ω : Ω) → Fin (Nm ω) → ι)
    (cost : (ω : Ω) → Fin (Np ω) → Fin (Nm ω) → ℝ)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ω i j, cost ω i j ≤ B)
    (hV : Integrable (fun ω ↦ PartialMatching.maxCardValue (cost ω)) P)
    (hBlock : ∀ t : ι, Integrable (fun ω ↦ PartialMatching.maxCardValue
      (blockCost (blockS ω) (blockT ω) (cost ω) t)) P)
    (hDisc : Integrable (fun ω ↦ ∑ t,
      |(blockSizeS (blockS ω) t : ℝ) - (blockSizeT (blockT ω) t : ℝ)|) P) :
    ∫ ω, PartialMatching.maxCardValue (cost ω) ∂P ≤
      (∑ t, ∫ ω, PartialMatching.maxCardValue
        (blockCost (blockS ω) (blockT ω) (cost ω) t) ∂P) +
        B * ((1 / 2 : ℝ) * ∫ ω, ∑ t,
          |(blockSizeS (blockS ω) t : ℝ) - (blockSizeT (blockT ω) t : ℝ)| ∂P) := by
  classical
  -- Pointwise block bound.
  have hpoint (ω : Ω) : PartialMatching.maxCardValue (cost ω) ≤
      (∑ t, PartialMatching.maxCardValue
        (blockCost (blockS ω) (blockT ω) (cost ω) t)) +
        B * ((1 / 2 : ℝ) * ∑ t,
          |(blockSizeS (blockS ω) t : ℝ) - (blockSizeT (blockT ω) t : ℝ)|) :=
    maxCardValue_le_sum_block_add_half_discrepancy (blockS ω) (blockT ω) (cost ω)
      (hB ω) hB0
  -- Integrability of the right-hand side.
  have hsumBlock : Integrable (fun ω ↦ ∑ t, PartialMatching.maxCardValue
      (blockCost (blockS ω) (blockT ω) (cost ω) t)) P :=
    integrable_finsetSum _ (fun t _ ↦ hBlock t)
  have hhalfDisc : Integrable (fun ω ↦ B * ((1 / 2 : ℝ) * ∑ t,
      |(blockSizeS (blockS ω) t : ℝ) - (blockSizeT (blockT ω) t : ℝ)|)) P :=
    (hDisc.const_mul (1 / 2 : ℝ)).const_mul B
  have hmajor : Integrable (fun ω ↦
      (∑ t, PartialMatching.maxCardValue
        (blockCost (blockS ω) (blockT ω) (cost ω) t)) +
        B * ((1 / 2 : ℝ) * ∑ t,
          |(blockSizeS (blockS ω) t : ℝ) - (blockSizeT (blockT ω) t : ℝ)|)) P :=
    hsumBlock.add hhalfDisc
  have hmono := integral_mono_ae hV hmajor (Filter.Eventually.of_forall hpoint)
  -- Integrate the majorant term by term.
  have hInt : ∫ ω, ((∑ t, PartialMatching.maxCardValue
        (blockCost (blockS ω) (blockT ω) (cost ω) t)) +
        B * ((1 / 2 : ℝ) * ∑ t,
          |(blockSizeS (blockS ω) t : ℝ) - (blockSizeT (blockT ω) t : ℝ)|)) ∂P =
      (∑ t, ∫ ω, PartialMatching.maxCardValue
        (blockCost (blockS ω) (blockT ω) (cost ω) t) ∂P) +
        B * ((1 / 2 : ℝ) * ∫ ω, ∑ t,
          |(blockSizeS (blockS ω) t : ℝ) - (blockSizeT (blockT ω) t : ℝ)| ∂P) := by
    rw [integral_add hsumBlock hhalfDisc,
      integral_finsetSum _ (fun t _ ↦ hBlock t)]
    congr 1
    rw [integral_const_mul, integral_const_mul]
  rwa [hInt] at hmono

end OTSelector.Probability
