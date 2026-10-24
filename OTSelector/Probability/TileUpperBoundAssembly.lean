import OTSelector.Probability.BinomialDiscrepancy

/-!
# Expectation-level tile upper assembly

The deterministic block repair bounds the assignment value by the sum of its
tile block values plus the kinetic bound times half the total count
discrepancy.  At fixed sample size the expected discrepancy of the cell counts
is `sqrt (2 n #C)`.  This module packages the resulting expectation-level upper
bound, isolating the geometric per-cell input `E[block_c] <= model_c` as an
explicit hypothesis.

The conclusion has exactly the shape needed by the physical pressure squeeze:
the expected value is bounded by the weighted model block sum plus a vanishing
repair error.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal unitInterval Topology

noncomputable section
namespace OTSelector.Probability

/-- **Expectation-level tile upper bound.**  If the assignment value is
pointwise at most the sum of its block values plus the kinetic bound times half
the total count discrepancy, the per-cell expected block values are at most
`model c`, and the per-cell expected discrepancies obey the binomial bound,
then the expected value is at most `sum_c model c` plus the repair term
`B/2 * sqrt (2 n #C)`. -/
theorem integral_total_le_sum_model_add_repair
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (w : ι → I) (hwsum : ∑ c, (w c : ℝ) = 1)
    (total : Ω → ℝ) (block : ι → Ω → ℝ)
    (mc kc : ι → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hrepair : ∀ᵐ ξ ∂P, total ξ ≤ (∑ c, block c ξ) +
      B * (1 / 2) * (∑ c, |(mc c ξ - kc c ξ)|))
    (hintTotal : Integrable total P)
    (hintBlock : ∀ c, Integrable (block c) P)
    (hintCount : ∀ c, Integrable (fun ξ => |(mc c ξ - kc c ξ)|) P)
    (hcount : ∀ c, ∫ ξ, |(mc c ξ - kc c ξ)| ∂P ≤
      Real.sqrt (2 * (n : ℝ) * (w c : ℝ)))
    (model : ι → ℝ)
    (hblock : ∀ c, ∫ ξ, block c ξ ∂P ≤ model c) :
    ∫ ξ, total ξ ∂P ≤
      (∑ c, model c) + B * (1 / 2) *
        Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ)) := by
  classical
  have hIntSumBlock : Integrable (fun ξ => ∑ c, block c ξ) P :=
    integrable_finsetSum _ (fun c _ => hintBlock c)
  have hIntSumCount : Integrable (fun ξ => ∑ c, |(mc c ξ - kc c ξ)|) P :=
    integrable_finsetSum _ (fun c _ => hintCount c)
  have hIntRhs : Integrable (fun ξ => (∑ c, block c ξ) +
      B * (1 / 2) * (∑ c, |(mc c ξ - kc c ξ)|)) P :=
    hIntSumBlock.add (hIntSumCount.const_mul (B * (1 / 2)))
  have hmono := integral_mono_ae hintTotal hIntRhs hrepair
  have hval : ∫ ξ, ((∑ c, block c ξ) +
        B * (1 / 2) * (∑ c, |(mc c ξ - kc c ξ)|)) ∂P =
      (∑ c, ∫ ξ, block c ξ ∂P) + B * (1 / 2) *
        (∑ c, ∫ ξ, |(mc c ξ - kc c ξ)| ∂P) := by
    rw [integral_add hIntSumBlock (hIntSumCount.const_mul (B * (1 / 2))),
      integral_const_mul, integral_finsetSum _ (fun c _ => hintBlock c),
      integral_finsetSum _ (fun c _ => hintCount c)]
  rw [hval] at hmono
  have hb : (∑ c, ∫ ξ, block c ξ ∂P) ≤ ∑ c, model c :=
    Finset.sum_le_sum fun c _ => hblock c
  have hd : (∑ c, ∫ ξ, |(mc c ξ - kc c ξ)| ∂P) ≤
      Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ)) :=
    (Finset.sum_le_sum fun c _ => hcount c).trans
      (sum_sqrt_two_mul_weight_le w hwsum n)
  have hmul : B * (1 / 2) *
        (∑ c, ∫ ξ, |(mc c ξ - kc c ξ)| ∂P) ≤
      B * (1 / 2) * Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ)) :=
    mul_le_mul_of_nonneg_left hd (mul_nonneg hB0 (by norm_num))
  linarith

end OTSelector.Probability
