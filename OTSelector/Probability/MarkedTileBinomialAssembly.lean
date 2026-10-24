import OTSelector.Probability.MarkedBlockBinomialLimit
import OTSelector.Probability.BinomialDiscrepancy

/-!
# Binomial tile assembly

Summing the single-tile binomial block limit over a finite family of tiles gives
the count-averaged block pressure: the normalized binomial-weighted sum of the
marked block expectations converges to the weighted sum of the local pressure
limits.  This is the fixed-sample-size, count-averaged counterpart of the marked
finite-tile upper bound.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal unitInterval Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

set_option maxHeartbeats 800000 in
/-- **Binomial tile assembly.**  The normalized expected block pressure at the
random tile counts is the weighted sum of the local marked pressures. -/
theorem tendsto_binomial_tileBlockPressure_sum
    (q : ℕ) (hq : 4 < q) {C : Type*} [Fintype C]
    {w : C → I} (hw : ∀ c, 0 < (w c : ℝ))
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : C → Measure A) (β : C → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : C → ℝ → ℝ)
    (hp : ∀ (c : C) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (t : ℝ) :
    Tendsto (fun n : ℕ =>
      ∑ c : C,
        (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          binomialMass n (w c) m * binomialMass n (w c) k *
            markedFixedBlockExpectation q
              ((Nat.floor ((n : ℝ) * (w c : ℝ)) : ℕ) : ℝ) t
              (kin c) (g c) (α c) (β c)
              ((Nat.floor ((n : ℝ) * (w c : ℝ)) : ℕ) : ℝ≥0) m k) / (n : ℝ))
      atTop (𝓝 (∑ c : C, (w c : ℝ) * p c t)) := by
  classical
  refine tendsto_finsetSum Finset.univ (fun c _ => ?_)
  exact tendsto_markedFixedBlockExpectation_binomial q hq hCb0 hG0
    (hkin c) (hkin_bound c) (hg c) (hgb c) (α c) (β c) (p c) (hp c) (w c) (hw c) t

/-- **Repair error of the binomial tile counts.**  For weights summing to one,
the normalized kinetic bound times the total expected count discrepancy vanishes
for `q > 4`. -/
theorem tendsto_binomial_tileRepairError_zero
    (q : ℕ) (hq : 4 < q) {C : Type*} [Fintype C]
    {w : C → I} (_hw : ∑ c, (w c : ℝ) = 1)
    (A G t : ℝ) :
    Tendsto (fun n : ℕ =>
      ((((n : ℝ) ^ (2 / (q : ℝ)) * A + |t| * G) / (n : ℝ)) *
        (Real.sqrt (2 * (n : ℝ) * (Fintype.card C : ℝ)) / 2))) atTop (𝓝 0) := by
  simpa using tendsto_binomial_repairError_zero hq A G t (Fintype.card C)

end OTSelector.Probability
