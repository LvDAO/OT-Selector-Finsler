import OTSelector.Probability.MarkedCountExpectation
import OTSelector.Probability.MarkedDePoissonization

/-!
# Diagonal limit of the fixed-size marked block expectation

At equal intensity and sample size, the fixed-size marked block value is the
marked fixed value `markedFixedValue`.  Consequently the diagonal limit of the
block expectation is exactly the de-Poissonized marked pressure limit.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The fixed-size block value at equal sizes is the marked fixed value. -/
theorem markedFixedBlockValue_self (q : ℕ) (r t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (n : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    markedFixedBlockValue q r t kin g n n ω =
      markedFixedValue q r t kin g n ω := by
  unfold markedFixedBlockValue markedFixedValue markedEdgeCost
  rfl

/-- The block expectation at equal intensity and size is the fixed marked pressure. -/
theorem markedFixedBlockExpectation_self (q : ℕ) (r t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (n : ℕ) :
    markedFixedBlockExpectation q r t kin g α β (n : ℝ≥0) n n =
      ∫ ω, markedFixedValue q r t kin g n ω
        ∂(twoMarkedCloudLaw q A B α β (n : ℝ≥0)) := by
  unfold markedFixedBlockExpectation
  congr 1

/-- **Diagonal limit of the block expectation.**  Along equal intensity and
sample size, the block pressure converges to the local marked pressure limit. -/
theorem tendsto_markedFixedBlockExpectation_diagonal
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun N : ℕ =>
      markedFixedBlockExpectation q (N : ℝ) t kin g α β (N : ℝ≥0) N N / (N : ℝ))
      atTop (𝓝 (p t)) := by
  intro t
  have hbase := tendsto_markedFixedPressure_div (q := q) hq
    (C := C) (G := G) hC0 hG0 hkin hkin_bound hg hgb α β p hp t
  refine hbase.congr' ?_
  filter_upwards with N
  rw [markedFixedBlockExpectation_self]

end OTSelector.Probability
