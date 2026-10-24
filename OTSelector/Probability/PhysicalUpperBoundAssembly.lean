import OTSelector.Probability.MarkedTileBinomialAssembly
import OTSelector.Probability.TileUpperBoundAssembly
import OTSelector.Probability.MarkedCountExpectation

/-!
# Physical expectation upper bound from the per-cell block model

This module assembles the fixed-sample-size upper bound for the physical
pressure.  The only geometric input is isolated as `hblock`: the expected value
of each physical tile block is at most the corresponding marked-model block
expectation at the random tile counts.  The other two inputs are

* the deterministic per-sample tile repair inequality, and
* the binomial count law of the tile labels (through the mean discrepancy
  bound).

Given those, the normalized expected value is eventually at most the weighted
sum of the local marked pressure limits.  This is the formal interface that the
geometric freezing/atlas comparison has to supply.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal unitInterval Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The un-normalized marked-model block sum at sample size `n` for a tile of
weight `w`. -/
noncomputable def modelBlockSum (q : ℕ) (t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (w : I) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
    binomialMass n w a * binomialMass n w b *
      markedFixedBlockExpectation q
        ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
        ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a b

/-- **Physical expectation upper bound from the per-cell block model.**  Under
the deterministic tile repair, the binomial count-discrepancy bound, and the
per-cell block comparison, the normalized expected value has limsup at most the
weighted sum of the local marked pressure limits. -/
theorem exists_physical_upper_bound_of_block_model
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι]
    {w : ι → I} (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {Kb G : ℝ} (hKb0 : 0 ≤ Kb) (hG0 : 0 ≤ G)
    {kin : ι → A → B → (Fin q → ℝ) → ℝ} {g : ι → A → B → ℝ}
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Kb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (t : ℝ)
    (total : ∀ n, Ω n → ℝ) (block : ∀ n, ι → Ω n → ℝ)
    (mc kc : ∀ n, ι → Ω n → ℝ)
    (hrepair : ∀ n, ∀ᵐ ξ ∂P n, total n ξ ≤ (∑ c, block n c ξ) +
      (((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) * (1 / 2) *
        (∑ c, |(mc n c ξ - kc n c ξ)|)))
    (hintTotal : ∀ n, Integrable (total n) (P n))
    (hintBlock : ∀ n c, Integrable (block n c) (P n))
    (hintCount : ∀ n c,
      Integrable (fun ξ => |(mc n c ξ - kc n c ξ)|) (P n))
    (hcount : ∀ n c, ∫ ξ, |(mc n c ξ - kc n c ξ)| ∂P n ≤
      Real.sqrt (2 * (n : ℝ) * (w c : ℝ)))
    (hblock : ∀ n c, ∫ ξ, block n c ξ ∂P n ≤ modelBlockSum q t (kin c) (g c)
      (α c) (β c) (w c) n) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, total n ξ ∂P n) / (n : ℝ) ≤
        (∑ c, (w c : ℝ) * p c t) + ε := by
  classical
  intro ε hε
  -- The model block sums converge to the weighted local pressure sum.
  have hmodel : Tendsto (fun n : ℕ =>
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) n) / (n : ℝ))
      atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    have h := tendsto_binomial_tileBlockPressure_sum (q := q) hq
      (w := w) hwpos hKb0 hG0 hkin hkin_bound hg hgb α β p hp t
    refine h.congr' ?_
    filter_upwards with n
    rw [Finset.sum_div]
    simp only [modelBlockSum]
  -- The normalized repair error vanishes.
  have hrepairlim : Tendsto (fun n : ℕ =>
      ((((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) * (1 / 2) *
        Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ))) / (n : ℝ)))
      atTop (𝓝 0) := by
    have h := tendsto_binomial_repairError_zero hq Kb G t (Fintype.card ι)
    refine h.congr' ?_
    filter_upwards with n
    ring
  have hlimsum : Tendsto (fun n : ℕ =>
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) n) / (n : ℝ) +
        ((((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) * (1 / 2) *
          Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ))) / (n : ℝ)))
      atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    simpa using hmodel.add hrepairlim
  have hev := hlimsum.eventually
    (Iio_mem_nhds (by linarith : (∑ c, (w c : ℝ) * p c t) <
      (∑ c, (w c : ℝ) * p c t) + ε))
  -- The per-sample assembly bound.
  have hb : ∀ n, ∫ ξ, total n ξ ∂P n ≤
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) n) +
        (((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) * (1 / 2) *
          Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ))) := by
    intro n
    have hB0 : 0 ≤ ((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) :=
      add_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hKb0)
        (mul_nonneg (abs_nonneg t) hG0)
    exact integral_total_le_sum_model_add_repair (P := P n) w hwsum
      (total n) (block n) (mc n) (kc n) (B := (n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G)
      hB0 (hrepair n) (hintTotal n) (fun c => hintBlock n c)
      (fun c => hintCount n c) (fun c => hcount n c)
      (fun c => modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) n)
      (fun c => hblock n c)
  filter_upwards [hev, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hdiv : (∫ ξ, total n ξ ∂P n) / (n : ℝ) ≤
      ((∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) n) +
        (((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) * (1 / 2) *
          Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ)))) / (n : ℝ) :=
    div_le_div_of_nonneg_right (hb n) hnpos.le
  have hsplit : ((∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) n) +
        (((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) * (1 / 2) *
          Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ)))) / (n : ℝ) =
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) n) / (n : ℝ) +
        ((((n : ℝ) ^ (2 / (q : ℝ)) * Kb + |t| * G) * (1 / 2) *
          Real.sqrt (2 * (n : ℝ) * (Fintype.card ι : ℝ))) / (n : ℝ)) := by
    ring
  rw [hsplit] at hdiv
  linarith

end OTSelector.Probability
