import OTSelector.Limit.FinslerExpectationUpperBound

/-!
# Relaxed per-cell comparison for the Finsler expectation upper bound

The module `OTSelector.Limit.FinslerExpectationUpperBound` reduces the
expectation upper bound input `hupper` to an *exact* per-cell comparison of the
normalized physical tile block expectation with the marked model block sum.
Reconnaissance of the geometric side showed that the available relative
Taylor/freezing comparisons do not give that exact comparison.  They give, per
cell and per scale `n`,

`physical block ≤ (1 + 2 εₙ) * frozen block + probe error`,

where `εₙ → 0` is the Taylor parameter and the probe error also vanishes as
`n → ∞` (it measures the fraction of edges that fall outside the frozen
neighbourhood).  Equivalently, after normalizing by the block size,

`normalized physical block ≤ (1 + δ n) * model block + δ n`

for a sequence `δ : ℕ → ℝ` with `δ n → 0`, where `δ n` dominates both `2 εₙ`
and the normalized probe error.

This module weakens the per-cell input of the upper-bound assembly from the
exact comparison to exactly this relaxed comparison.  It contains:

* `supportedPressure_integral_le_weighted_sum_of_relaxed_block_model`, the
  generic relaxed assembly: the per-cell comparison with a relative error
  `δ n → 0` still yields the same conclusion as the exact assembly,
  `∫ pressure ≤ ∑ c, w c * p c t + ε` eventually;
* `supportedPressure_integral_le_weighted_sum_of_tile_dependent_relaxed_block_model`,
  the variant in which the relative error `δ n c` depends on the tile and is
  dominated by a vanishing sequence (this needs the signed model block sums to
  be uniformly bounded in absolute value, since the model block sums are not
  sign-definite);
* `finslerExpectationUpperBound_of_relaxed_block_model`, the physical Finsler
  specialization with the concrete normalized `maxCardValue` tile blocks;
* `finsler_hupper_of_relaxed_block_model`, the `hupper` interface corollary.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BigOperators BoundedContinuousFunction unitInterval

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Relaxed block-model assembly.**

This is the analogue of
`supportedPressure_integral_le_weighted_sum_of_block_model` in which the exact
per-cell comparison `hblock` is replaced by the relative comparison

`∫ ξ, block n c ξ ∂P n ≤ (1 + δ n) * (modelBlockSum ... (n + 1) / (n + 1)) + δ n`

with a nonnegative relative error `δ n` that tends to zero.  The conclusion is
unchanged: for every `ε > 0` the normalized expected physical pressure is
eventually at most `∑ c, w c * p c t + ε`.

The proof sums the relaxed comparisons.  The model part becomes

`(1 + δ n) * (∑ c, modelBlockSum_c / (n + 1)) + δ n * #ι`,

which converges to `∑ c, w c * p c t` because the normalized model block sums
converge to that weighted sum and `δ n → 0`.  The repair term is unchanged and
already vanishes after normalization. -/
theorem supportedPressure_integral_le_weighted_sum_of_relaxed_block_model
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι]
    {w : ι → I} (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : ι → A → B → (Fin q → ℝ) → ℝ} {g : ι → A → B → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (block : ∀ n, ι → Ω n → ℝ) (mc kc : ∀ n, ι → Ω n → ℝ)
    (Bnd : ℕ → ℝ) (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hrepair : ∀ n, ∀ᵐ ξ ∂P n,
      supportedDistancePressure μ ν K hK hμ hν (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ≤
      (∑ c, block n c ξ) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          (∑ c, |mc n c ξ - kc n c ξ|))
    (hBlim : Tendsto (fun n =>
      (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
        Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ))) atTop (𝓝 0))
    (hintTotal : ∀ n, Integrable (fun ξ => supportedDistancePressure μ ν K hK hμ hν
      (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t) (P n))
    (hintBlock : ∀ n c, Integrable (block n c) (P n))
    (hintCount : ∀ n c, Integrable (fun ξ => |mc n c ξ - kc n c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ, |mc n c ξ - kc n c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hblock : ∀ n c, ∫ ξ, block n c ξ ∂P n ≤
      (1 + δ n) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, supportedDistancePressure μ ν K hK hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε := by
  classical
  intro ε hε
  -- The marked model block sums converge at the physical sample size `n + 1`.
  have hmodel := tendsto_binomial_tileBlockPressure_sum (q := q) hq
    (w := w) hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp t
  have hshift : Tendsto (fun n : ℕ =>
      ∑ c : ι, (∑ m ∈ Finset.range (n + 1 + 1), ∑ k ∈ Finset.range (n + 1 + 1),
        binomialMass (n + 1) (w c) m * binomialMass (n + 1) (w c) k *
          markedFixedBlockExpectation q
            ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w c : ℝ)) : ℕ) : ℝ) t
            (kin c) (g c) (α c) (β c)
            ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w c : ℝ)) : ℕ) : ℝ≥0) m k) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hmodel
  have hmodel' : Tendsto (fun n : ℕ =>
      ∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    refine hshift.congr' ?_
    filter_upwards with n
    rfl
  -- The per-sample expectation bound with the relaxed comparison.
  have hmain : ∀ n, (∫ ξ, supportedDistancePressure μ ν K hK hμ hν
      (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
      (1 + δ n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n * (Fintype.card ι : ℝ) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) := by
    intro n
    have hB0 : 0 ≤ Bnd n / ((n + 1 : ℕ) : ℝ) :=
      div_nonneg (hBnd0 n) (by positivity)
    have h := integral_total_le_sum_model_add_repair (P := P n) (n := n + 1)
      w hwsum
      (fun ξ => supportedDistancePressure μ ν K hK hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t)
      (block n) (mc n) (kc n) (B := Bnd n / ((n + 1 : ℕ) : ℝ)) hB0
      (hrepair n) (hintTotal n) (fun c => hintBlock n c) (fun c => hintCount n c)
      (fun c => hcount n c)
      (fun c => (1 + δ n) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n)
      (fun c => hblock n c)
    have hsum : (∑ c, ((1 + δ n) *
          (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)) + δ n)) =
        (1 + δ n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
          ((n + 1 : ℕ) : ℝ)) + δ n * (Fintype.card ι : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    rw [hsum] at h
    exact h
  -- The relaxed model bound converges to the weighted sum of the local limits.
  have hlim : Tendsto (fun n : ℕ =>
      (1 + δ n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n * (Fintype.card ι : ℝ) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)))
      atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    have h1 : Tendsto (fun n : ℕ => (1 + δ n) *
        (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
          ((n + 1 : ℕ) : ℝ))) atTop
        (𝓝 ((1 + 0) * (∑ c, (w c : ℝ) * p c t))) :=
      ((tendsto_const_nhds.add hδ).mul hmodel')
    have h2 : Tendsto (fun n : ℕ => δ n * (Fintype.card ι : ℝ)) atTop
        (𝓝 (0 * (Fintype.card ι : ℝ))) :=
      hδ.mul tendsto_const_nhds
    have h3 : Tendsto (fun n : ℕ =>
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ))) atTop (𝓝 0) :=
      hBlim
    simpa using (h1.add h2).add h3
  have hev := hlim.eventually
    (Iio_mem_nhds (lt_add_of_pos_right (∑ c, (w c : ℝ) * p c t) hε))
  filter_upwards [hev] with n hn
  exact (hmain n).trans hn.le

/-- **Tile-dependent relaxed block-model assembly.**

The per-cell relative error is now allowed to depend on the tile:
`δ n c ≥ 0` with a common dominating sequence `d n → 0`.

Because the model block sums are signed (the marked block expectation contains
the tilt term), a tile-dependent error cannot simply be replaced by its
maximum: for a negative model block a smaller error gives a *larger* relative
bound.  The sound comparison is

`(1 + δ n c) M_c + δ n c ≤ (1 + d n) M_c + d n |M_c| + d n`,

so the conclusion carries the additional error `d n * ∑ c, |M_c|`.  The
hypothesis `hModelBound` that the normalized model block sums are uniformly
bounded in absolute value is what makes this error vanish; it holds in the
intended application, where the normalized model block sums converge. -/
theorem supportedPressure_integral_le_weighted_sum_of_tile_dependent_relaxed_block_model
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι]
    {w : ι → I} (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : ι → A → B → (Fin q → ℝ) → ℝ} {g : ι → A → B → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (block : ∀ n, ι → Ω n → ℝ) (mc kc : ∀ n, ι → Ω n → ℝ)
    (Bnd : ℕ → ℝ) (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hrepair : ∀ n, ∀ᵐ ξ ∂P n,
      supportedDistancePressure μ ν K hK hμ hν (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ≤
      (∑ c, block n c ξ) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          (∑ c, |mc n c ξ - kc n c ξ|))
    (hBlim : Tendsto (fun n =>
      (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
        Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ))) atTop (𝓝 0))
    (hintTotal : ∀ n, Integrable (fun ξ => supportedDistancePressure μ ν K hK hμ hν
      (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t) (P n))
    (hintBlock : ∀ n c, Integrable (block n c) (P n))
    (hintCount : ∀ n c, Integrable (fun ξ => |mc n c ξ - kc n c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ, |mc n c ξ - kc n c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (δ : ℕ → ι → ℝ) (d : ℕ → ℝ) (C : ℝ)
    (hδ0 : ∀ n c, 0 ≤ δ n c) (hδd : ∀ n c, δ n c ≤ d n)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Tendsto d atTop (𝓝 0))
    (hblock : ∀ n c, ∫ ξ, block n c ξ ∂P n ≤
      (1 + δ n c) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n c)
    (hModelBound : ∀ n, ∑ c, |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
      ((n + 1 : ℕ) : ℝ)| ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, supportedDistancePressure μ ν K hK hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε := by
  classical
  intro ε hε
  have hmodel := tendsto_binomial_tileBlockPressure_sum (q := q) hq
    (w := w) hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp t
  have hshift : Tendsto (fun n : ℕ =>
      ∑ c : ι, (∑ m ∈ Finset.range (n + 1 + 1), ∑ k ∈ Finset.range (n + 1 + 1),
        binomialMass (n + 1) (w c) m * binomialMass (n + 1) (w c) k *
          markedFixedBlockExpectation q
            ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w c : ℝ)) : ℕ) : ℝ) t
            (kin c) (g c) (α c) (β c)
            ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w c : ℝ)) : ℕ) : ℝ≥0) m k) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hmodel
  have hmodel' : Tendsto (fun n : ℕ =>
      ∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    refine hshift.congr' ?_
    filter_upwards with n
    rfl
  have hmain : ∀ n, (∫ ξ, supportedDistancePressure μ ν K hK hμ hν
      (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
      (1 + d n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + d n * (C + (Fintype.card ι : ℝ)) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) := by
    intro n
    have hB0 : 0 ≤ Bnd n / ((n + 1 : ℕ) : ℝ) :=
      div_nonneg (hBnd0 n) (by positivity)
    have h := integral_total_le_sum_model_add_repair (P := P n) (n := n + 1)
      w hwsum
      (fun ξ => supportedDistancePressure μ ν K hK hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t)
      (block n) (mc n) (kc n) (B := Bnd n / ((n + 1 : ℕ) : ℝ)) hB0
      (hrepair n) (hintTotal n) (fun c => hintBlock n c) (fun c => hintCount n c)
      (fun c => hcount n c)
      (fun c => (1 + δ n c) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n c)
      (fun c => hblock n c)
    -- Termwise comparison with the common dominating error `d n`.
    have hterm : ∀ c, (1 + δ n c) *
          (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)) + δ n c ≤
        (1 + d n) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)) +
          d n * |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)| + d n := by
      intro c
      have hMabs : (δ n c - d n) *
            (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) ≤
          d n * |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)| := by
        have h1 : δ n c - d n ≤ 0 := by linarith [hδd n c]
        have h2 : (δ n c - d n) *
              (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
                ((n + 1 : ℕ) : ℝ)) ≤
            |(δ n c - d n) *
              (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
                ((n + 1 : ℕ) : ℝ))| := le_abs_self _
        rw [abs_mul, abs_of_nonpos h1] at h2
        have h3 : (d n - δ n c) *
              |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
                ((n + 1 : ℕ) : ℝ)| ≤
            d n * |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
                ((n + 1 : ℕ) : ℝ)| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          linarith [hδ0 n c]
        linarith
      have hid : (1 + δ n c) *
            (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) + δ n c =
          (1 + d n) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) +
            (δ n c - d n) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) + δ n c := by
        ring
      rw [hid]
      linarith [hMabs, hδd n c]
    have hsum : (∑ c, ((1 + δ n c) *
          (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)) + δ n c)) ≤
        (∑ c, ((1 + d n) *
          (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)) +
          d n * |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)| + d n)) :=
      Finset.sum_le_sum fun c _ => hterm c
    have hsum_eq : (∑ c, ((1 + d n) *
          (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)) +
          d n * |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)| + d n)) =
        (1 + d n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)) +
          d n * (∑ c, |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
            ((n + 1 : ℕ) : ℝ)|) +
          d n * (Fintype.card ι : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    have hCbound : d n * (∑ c, |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
          ((n + 1 : ℕ) : ℝ)|) ≤ d n * C :=
      mul_le_mul_of_nonneg_left (hModelBound n) (hd0 n)
    rw [hsum_eq] at hsum
    calc (∫ ξ, supportedDistancePressure μ ν K hK hμ hν
          (fun i => X n i ξ) (fun j => Y n j ξ) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n)
        ≤ (∑ c, ((1 + δ n c) *
            (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) + δ n c)) +
            (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
              Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) := h
      _ ≤ ((1 + d n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) +
            d n * (∑ c, |modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)|) +
            d n * (Fintype.card ι : ℝ)) +
            (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
              Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) := by
          linarith [hsum]
      _ ≤ ((1 + d n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) + d n * C + d n * (Fintype.card ι : ℝ)) +
            (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
              Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) := by
          linarith [hCbound]
      _ = (1 + d n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
              ((n + 1 : ℕ) : ℝ)) + d n * (C + (Fintype.card ι : ℝ)) +
            (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
              Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) := by
          ring
  have hlim : Tendsto (fun n : ℕ =>
      (1 + d n) * (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + d n * (C + (Fintype.card ι : ℝ)) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)))
      atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    have h1 : Tendsto (fun n : ℕ => (1 + d n) *
        (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
          ((n + 1 : ℕ) : ℝ))) atTop
        (𝓝 ((1 + 0) * (∑ c, (w c : ℝ) * p c t))) :=
      ((tendsto_const_nhds.add hd).mul hmodel')
    have h2 : Tendsto (fun n : ℕ => d n * (C + (Fintype.card ι : ℝ))) atTop
        (𝓝 (0 * (C + (Fintype.card ι : ℝ)))) :=
      hd.mul tendsto_const_nhds
    have h3 : Tendsto (fun n : ℕ =>
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ))) atTop (𝓝 0) :=
      hBlim
    simpa using (h1.add h2).add h3
  have hev := hlim.eventually
    (Iio_mem_nhds (lt_add_of_pos_right (∑ c, (w c : ℝ) * p c t) hε))
  filter_upwards [hev] with n hn
  exact (hmain n).trans hn.le

end OTSelector.Pressure

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **Relaxed physical Finsler expectation upper bound.**

This is the analogue of `finslerExpectationUpperBound_of_block_model` with the
exact per-cell comparison replaced by the relative comparison

`∫ ξ, block n c ξ ∂P n ≤ (1 + δ n) * (modelBlockSum_c / (n + 1)) + δ n`

with `δ n ≥ 0` and `δ n → 0`.  All other physical inputs are unchanged: the
block functions are the concrete normalized `maxCardValue` tile blocks, the
repair constant is the concrete `(n + 1) ^ (2 / q) * (2 diam K) + |t| ‖f‖`, and
the integrability of the physical pressure is derived from the marginal laws.

The relative error `δ` is exactly the slot where the frozen-block comparison
`physical ≤ (1 + 2 εₙ) * frozen + probe error` is meant to be inserted: choose
`δ n` to dominate `2 εₙ` and the normalized probe error, both of which vanish
as `n → ∞`. -/
theorem finslerExpectationUpperBound_of_relaxed_block_model
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (φ : M → ℝ)
    (hφ : let _instUpperPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → I) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : ι → A → B → (Fin q → ℝ) → ℝ} {g : ι → A → B → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (blockS blockT : ∀ n, Fin (n + 1) → Ω n → ι)
    (hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (P n))
    (hintCount : ∀ n c, Integrable (fun ξ =>
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hblock : ∀ n c, ∫ ξ,
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂P n ≤
      (1 + δ n) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε := by
  intro ε hε
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hφ' : LipschitzWith 1 φ := hφ
  -- Almost-sure membership in the compact carrier.
  have hXK : ∀ n, ∀ᵐ ξ ∂P n, ∀ i, X n i ξ ∈ K := by
    intro n
    apply ae_all_iff.mpr
    intro i
    exact ae_of_ae_map (hX n i).aemeasurable (by rw [hXlaw n i]; exact hμ)
  have hYK : ∀ n, ∀ᵐ ξ ∂P n, ∀ j, Y n j ξ ∈ K := by
    intro n
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (hY n j).aemeasurable (by rw [hYlaw n j]; exact hν)
  -- The concrete physical repair constant.
  let Bnd : ℕ → ℝ := fun n =>
    (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) * (2 * finslerDiam F K) +
      |t| * (‖f‖₊ : ℝ)
  have hBnd_eq : ∀ n, Bnd n =
      (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) * (2 * finslerDiam F K) +
        |t| * (‖f‖₊ : ℝ) := fun n => rfl
  have hBnd0 : ∀ n, 0 ≤ Bnd n := by
    intro n
    have h1 : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h2 : 0 ≤ finslerDiam F K := by
      simpa only [finslerDiam] using Metric.diam_nonneg (s := K)
    have h3 : 0 ≤ |t| * (‖f‖₊ : ℝ) :=
      mul_nonneg (abs_nonneg t) (by positivity)
    rw [hBnd_eq n]
    exact add_nonneg (mul_nonneg h1 (by linarith)) h3
  -- Integrability of the physical supported pressure.
  have hintTotal : ∀ n, Integrable (fun ξ =>
      Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t) (P n) := by
    intro n
    exact Pressure.integrable_supportedDistancePressure (P := P n) (n := n + 1)
      μ ν K hK.measurableSet hμ hν
      (fun i (ξ : Ω n) => X n i ξ) (fun j (ξ : Ω n) => Y n j ξ)
      (fun i => hX n i) (fun j => hY n j)
      φ hφ' hφ'.continuous _ f t (Nat.succ_pos n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) hK (hXK n) (hYK n)
  -- The concrete deterministic tile repair.
  have hrepair : ∀ n, ∀ᵐ ξ ∂P n,
      Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ≤
      (∑ c, finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) +
      (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
        tileLabelCountDiscrepancy (blockS n) (blockT n) ξ := by
    intro n
    have h := finslerSupportedPressure_tile_repair_ae (F := F) (n := n)
      μ ν K hK.measurableSet hμ hν
      (blockS n) (blockT n) (X n) (Y n) φ hφ
      (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) f t hK (P n) (hXK n) (hYK n)
    simpa only [finslerSupportedPressure, hBnd_eq n] using h
  -- The normalized physical repair constant vanishes after normalization.
  have hBlim : Tendsto (fun n =>
      (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
        Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ))) atTop (𝓝 0) := by
    have hbase := tendsto_binomial_repairError_zero (q := q) hq
      (2 * finslerDiam F K) (‖f‖₊ : ℝ) t (Fintype.card ι)
    have hshift : Tendsto (fun n : ℕ =>
        ((((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)) * (2 * finslerDiam F K) +
            |t| * (‖f‖₊ : ℝ)) / ((n + 1 : ℕ) : ℝ)) *
          (Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) / 2))
        atTop (𝓝 0) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr hbase
    refine hshift.congr' ?_
    filter_upwards with n
    rw [hBnd_eq n]
    ring
  -- The generic relaxed block-model assembly.
  have h := Pressure.supportedPressure_integral_le_weighted_sum_of_relaxed_block_model
    (M := M) (Ω := Ω) P μ ν K hK.measurableSet hμ hν X Y φ f t q hq hwsum hwpos
    hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    (fun n c ξ => finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet
      hμ hν (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ)
    (fun n c ξ => tileSourceCount (blockS n) c ξ)
    (fun n c ξ => tileTargetCount (blockT n) c ξ)
    Bnd hBnd0 hrepair hBlim hintTotal hintBlock hintCount hcount δ hδ0 hδ hblock
  simpa only [finslerSupportedPressure] using h ε hε

/-- **The relaxed `hupper` interface.**

If the relaxed per-cell comparison with a vanishing relative error holds, the
resulting normalized expected Finsler supported pressure is eventually at most
the weighted sum `∑ c, w c * p c t` plus any `ε > 0`.  If the target pressure
agrees with that weighted sum at the fixed probe and tilt, this is exactly the
`hupper` clause of `exists_finsler_pressure_producer_of_squeeze`. -/
theorem finsler_hupper_of_relaxed_block_model
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (φ : M → ℝ)
    (hφ : let _instUpperPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → I) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : ι → A → B → (Fin q → ℝ) → ℝ} {g : ι → A → B → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (blockS blockT : ∀ n, Fin (n + 1) → Ω n → ι)
    (hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (P n))
    (hintCount : ∀ n c, Integrable (fun ξ =>
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hblock : ∀ n c, ∫ ξ,
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂P n ≤
      (1 + δ n) * (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hpressure : pressure f t = ∑ c, (w c : ℝ) * p c t) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        pressure f t + ε := by
  have h := finslerExpectationUpperBound_of_relaxed_block_model
    (F := F) hcomplete μ ν K hK hμ hν P X Y hX hY hXlaw hYlaw φ hφ f t q hq
    w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    blockS blockT hintBlock hintCount hcount δ hδ0 hδ hblock
  intro ε hε
  filter_upwards [h ε hε] with n hn
  rwa [hpressure]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
