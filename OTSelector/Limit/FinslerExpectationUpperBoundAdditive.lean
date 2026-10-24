import OTSelector.Limit.FinslerExpectationUpperBound

/-!
# Additive per-cell relaxation for the Finsler expectation upper bound

The module `OTSelector.Limit.FinslerExpectationUpperBoundRelaxed` weakens the
exact per-cell comparison of the upper-bound assembly to the multiplicative
form

`∫ block ≤ (1 + δ n) * (modelBlockSum_c / (n + 1)) + δ n`.

That form is adequate when the normalized model block sums `M_c` are
nonnegative, but not in general: the model block sums are **signed** (the marked
block expectation contains the tilt term), and for negative `M_c` the
multiplicative factor `(1 + δ)` decreases the bound, so an additive error from
the frozen comparison cannot be absorbed.

The frozen-block comparison actually gives

`physical ≤ (1 + 2 εₙ) * M_c + cₙ`

with a vanishing relative error `2 εₙ` and a vanishing additive error `cₙ`.
The correct interface for this shape is *additive*:

`∫ block ≤ M_c + δ n` with `δ n ≥ 0`, `δ n → 0`,

where `δ n` dominates `2 εₙ * |M_c| + cₙ`.  For signed `M_c` this is exactly
the right form: adding a vanishing allowance never decreases the bound.

This module proves:

* `supportedPressure_integral_le_weighted_sum_of_additive_block_model`, the
  generic additive assembly.  Summing gives
  `∑ c, (M_c + δ n) = (∑ c, M_c) + δ n * #ι`, which converges to
  `∑ c, w c * p c t` because the normalized model block sums converge and
  `δ n → 0`; the repair term is unchanged and vanishes after normalization.
* `finslerExpectationUpperBound_of_additive_block_model`, the physical Finsler
  specialization with the concrete normalized `maxCardValue` tile blocks.
* `finsler_hupper_of_additive_block_model`, the `hupper` interface corollary.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BigOperators BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Additive block-model assembly.**

This is the analogue of
`supportedPressure_integral_le_weighted_sum_of_block_model` in which the exact
per-cell comparison `hblock` is replaced by the additive comparison

`∫ ξ, block n c ξ ∂P n ≤ modelBlockSum ... (n + 1) / (n + 1) + δ n`

for all sufficiently large `n`, with a nonnegative error `δ n` tending to zero.
The conclusion is unchanged:
for every `ε > 0` the normalized expected physical pressure is eventually at
most `∑ c, w c * p c t + ε`.

Unlike the multiplicative relaxation, this form is stable under the sign of the
model block sums, which is exactly what the frozen-block comparison
`physical ≤ (1 + 2 εₙ) M_c + cₙ` requires. -/
theorem supportedPressure_integral_le_weighted_sum_of_additive_block_model
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι]
    {w : ι → unitInterval} (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
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
    (hblock : ∀ᶠ n in atTop, ∀ c, ∫ ξ, block n c ξ ∂P n ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) + δ n) :
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
  -- The per-sample expectation bound with the additive comparison.
  have hmain : ∀ᶠ n in atTop, (∫ ξ, supportedDistancePressure μ ν K hK hμ hν
      (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n * (Fintype.card ι : ℝ) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)) := by
    filter_upwards [hblock] with n hnBlock
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
      (fun c => modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) + δ n)
      (fun c => hnBlock c)
    have hsum : (∑ c, (modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
          ((n + 1 : ℕ) : ℝ) + δ n)) =
        (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
          ((n + 1 : ℕ) : ℝ)) + δ n * (Fintype.card ι : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hsum] at h
    exact h
  -- The additive model bound converges to the weighted sum of the local limits.
  have hlim : Tendsto (fun n : ℕ =>
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + δ n * (Fintype.card ι : ℝ) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)))
      atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    have h2 : Tendsto (fun n : ℕ => δ n * (Fintype.card ι : ℝ)) atTop
        (𝓝 (0 * (Fintype.card ι : ℝ))) :=
      hδ.mul tendsto_const_nhds
    have h3 : Tendsto (fun n : ℕ =>
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ))) atTop (𝓝 0) :=
      hBlim
    simpa using (hmodel'.add h2).add h3
  have hev := hlim.eventually
    (Iio_mem_nhds (lt_add_of_pos_right (∑ c, (w c : ℝ) * p c t) hε))
  filter_upwards [hev, hmain] with n hn hnMain
  exact hnMain.trans hn.le

end OTSelector.Pressure

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **Additive physical Finsler expectation upper bound.**

This is the analogue of `finslerExpectationUpperBound_of_block_model` with the
exact per-cell comparison replaced by the additive comparison

`∫ ξ, block n c ξ ∂P n ≤ modelBlockSum_c / (n + 1) + δ n`

for all sufficiently large `n`, with `δ n ≥ 0` and `δ n → 0`. This matches the frozen-block
comparison `physical ≤ (1 + 2 εₙ) M_c + cₙ`: choose `δ n` to dominate
`2 εₙ * sup_c |M_c| + cₙ`, which vanishes because `εₙ → 0`, `cₙ → 0`, and the
normalized model block sums are uniformly bounded (they converge).  All other
physical inputs are unchanged from the exact-relaxation module. -/
theorem finslerExpectationUpperBound_of_additive_block_model
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
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
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
    (hblock : ∀ᶠ n in atTop, ∀ c, ∫ ξ,
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂P n ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) + δ n) :
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
  -- The generic additive block-model assembly.
  have h := Pressure.supportedPressure_integral_le_weighted_sum_of_additive_block_model
    (M := M) (Ω := Ω) P μ ν K hK.measurableSet hμ hν X Y φ f t q hq hwsum hwpos
    hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    (fun n c ξ => finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet
      hμ hν (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ)
    (fun n c ξ => tileSourceCount (blockS n) c ξ)
    (fun n c ξ => tileTargetCount (blockT n) c ξ)
    Bnd hBnd0 hrepair hBlim hintTotal hintBlock hintCount hcount δ hδ0 hδ hblock
  simpa only [finslerSupportedPressure] using h ε hε

/-- **The additive `hupper` interface.**

If the additive per-cell comparison with a vanishing additive error holds, the
normalized expected Finsler supported pressure is eventually at most the
weighted sum `∑ c, w c * p c t` plus any `ε > 0`.  If the target pressure agrees
with that weighted sum at the fixed probe and tilt, this is exactly the `hupper`
clause of `exists_finsler_pressure_producer_of_squeeze`. -/
theorem finsler_hupper_of_additive_block_model
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
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
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
    (hblock : ∀ᶠ n in atTop, ∀ c, ∫ ξ,
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂P n ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) + δ n)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hpressure : pressure f t = ∑ c, (w c : ℝ) * p c t) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        pressure f t + ε := by
  have h := finslerExpectationUpperBound_of_additive_block_model
    (F := F) hcomplete μ ν K hK hμ hν P X Y hX hY hXlaw hYlaw φ hφ f t q hq
    w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    blockS blockT hintBlock hintCount hcount δ hδ0 hδ hblock
  intro ε hε
  filter_upwards [h ε hε] with n hn
  rwa [hpressure]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
