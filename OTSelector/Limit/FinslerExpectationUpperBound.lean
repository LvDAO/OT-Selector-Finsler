import OTSelector.Limit.FinslerPressureSqueeze
import OTSelector.Probability.PhysicalUpperBoundAssembly
import OTSelector.Finite.PerturbedTileRepair

/-!
# The expectation upper bound of the physical Finsler pressure

This module advances the expectation upper-bound input (`hupper`) of
`exists_finsler_pressure_producer_of_squeeze`.  The compiled interface
`exists_physical_upper_bound_of_block_model` already turns

* a deterministic tile repair,
* the binomial label-count discrepancy, and
* a per-cell comparison of the physical tile block expectation with the marked
  model block expectation

into the normalized expected-value bound at the weighted sum of the local
marked pressure limits.  What has been missing is the *physical* side of that
interface: the actual normalized supported pressure of the ambient iid arrays,
the concrete tile block given by `maxCardValue` of the tilted block matrix, and
the exact scaling `(n + 1) ^ (2 / q)` used by the selector.

The first part of the file proves the concrete deterministic tile repair for
the supported pressure (`supportedDistancePressure_mul_le_tileBlockSum_add_repair`
and its Finsler specialization).  The second part assembles the normalized
expectation upper bound with the physical normalization of the selector and
identifies its limit with the weighted sum of the local marked pressure limits.
The only remaining inputs are stated as explicit hypotheses:

* `hblock`, the per-cell comparison of the physical block expectation with the
  marked model block (the geometric conditional-law/frozen-kernel gap);
* `hcount`, the binomial count-discrepancy bound for the tile labels;
* the routine integrability of the physical block and of the label counts.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BigOperators BoundedContinuousFunction unitInterval

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The physical tile block of the supported pressure: the least cost of a
maximum-cardinality matching inside one label block of the tilted physical
matrix `k * (dist - φ y + φ x) + t * f`. -/
noncomputable def supportedTileBlock
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin n → ι) (X Y : Fin n → M) (φ : M → ℝ) (k : ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι) : ℝ :=
  PartialMatching.maxCardValue
    (blockCost blockS blockT
      (perturbedEdgeCost
        (fun i j => k * distanceSlackEdgeCost X Y φ i j)
        (fun i j => f (supportProjection μ K hK hμ (X i),
          supportProjection ν K hK hν (Y j))) t) c)

/-- The uniform upper bound on the tilted physical edge cost of a tile. -/
theorem supportedTileEdgeCost_le
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {X Y : Fin n → M} {φ : M → ℝ} (hφ : LipschitzWith 1 φ)
    {K' : Set M} (hK'c : IsCompact K') (hXK : ∀ i, X i ∈ K') (hYK : ∀ j, Y j ∈ K')
    {k : ℝ} (hk : 0 ≤ k) (f : (K × K) →ᵇ ℝ) (t : ℝ) (i j : Fin n) :
    k * distanceSlackEdgeCost X Y φ i j +
        t * f (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j)) ≤
      k * (2 * Metric.diam K') + |t| * (‖f‖₊ : ℝ) := by
  have hd : dist (X i) (Y j) ≤ Metric.diam K' :=
    Metric.dist_le_diam_of_mem hK'c.isBounded (hXK i) (hYK j)
  have hp : φ (X i) - φ (Y j) ≤ dist (X i) (Y j) := by
    have h := hφ.dist_le_mul (X i) (Y j)
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at h
    exact (abs_le.mp h).2
  have hslack : distanceSlackEdgeCost X Y φ i j ≤ 2 * Metric.diam K' := by
    unfold distanceSlackEdgeCost
    linarith
  have h1 : k * distanceSlackEdgeCost X Y φ i j ≤ k * (2 * Metric.diam K') :=
    mul_le_mul_of_nonneg_left hslack hk
  have h2 : t * f (supportProjection μ K hK hμ (X i),
      supportProjection ν K hK hν (Y j)) ≤ |t| * (‖f‖₊ : ℝ) := by
    have hprobe : |f (supportProjection μ K hK hμ (X i),
        supportProjection ν K hK hν (Y j))| ≤ (‖f‖₊ : ℝ) := by
      simpa only [coe_nnnorm, Real.norm_eq_abs] using
        f.norm_coe_le_norm (supportProjection μ K hK hμ (X i),
          supportProjection ν K hK hν (Y j))
    calc t * f (supportProjection μ K hK hμ (X i),
          supportProjection ν K hK hν (Y j))
        ≤ |t * f (supportProjection μ K hK hμ (X i),
            supportProjection ν K hK hν (Y j))| := le_abs_self _
      _ = |t| * |f (supportProjection μ K hK hμ (X i),
            supportProjection ν K hK hν (Y j))| := abs_mul _ _
      _ ≤ |t| * (‖f‖₊ : ℝ) :=
          mul_le_mul_of_nonneg_left hprobe (abs_nonneg t)
  linarith

/-- **Concrete deterministic tile repair for the supported pressure.**  For
points of the compact carrier, the un-normalized supported pressure is at most
the sum of the physical tile block values plus the uniform tilted edge bound
times half the total label-count discrepancy. -/
theorem supportedDistancePressure_mul_le_tileBlockSum_add_repair
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin n → ι) (X Y : Fin n → M) (φ : M → ℝ)
    (hφ : LipschitzWith 1 φ) (k : ℝ) (hk : 0 ≤ k)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (hKc : IsCompact K) (hXK : ∀ i, X i ∈ K) (hYK : ∀ j, Y j ∈ K) (hn : 0 < n) :
    (n : ℝ) * supportedDistancePressure μ ν K hK hμ hν X Y φ k f t ≤
      (∑ c, supportedTileBlock μ ν K hK hμ hν blockS blockT X Y φ k f t c) +
        (k * (2 * Metric.diam K) + |t| * (‖f‖₊ : ℝ)) *
          (1 / 2 * ∑ c,
            |((blockSizeS blockS c : ℕ) : ℝ) - ((blockSizeT blockT c : ℕ) : ℝ)|) := by
  classical
  have hdiam0 : (0 : ℝ) ≤ 2 * Metric.diam K := by
    have := Metric.diam_nonneg (s := K)
    linarith
  have hB0 : 0 ≤ k * (2 * Metric.diam K) + |t| * (‖f‖₊ : ℝ) :=
    add_nonneg (mul_nonneg hk hdiam0) (mul_nonneg (abs_nonneg t) (by positivity))
  have hB : ∀ i j : Fin n,
      k * distanceSlackEdgeCost X Y φ i j +
          t * f (supportProjection μ K hK hμ (X i),
            supportProjection ν K hK hν (Y j)) ≤
        k * (2 * Metric.diam K) + |t| * (‖f‖₊ : ℝ) :=
    fun i j => supportedTileEdgeCost_le μ ν K hK hμ hν hφ hKc hXK hYK hk f t i j
  have hmain := PartialMatching.perturbedAssignmentValue_le_sum_block_add_discrepancy
    blockS blockT
    (fun i j => k * distanceSlackEdgeCost X Y φ i j)
    (fun i j => f (supportProjection μ K hK hμ (X i),
      supportProjection ν K hK hν (Y j))) t _ hB0 hB
  have hval : (n : ℝ) * supportedDistancePressure μ ν K hK hμ hν X Y φ k f t =
      perturbedAssignmentValue
        (fun i j => k * distanceSlackEdgeCost X Y φ i j)
        (fun i j => f (supportProjection μ K hK hμ (X i),
          supportProjection ν K hK hν (Y j))) t := by
    rw [supportedDistancePressure]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')
  rw [hval]
  simpa only [supportedTileBlock] using hmain

end OTSelector.Pressure

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Normalized expectation upper bound from the per-cell block model.**

For the physical supported pressure of the ambient iid arrays at the selector
scale `(n + 1) ^ (2 / q)`, the deterministic tile repair, the binomial count
discrepancy, and the per-cell comparison with the marked model block give the
normalized expected-value bound at the weighted sum of the local marked
pressure limits.  The normalization is exactly the selector's: the physical
block is divided by the sample size `n + 1` and the model block sum is compared
at the same size. -/
theorem supportedPressure_integral_le_weighted_sum_of_block_model
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
    (hblock : ∀ n c, ∫ ξ, block n c ξ ∂P n ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) :
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
  -- The per-sample expectation bound at the physical normalization.
  have hmain : ∀ n, (∫ ξ, supportedDistancePressure μ ν K hK hμ hν
      (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) +
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
      (fun c => modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ))
      (fun c => hblock n c)
    exact h
  -- The upper comparison converges to the weighted sum of the local limits.
  have hlim : Tendsto (fun n : ℕ =>
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) +
        (Bnd n / ((n + 1 : ℕ) : ℝ)) * (1 / 2) *
          Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ)))
      atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
    simpa using hmodel'.add hBlim
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

/-- The physical tile block of the Finsler supported pressure, evaluated in the
Finsler length metric.  It is the least cost of a maximum-cardinality matching
inside one label block of the tilted physical matrix
`k (dist - φ y + φ x) + t f`. -/
noncomputable def finslerTileBlock
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → ι) (X Y : Fin (n + 1) → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι) : ℝ :=
  let _instFinslerTileBlockMetric : MetricSpace M := F.metricSpace
  Pressure.supportedTileBlock μ ν K hK hμ hν blockS blockT X Y φ k f t c

/-- The carrier diameter measured in the Finsler length metric. -/
noncomputable def finslerDiam (F : ContinuousFinslerNorm E M) (K : Set M) : ℝ :=
  let _instFinslerDiamMetric : MetricSpace M := F.metricSpace
  Metric.diam K

/-- The normalized physical tile block of the Finsler supported pressure at
sample size `n + 1`. -/
noncomputable def finslerNormalizedTileBlock
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι) (ξ : Ω n) : ℝ :=
  finslerTileBlock (ι := ι) F μ ν K hK hμ hν
    (fun i => blockS i ξ) (fun j => blockT j ξ)
    (fun i => X i ξ) (fun j => Y j ξ) φ k f t c / ((n + 1 : ℕ) : ℝ)

/-- The source label count of one tile. -/
noncomputable def tileSourceCount {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS : Fin (n + 1) → Ω n → ι) (c : ι) (ξ : Ω n) : ℝ :=
  ((blockSizeS (fun i => blockS i ξ) c : ℕ) : ℝ)

/-- The target label count of one tile. -/
noncomputable def tileTargetCount {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockT : Fin (n + 1) → Ω n → ι) (c : ι) (ξ : Ω n) : ℝ :=
  ((blockSizeT (fun j => blockT j ξ) c : ℕ) : ℝ)

/-- The total absolute label-count discrepancy of a finite tile family. -/
noncomputable def tileLabelCountDiscrepancy {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (ξ : Ω n) : ℝ :=
  ∑ c, |tileSourceCount blockS c ξ - tileTargetCount blockT c ξ|

set_option maxHeartbeats 1600000 in
/-- **Concrete deterministic tile repair for the Finsler supported pressure.**

On the almost-sure event that both samples lie in the compact carrier, the
normalized Finsler supported pressure is at most the sum of the normalized
physical tile blocks plus the normalized uniform tilted edge bound times half
the total label-count discrepancy.  The edge constant is
`k * (2 diam K) + |t| ‖f‖`, the physical analogue of the marked-model constant
`(n + 1) ^ (2 / q) Kb + |t| G`. -/
theorem finslerSupportedPressure_tile_repair_ae
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (blockS blockT : Fin (n + 1) → Ω n → ι)
    (X Y : Fin (n + 1) → Ω n → M) (φ : M → ℝ)
    (hφ : let _instRepairPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (k : ℝ) (hk : 0 ≤ k) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (hKc : IsCompact K)
    (P : Measure (Ω n)) [IsProbabilityMeasure P]
    (hXK : ∀ᵐ ξ ∂P, ∀ i, X i ξ ∈ K)
    (hYK : ∀ᵐ ξ ∂P, ∀ j, Y j ξ ∈ K) :
    ∀ᵐ ξ ∂P,
      finslerSupportedPressure F μ ν K hK hμ hν (fun i => X i ξ) (fun j => Y j ξ)
        φ k f t ≤
      (∑ c, finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
        blockS blockT X Y φ k f t c ξ) +
      ((k * (2 * finslerDiam F K) + |t| * (‖f‖₊ : ℝ)) / ((n + 1 : ℕ) : ℝ)) *
        (1 / 2) * tileLabelCountDiscrepancy blockS blockT ξ := by
  letI : MetricSpace M := F.metricSpace
  have hφ' : LipschitzWith 1 φ := hφ
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  filter_upwards [hXK, hYK] with ξ hx hy
  have h := Pressure.supportedDistancePressure_mul_le_tileBlockSum_add_repair
    μ ν K hK hμ hν (fun i => blockS i ξ) (fun j => blockT j ξ)
    (fun i => X i ξ) (fun j => Y j ξ) φ hφ' k hk f t hKc hx hy (Nat.succ_pos n)
  simp only [finslerSupportedPressure]
  have hdiv := div_le_div_of_nonneg_right h hpos.le
  rw [mul_div_cancel_left₀ _ hpos.ne'] at hdiv
  have hsum : (∑ c, Pressure.supportedTileBlock μ ν K hK hμ hν
        (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
        φ k f t c +
        (k * (2 * Metric.diam K) + |t| * (‖f‖₊ : ℝ)) *
          (1 / 2 * ∑ c, |((blockSizeS (fun i => blockS i ξ) c : ℕ) : ℝ) -
            ((blockSizeT (fun j => blockT j ξ) c : ℕ) : ℝ)|)) / ((n + 1 : ℕ) : ℝ) =
      (∑ c, Pressure.supportedTileBlock μ ν K hK hμ hν
        (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
        φ k f t c / ((n + 1 : ℕ) : ℝ)) +
        ((k * (2 * Metric.diam K) + |t| * (‖f‖₊ : ℝ)) / ((n + 1 : ℕ) : ℝ)) *
          (1 / 2 * ∑ c, |((blockSizeS (fun i => blockS i ξ) c : ℕ) : ℝ) -
            ((blockSizeT (fun j => blockT j ξ) c : ℕ) : ℝ)|) := by
    rw [add_div, Finset.sum_div]
    ring
  rw [hsum] at hdiv
  refine hdiv.trans (le_of_eq ?_)
  simp only [finslerNormalizedTileBlock, finslerTileBlock, finslerDiam,
    tileLabelCountDiscrepancy, tileSourceCount, tileTargetCount]
  ring

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

set_option maxHeartbeats 1600000 in
/-- **Expectation upper bound for the physical Finsler pressure from the block
model.**

For a fixed bounded probe `f` and tilt `t`, the normalized expected supported
Finsler pressure at the selector scale `(n + 1) ^ (2 / q)` is eventually at most
the weighted sum of the local marked pressure limits, plus any `ε > 0`.

The physical side is completely discharged: the block functions are the actual
normalized `maxCardValue` tile blocks `finslerNormalizedTileBlock`, the repair
uses the concrete constant `(n + 1) ^ (2 / q) * (2 diam K) + |t| ‖f‖`, and the
integrability of the physical pressure is derived from the iid marginal laws.
The explicit hypotheses are the per-cell comparison `hblock`, the binomial
count bound `hcount`, and the routine integrability of the physical block and
the label counts. -/
theorem finslerExpectationUpperBound_of_block_model
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
    (hblock : ∀ n c, ∫ ξ,
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂P n ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) :
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
  -- The generic block-model assembly.
  have h := Pressure.supportedPressure_integral_le_weighted_sum_of_block_model
    (M := M) (Ω := Ω) P μ ν K hK.measurableSet hμ hν X Y φ f t q hq hwsum hwpos
    hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    (fun n c ξ => finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet
      hμ hν (blockS n) (blockT n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ)
    (fun n c ξ => tileSourceCount (blockS n) c ξ)
    (fun n c ξ => tileTargetCount (blockT n) c ξ)
    Bnd hBnd0 hrepair hBlim hintTotal hintBlock hintCount hcount hblock
  simpa only [finslerSupportedPressure] using h ε hε

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **The `hupper` interface.**

If the normalized expected Finsler supported pressure at the selector scale is
eventually at most a constant `S` plus any `ε > 0`, and the target pressure
agrees with `S` at the fixed probe and tilt, then this is exactly the `hupper`
clause of `exists_finsler_pressure_producer_of_squeeze` for that pressure. -/
theorem finsler_hupper_of_integral_bound
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (φ : M → ℝ) (k : ℕ → ℝ)
    (f : (K × K) →ᵇ ℝ) (t S : ℝ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (hpressure : pressure f t = S)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ (k n) f t ∂P n) ≤ S + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ (k n) f t ∂P n) ≤
        pressure f t + ε := by
  intro ε hε
  filter_upwards [h ε hε] with n hn
  rwa [hpressure]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
