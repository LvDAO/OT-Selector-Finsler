import OTSelector.Reconstruction.FinslerConcreteUpperBlocks
import OTSelector.Limit.FinslerExpectationUpperBoundAdditive

/-!
# The concrete upper bound with cover-fixed geometric and law errors

Physical tile repair and the aggregate relative comparison give a fixed bias
`2 ε Bnd + |t| B`, together with the law-transport bias.  The cover remains
fixed while the marked binomial block limit is taken.  Only afterwards is the
cover refined.  No uniform-in-sample-size kernel bound, exact actual cell law,
or vanishing geometric error for one fixed cover is required.

The local pressures in this module are the unrestricted marked matching
pressures.  Their identification with a conditional pressure with a clock-order
constraint requires a separate legality and recovery theorem.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BigOperators BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Limit

/-- The normalized marked binomial block sum converges at sample size `n+1`.
The bound on `kin` is quadratic in displacement and does not bound the scaled
finite-sample kernel uniformly in `n`. -/
theorem tendsto_normalized_modelBlockSum
    (q : ℕ) (hq : 4 < q) {ι A B : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace B]
    {w : ι → unitInterval} (hwpos : ∀ c, 0 < (w c : ℝ))
    {kin : ι → A → B → (Fin q → ℝ) → ℝ} {g : ι → A → B → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B ↦ kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ c t, Tendsto
      (fun R ↦ markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t))) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ ∑ c, modelBlockSum q t (kin c) (g c)
      (α c) (β c) (w c) (n + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (∑ c, (w c : ℝ) * p c t)) := by
  have h := tendsto_binomial_tileBlockPressure_sum q hq hwpos hCb0 hG0
    hkin hkin_bound hg hgb α β p hp t
  exact (Filter.tendsto_add_atTop_iff_nat 1).mpr h

/-- Fixed geometric bias and law bias are retained when taking the sample-size
limit.  Signed model pressures are permitted. -/
theorem eventually_le_add_fixed_bias
    {actual model relative lawError repair : ℕ → ℝ}
    {limit ε lawBias t B G Bnd : ℝ}
    (hmodel : Tendsto model atTop (𝓝 limit))
    (hrelative : Tendsto relative atTop (𝓝 (2 * ε)))
    (hlaw : Tendsto lawError atTop (𝓝 lawBias))
    (hrepair : Tendsto repair atTop (𝓝 0))
    (hε : 0 ≤ ε) (hBnd : limit + |t| * G ≤ Bnd)
    (hactual : ∀ n, actual n ≤
      (1 + relative n) * (model n + lawError n) +
        (|t| * B + relative n * (|t| * G)) + repair n) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      actual n ≤ limit + (2 * ε * Bnd + |t| * B) +
        (1 + 2 * ε) * lawBias + δ := by
  intro δ hδ
  have hlim : Tendsto (fun n ↦
      (1 + relative n) * (model n + lawError n) +
        (|t| * B + relative n * (|t| * G)) + repair n) atTop
      (𝓝 ((1 + 2 * ε) * (limit + lawBias) +
        (|t| * B + 2 * ε * (|t| * G)))) := by
    simpa using (((tendsto_const_nhds.add hrelative).mul (hmodel.add hlaw)).add
      (tendsto_const_nhds.add (hrelative.mul_const (|t| * G)))).add hrepair
  have hbound : (1 + 2 * ε) * (limit + lawBias) +
      (|t| * B + 2 * ε * (|t| * G)) ≤
      limit + (2 * ε * Bnd + |t| * B) + (1 + 2 * ε) * lawBias := by
    nlinarith [mul_le_mul_of_nonneg_left hBnd (show 0 ≤ 2 * ε by positivity)]
  filter_upwards [hlim.eventually (Iio_mem_nhds (lt_add_of_pos_right
    ((1 + 2 * ε) * (limit + lawBias) + (|t| * B + 2 * ε * (|t| * G))) hδ))]
    with n hn
  linarith [hactual n]

/-- Refining the cover after taking each fixed-cover limit removes the fixed
bias.  The index type may include both a chosen core and its finite partition. -/
theorem eventually_le_of_cover_refinement
    {actual : ℕ → ℝ} {pressure : ℝ} {Cover : Type*}
    (localPressure bias : Cover → ℝ)
    (hfixed : ∀ T δ, 0 < δ → ∀ᶠ n in atTop,
      actual n ≤ localPressure T + bias T + δ)
    (hcover : ∀ δ : ℝ, 0 < δ → ∃ T,
      localPressure T + bias T ≤ pressure + δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, actual n ≤ pressure + δ := by
  intro δ hδ
  obtain ⟨T, hT⟩ := hcover (δ / 2) (half_pos hδ)
  filter_upwards [hfixed T (δ / 2) (half_pos hδ)] with n hn
  linarith

end OTSelector.Limit

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- Physical repair, a.e. relative freezing, actual-to-product law transport,
and the marked binomial limit give the fixed-cover expectation bound.  The
law transport compares the actual frozen block sum to the frozen product
model; it does not assert a uniform law for the actual cell population. -/
theorem finslerExpectationUpperBound_concrete_fixed_cover
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (sample n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (sample n).map (Y n i) = (ν : Measure M))
    (φ : M → ℝ)
    (hφ : let _instConcreteUpperMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : ι → A → B → (Fin q → ℝ) → ℝ} {g : ι → A → B → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B ↦ kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure B)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ c t, Tendsto
      (fun R ↦ markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (s z : ∀ n, Fin (n + 1) → Ω n → ι)
    (frozen modelProbe : ∀ n, Ω n → Fin (n + 1) → Fin (n + 1) → ℝ)
    (relative lawError : ℕ → ℝ) (ε probeError lawBias Bnd : ℝ)
    (hε : 0 ≤ ε) (herror : 0 ≤ probeError)
    (hrelative0 : ∀ n, 0 ≤ relative n)
    (hrelative : Tendsto relative atTop (𝓝 (2 * ε)))
    (hlawError : Tendsto lawError atTop (𝓝 lawBias))
    (hBnd : (∑ c, (w c : ℝ) * p c t) + |t| * G ≤ Bnd)
    (hedge : ∀ n, ∀ᵐ ξ ∂sample n, ∀ c i j, s n i ξ = c → z n j ξ = c →
      0 ≤ frozen n ξ i j ∧
      |finslerTileKinetic F (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j - frozen n ξ i j| ≤
        relative n * frozen n ξ i j ∧
      |finslerTileProbe μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) f i j - modelProbe n ξ i j| ≤
        probeError ∧ |modelProbe n ξ i j| ≤ G)
    (hintBlock : ∀ n c, Integrable (fun ξ ↦ finslerNormalizedTileBlock F μ ν K
      hK.measurableSet hμ hν (s n) (z n) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (sample n))
    (hintFrozen : ∀ n c, Integrable (fun ξ ↦ OTSelector.frozenModelTileBlock
      (fun i ↦ s n i ξ) (fun j ↦ z n j ξ) (frozen n ξ) (modelProbe n ξ) t c /
        ((n + 1 : ℕ) : ℝ)) (sample n))
    (htransport : ∀ n, (∑ c, ∫ ξ, OTSelector.frozenModelTileBlock
      (fun i ↦ s n i ξ) (fun j ↦ z n j ξ) (frozen n ξ) (modelProbe n ξ) t c /
        ((n + 1 : ℕ) : ℝ) ∂sample n) ≤
      (∑ c, modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ)) + lawError n)
    (hintCount : ∀ n c, Integrable (fun ξ ↦
      |tileSourceCount (s n) c ξ - tileTargetCount (z n) c ξ|) (sample n))
    (hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (s n) c ξ - tileTargetCount (z n) c ξ| ∂sample n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ))) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂sample n) ≤
        (∑ c, (w c : ℝ) * p c t) + (2 * ε * Bnd + |t| * probeError) +
          (1 + 2 * ε) * lawBias + δ := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hXK : ∀ n, ∀ᵐ ξ ∂sample n, ∀ i, X n i ξ ∈ K := by
    intro n
    exact ae_all_iff.mpr fun i ↦
      ae_of_ae_map (hX n i).aemeasurable (by rw [hXlaw n i]; exact hμ)
  have hYK : ∀ n, ∀ᵐ ξ ∂sample n, ∀ j, Y n j ξ ∈ K := by
    intro n
    exact ae_all_iff.mpr fun j ↦
      ae_of_ae_map (hY n j).aemeasurable (by rw [hYlaw n j]; exact hν)
  let edgeBound : ℕ → ℝ := fun n ↦
    (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) * (2 * finslerDiam F K) + |t| * (‖f‖₊ : ℝ)
  let repair : ℕ → ℝ := fun n ↦ edgeBound n / ((n + 1 : ℕ) : ℝ) * (1 / 2) *
    Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ))
  have hbound0 (n : ℕ) : 0 ≤ edgeBound n / ((n + 1 : ℕ) : ℝ) := by
    have hd : 0 ≤ finslerDiam F K := Metric.diam_nonneg
    dsimp [edgeBound]
    positivity
  have hrepairlim : Tendsto repair atTop (𝓝 0) := by
    have hbase := tendsto_binomial_repairError_zero (q := q) hq
      (2 * finslerDiam F K) (‖f‖₊ : ℝ) t (Fintype.card ι)
    have hshift := (Filter.tendsto_add_atTop_iff_nat 1).mpr hbase
    convert hshift using 1
    funext n
    dsimp [repair, edgeBound]
    ring
  apply OTSelector.Limit.eventually_le_add_fixed_bias
    (OTSelector.Limit.tendsto_normalized_modelBlockSum q hq hwpos hCb0 hG0
      hkin hkin_bound hg hgb α β p hp t)
    hrelative hlawError hrepairlim hε hBnd
  intro n
  have hintTotal : Integrable (fun ξ ↦ Pressure.supportedDistancePressure μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t) (sample n) :=
    Pressure.integrable_supportedDistancePressure (P := sample n) (n := n + 1)
      μ ν K hK.measurableSet hμ hν (X n) (Y n) (hX n) (hY n)
      φ hφ hφ.continuous _ f t (Nat.succ_pos n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) hK (hXK n) (hYK n)
  have hrepair := finslerSupportedPressure_tile_repair_ae (F := F) (n := n)
    μ ν K hK.measurableSet hμ hν (s n) (z n) (X n) (Y n) φ hφ
    (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) f t hK (sample n) (hXK n) (hYK n)
  have htotal := integral_total_le_sum_model_add_repair (P := sample n) (n := n + 1)
    w hwsum
    (fun ξ ↦ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
      (fun i ↦ X n i ξ) (fun j ↦ Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t)
    (fun c ξ ↦ finslerNormalizedTileBlock F μ ν K hK.measurableSet hμ hν
      (s n) (z n) (X n) (Y n) φ (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ)
    (fun c ξ ↦ tileSourceCount (s n) c ξ) (fun c ξ ↦ tileTargetCount (z n) c ξ)
    (hbound0 n) hrepair hintTotal (hintBlock n) (hintCount n) (hcount n)
    (fun c ↦ ∫ ξ, finslerNormalizedTileBlock F μ ν K hK.measurableSet hμ hν
      (s n) (z n) (X n) (Y n) φ (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂sample n)
    (fun _ ↦ le_rfl)
  have hphysical := Reconstruction.integral_sum_finslerNormalizedTileBlock_le_frozen_sum
    (sample n) μ ν K hK.measurableSet hμ hν (s n) (z n) (X n) (Y n) φ
    (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t (frozen n) (modelProbe n)
    (hrelative0 n) herror hG0 (hedge n) (hintBlock n) (hintFrozen n)
  have htransport' := mul_le_mul_of_nonneg_left (htransport n)
    (show 0 ≤ 1 + relative n by linarith [hrelative0 n])
  dsimp only [repair, edgeBound]
  dsimp only [edgeBound] at htotal
  linarith

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
