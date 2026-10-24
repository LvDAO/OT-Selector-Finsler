import OTSelector.Limit.FinslerExpectationUpperBound
import OTSelector.Limit.FinslerProbabilityLowerBound

/-!
# Assembly of the two pressure-bound lanes

`OTSelector/Limit/FinslerPressureSqueeze.lean` reduces the pointwise convergence
of the physical Dirichlet semidiscrete mean to two asymptotic inputs at a common
value `pressure f t`:

* `hprob`, the probability lower bound;
* `hupper`, the expectation upper bound.

`OTSelector/Limit/FinslerExpectationUpperBound.lean` supplies `hupper` from the
per-cell block model at the pressure value
`pressure f t = sum_c (w c : ℝ) * p c t`, where `p c t` is the local marked
pressure limit.  `OTSelector/Limit/FinslerProbabilityLowerBound.lean` supplies
`hprob` from several lower-lane hypotheses (pathwise good events, expectation
lower bounds, model comparison, or the subsequential weak-support statement).

This file joins the two lanes for a single probe `f` and tilt `t`:

* `FinslerTilePressureData` bundles the upper-lane block-model inputs of one
  probe (including the three integrability/count/comparison inputs
  `hintBlock`, `hintCount`, `hcount`, `hblock`, uniformly in the tilt);
* `finsler_hupper_of_tile_data` restates
  `finslerExpectationUpperBound_of_block_model` at the paper's exponent
  `2 / (d - 1)` and at the pressure value `sum_c w c * p c t`;
* `finslerSemidiscreteMean_tendsto_of_tile_bounds_of_hprob` turns the bundled
  upper data plus an arbitrary `hprob` at `sum_c w c * p c t` into pointwise
  convergence of the physical semidiscrete mean at that value;
* four corollaries instantiate `hprob` from the lower lane:
  `..._of_integral_lower` (expectation lower bound),
  `..._of_good_event` (pathwise good events),
  `..._of_comparison` (frozen model comparison), and
  `..._of_subseq_weak_support` (subsequential weak limits supported on
  `[L, ∞)`);
* `exists_finsler_pressure_producer_of_tile_bounds_of_hprob` and
  `exists_finsler_pressure_producer_of_tile_bounds` assemble the whole producer
  `∃ pressure radius derivative, ...` of
  `exists_finsler_pressure_producer_of_squeeze`, with
  `pressure f t = sum_c (w c : ℝ) * p f c t`.

The dimension is `d >= 6`, so that the paper's exponent
`2 / (d - 1)` is the upper-lane exponent `2 / q` for an integer `q > 4`; the
hypothesis `hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1` records this.
The derivative `derivative` and its differentiability `hderiv` at zero are
supplied by the caller: they are the subject of the differentiability lane, not
of either bounds lane.

No `sorry`, `admit` or added axiom occurs.  Nothing here proves the per-cell
block comparison `hblock` or the population value; those stay explicit.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BigOperators BoundedContinuousFunction
  unitInterval

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **Upper-lane block-model data for one probe.**

All fields are exactly the hypotheses of
`finslerExpectationUpperBound_of_block_model` for the fixed probe `f` and the
integer scale exponent `q`, except that the three tilt-dependent inputs
`hintBlock`, `hintCount`, `hblock` and the count bound `hcount` are quantified
over every tilt, so that the assembled convergence holds for all tilts at once.

The type parameters `ι` (tile labels), `A` and `B` (local marked model spaces)
are shared by all probes when the family version is used. -/
structure FinslerTilePressureData
    (ι A B : Type*) [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (φ : M → ℝ)
    (f : (K × K) →ᵇ ℝ) (q : ℕ) where
  /-- Tile weights. -/
  w : ι → I
  hwsum : ∑ c, (w c : ℝ) = 1
  hwpos : ∀ c, 0 < (w c : ℝ)
  /-- The local marked kinetic kernel and probe. -/
  kin : ι → A → B → (Fin q → ℝ) → ℝ
  g : ι → A → B → ℝ
  Cb : ℝ
  G : ℝ
  hCb0 : 0 ≤ Cb
  hG0 : 0 ≤ G
  hkin : ∀ c, Measurable (Function.uncurry (fun p : A × B => kin c p.1 p.2))
  hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2
  hg : ∀ c, Measurable (Function.uncurry (g c))
  hgb : ∀ c a b, |g c a b| ≤ G
  /-- The local marked input laws. -/
  α : ι → Measure A
  β : ι → Measure B
  instProbα : ∀ c, IsProbabilityMeasure (α c)
  instProbβ : ∀ c, IsProbabilityMeasure (β c)
  /-- The local marked pressure limits. -/
  p : ι → ℝ → ℝ
  hp : ∀ (c : ι) (t : ℝ), Tendsto
    (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
    atTop (𝓝 (p c t))
  /-- The tile label arrays. -/
  blockS : ∀ n, Fin (n + 1) → Ω n → ι
  blockT : ∀ n, Fin (n + 1) → Ω n → ι
  /-- Integrability of the physical normalized tile blocks, uniformly in the tilt. -/
  hintBlock : ∀ (t : ℝ) (n : ℕ) (c : ι), Integrable (fun ξ =>
    finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
      (blockS n) (blockT n) (X n) (Y n) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (P n)
  /-- Integrability of the label-count discrepancies. -/
  hintCount : ∀ (n : ℕ) (c : ι), Integrable (fun ξ =>
    |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ|) (P n)
  /-- The binomial count-discrepancy bound. -/
  hcount : ∀ (n : ℕ) (c : ι), ∫ ξ,
    |tileSourceCount (blockS n) c ξ - tileTargetCount (blockT n) c ξ| ∂P n ≤
    Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ))
  /-- The per-cell block comparison with the marked model block. -/
  hblock : ∀ (t : ℝ) (n : ℕ) (c : ι), ∫ ξ,
    finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK hμ hν
      (blockS n) (blockT n) (X n) (Y n) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ ∂P n ≤
    modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
      ((n + 1 : ℕ) : ℝ)

/-- **Upper lane: the `hupper` clause for one probe and one tilt.**

This is `finslerExpectationUpperBound_of_block_model` restated at the paper's
exponent `2 / (d - 1)` and at the pressure value `sum_c w c * p c t`. -/
theorem finsler_hupper_of_tile_data
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
    (hφ : let _instUpperDataPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (data : FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
        (∑ c, (data.w c : ℝ) * data.p c t) + ε := by
  intro ε hε
  letI : ∀ c, IsProbabilityMeasure (data.α c) := data.instProbα
  letI : ∀ c, IsProbabilityMeasure (data.β c) := data.instProbβ
  have h := finslerExpectationUpperBound_of_block_model hcomplete μ ν K hK hμ hν P X Y
    hX hY hXlaw hYlaw φ hφ f t q hq data.w data.hwsum data.hwpos
    (kin := data.kin) (g := data.g) (Cb := data.Cb) (G := data.G)
    data.hCb0 data.hG0 data.hkin data.hkin_bound data.hg data.hgb
    data.α data.β data.p data.hp data.blockS data.blockT
    (data.hintBlock t) data.hintCount data.hcount (data.hblock t) ε hε
  simpa only [hqdim] using h

/-- **Core assembly: bundled upper data plus an arbitrary `hprob` give the
pointwise semidiscrete-mean convergence at the weighted tile pressure.** -/
theorem finslerSemidiscreteMean_tendsto_of_tile_bounds_of_hprob
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i => X n i sample)
      (fun sample i => Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instAssemblyCorePotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (data : FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q)
    (hprob : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (P n).real {ξ |
      finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
      (∑ c, (data.w c : ℝ) * data.p c t) - ε}) atTop (𝓝 0)) :
    Tendsto (fun n => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
      (𝓝 (∑ c, (data.w c : ℝ) * data.p c t)) := by
  have hupper := finsler_hupper_of_tile_data hcomplete μ ν K hK hμ hν P X Y hX hY
    hXlaw hYlaw φ hφ f t hq hqdim data
  exact tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
    hF hcomplete m (by omega : 2 ≤ Module.finrank ℝ E) μ ν hμchart hνchart K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t
    (∑ c, (data.w c : ℝ) * data.p c t) hprob hupper

/-- **From an expectation lower bound.**  The lower lane supplies
`hprob` through `finslerSupportedPressure_probability_lower_of_integral_lower`
(using the unconditional centred concentration at `d >= 6`). -/
theorem finslerSemidiscreteMean_tendsto_of_tile_bounds_of_integral_lower
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i => X n i sample)
      (fun sample i => Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instAssemblyIntegralLowerPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (data : FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (∑ c, (data.w c : ℝ) * data.p c t) - ε ≤
        ∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) :
    Tendsto (fun n => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
      (𝓝 (∑ c, (data.w c : ℝ) * data.p c t)) := by
  letI : MetricSpace M := F.metricSpace
  have hφc : Continuous φ := hφ.continuous
  refine finslerSemidiscreteMean_tendsto_of_tile_bounds_of_hprob hF hcomplete m hdim
    μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t
    hq hqdim data ?_
  intro ε hε
  exact finslerSupportedPressure_probability_lower_of_integral_lower hdim μ ν K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφc f t
    (∑ c, (data.w c : ℝ) * data.p c t) hε (hlower (ε / 2) (by linarith))

/-- **From the paper's pathwise good-event bound.** -/
theorem finslerSemidiscreteMean_tendsto_of_tile_bounds_of_good_event
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i => X n i sample)
      (fun sample i => Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instAssemblyGoodEventPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (data : FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q)
    (G : ℝ → ∀ n, Set (Ω n))
    (hgood : ∀ ε : ℝ, 0 < ε → ∀ n, ∀ ξ ∈ G ε n,
      (∑ c, (data.w c : ℝ) * data.p c t) - ε ≤
        finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hbad : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P n).real ((G ε n)ᶜ)) atTop (𝓝 0)) :
    Tendsto (fun n => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
      (𝓝 (∑ c, (data.w c : ℝ) * data.p c t)) := by
  refine finslerSemidiscreteMean_tendsto_of_tile_bounds_of_hprob hF hcomplete m hdim
    μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t
    hq hqdim data ?_
  intro ε hε
  exact finslerSupportedPressure_probability_lower_of_good_event μ ν K hK hμ hν P X Y
    φ f t (∑ c, (data.w c : ℝ) * data.p c t) ε (G ε)
    (hgood ε hε) (hbad ε hε)

/-- **From a lower comparison with a frozen model sequence.** -/
theorem finslerSemidiscreteMean_tendsto_of_tile_bounds_of_comparison
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i => X n i sample)
      (fun sample i => Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instAssemblyComparisonPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (data : FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q)
    (W : ∀ n, Ω n → ℝ) (δ : ℕ → ℝ) (G : ∀ n, Set (Ω n))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hcomp : ∀ n, ∀ ξ ∈ G n, W n ξ - δ n ≤
      finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hbad : Tendsto (fun n => (P n).real ((G n)ᶜ)) atTop (𝓝 0))
    (hW : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (P n).real {ξ | W n ξ <
      (∑ c, (data.w c : ℝ) * data.p c t) - ε / 2}) atTop (𝓝 0)) :
    Tendsto (fun n => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
      (𝓝 (∑ c, (data.w c : ℝ) * data.p c t)) := by
  refine finslerSemidiscreteMean_tendsto_of_tile_bounds_of_hprob hF hcomplete m hdim
    μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t
    hq hqdim data ?_
  intro ε hε
  exact OTSelector.Probability.tendsto_measureReal_lt_sub_of_eventually_lower_model
    P (V := fun n ξ => finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
      (fun i => X n i ξ) (fun j => Y n j ξ) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (W := W) (G := G) (δ := δ) (L := ∑ c, (data.w c : ℝ) * data.p c t) hε hδ
    hcomp hbad (hW ε hε)

/-- **From the subsequence criterion of the paper's lower bound.**  The
hypothesis is that every subsequential weak limit of the scalar pressure laws
is supported on `[sum_c w c * p c t, ∞)`. -/
theorem finslerSemidiscreteMean_tendsto_of_tile_bounds_of_subseq_weak_support
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i => X n i sample)
      (fun sample i => Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instAssemblySupportPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (hφc : let _instAssemblySupportContinuousMetric : MetricSpace M := F.metricSpace
      Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (data : FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q)
    (hsub : ∀ φidx : ℕ → ℕ, StrictMono φidx →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
        Tendsto (fun k => pressureScalarLaw P
          (fun n s => finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
            (fun i => X n i s) (fun j => Y n j s) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
          (measurable_finslerSupportedPressure hcomplete μ ν K hK.measurableSet hμ hν
            X Y hX hY φ hφc f t) (φidx (ψ k))) atTop (𝓝 νlim) ∧
        (νlim : Measure ℝ) (Iio (∑ c, (data.w c : ℝ) * data.p c t)) = 0) :
    Tendsto (fun n => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
      (𝓝 (∑ c, (data.w c : ℝ) * data.p c t)) := by
  refine finslerSemidiscreteMean_tendsto_of_tile_bounds_of_hprob hF hcomplete m hdim
    μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t
    hq hqdim data ?_
  intro ε hε
  exact finslerSupportedPressure_probability_lower_of_subseq_weak_support hcomplete
    μ ν K hK hμ hν P X Y hX hY φ hφc f t (∑ c, (data.w c : ℝ) * data.p c t) hε hsub

/-- **Whole producer from a family of upper-lane data and a family `hprob`.**

The pressure is `pressure f t = sum_c (data f).w c * (data f).p c t`; `radius`
and `derivative` are supplied, with `0 < radius f` and differentiability of the
constructed pressure at zero. -/
theorem exists_finsler_pressure_producer_of_tile_bounds_of_hprob
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i => X n i sample)
      (fun sample i => Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instAssemblyProducerPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (radius : ((K × K) →ᵇ ℝ) → ℝ) (hradius : ∀ f, 0 < radius f)
    (derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (data : (f : (K × K) →ᵇ ℝ) →
      FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q)
    (hprob : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n => (P n).real {ξ | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i => X n i ξ) (fun j => Y n j ξ) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          (∑ c, ((data f).w c : ℝ) * (data f).p c t) - ε}) atTop (𝓝 0))
    (hderiv : ∀ f, HasDerivAt
      (fun t => ∑ c, ((data f).w c : ℝ) * (data f).p c t) (derivative f) 0) :
    let _instAssemblyProducerMetric : MetricSpace M := F.metricSpace
    ∃ (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
      (radius' derivative' : ((K × K) →ᵇ ℝ) → ℝ),
      (∀ f, 0 < radius' f) ∧
      (∀ f, HasDerivAt (pressure f) (derivative' f) 0) ∧
      (∀ f t, |t| < radius' f →
        Tendsto (fun n => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
          (𝓝 (pressure f t))) := by
  refine ⟨fun f t => ∑ c, ((data f).w c : ℝ) * (data f).p c t, radius, derivative,
    hradius, hderiv, ?_⟩
  intro f t ht
  exact finslerSemidiscreteMean_tendsto_of_tile_bounds_of_hprob hF hcomplete m hdim
    μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t
    hq hqdim (data f) (fun ε hε => hprob f t ε ht hε)

/-- **Whole producer from a family of upper-lane data and an expectation lower
bound family.**  This is the most direct assembly of the two compiled lanes:
the upper block model at `q = d - 1` and the lower expectation bound at the
same weighted pressure value. -/
theorem exists_finsler_pressure_producer_of_tile_bounds
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i => X n i sample)
      (fun sample i => Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instAssemblyProducerLowerPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace A] [MeasurableSpace B]
    {q : ℕ} (hq : 4 < q) (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1)
    (radius : ((K × K) →ᵇ ℝ) → ℝ) (hradius : ∀ f, 0 < radius f)
    (derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (data : (f : (K × K) →ᵇ ℝ) →
      FinslerTilePressureData ι A B F μ ν K hK.measurableSet hμ hν P X Y φ f q)
    (hlower : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∑ c, ((data f).w c : ℝ) * (data f).p c t) - ε ≤
          ∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
            (fun i => X n i ξ) (fun j => Y n j ξ) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n)
    (hderiv : ∀ f, HasDerivAt
      (fun t => ∑ c, ((data f).w c : ℝ) * (data f).p c t) (derivative f) 0) :
    let _instAssemblyProducerLowerMetric : MetricSpace M := F.metricSpace
    ∃ (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
      (radius' derivative' : ((K × K) →ᵇ ℝ) → ℝ),
      (∀ f, 0 < radius' f) ∧
      (∀ f, HasDerivAt (pressure f) (derivative' f) 0) ∧
      (∀ f t, |t| < radius' f →
        Tendsto (fun n => finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
          (𝓝 (pressure f t))) := by
  refine ⟨fun f t => ∑ c, ((data f).w c : ℝ) * (data f).p c t, radius, derivative,
    hradius, hderiv, ?_⟩
  intro f t ht
  exact finslerSemidiscreteMean_tendsto_of_tile_bounds_of_integral_lower hF hcomplete m
    hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t
    hq hqdim (data f) (fun ε hε => hlower f t ht ε hε)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
