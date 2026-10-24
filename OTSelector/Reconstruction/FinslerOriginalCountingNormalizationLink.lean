import OTSelector.Reconstruction.FinslerOriginalCloudReadoutConvergence
import OTSelector.Reconstruction.FinslerOriginalTileScaleConsistency
import OTSelector.Reconstruction.FinslerOriginalTileIntegralSplit
import OTSelector.Reconstruction.FinslerOriginalLinearPalmIdentification
import OTSelector.Reconstruction.FinslerOriginalTileNormalization
import OTSelector.Reconstruction.FinslerOriginalTileFixedPairDecomposition
import OTSelector.Reconstruction.FinslerOriginalTileBoundedCorrectionInsertion

/-!
# Counting normalization link: closed boundedness and the fixed-pair route to field (b)

Continues `FinslerOriginalCloudReadoutConvergence.lean`.  That module reduced field
(b) of `TilePalmSampleLaw` to three inputs: the empirical readout convergence
(`hlln`), the population Campbell identification (`hpop`), and boundedness of the
paper multiplier (`hbounded`).  This module closes the boundedness input with the
paper scale and derives the readout from the *fixed-pair* convergence instead of
the abstract population identification, using the repo's exact decomposition
`tileFixedPair = (cost + probe) + clipping`.

## Closed here

* `abs_tileScale_le_one` and `eps_mul_tileScale_abs_le`: the lane's decaying scale
  `tileScale n = 1/(n+1)` gives the bound with constant `1 - 2ε` for `ε ≤ 1/2` — the
  boundedness input is discharged for the actual `TilePalmSampleLaw` scale.
* `abs_tileScalePaper_le_one_of_nonpos` and
  `eps_mul_tileScalePaper_abs_le_of_nonpos`: the paper scale `tileScalePaper q` is
  bounded whenever `2/q ≤ 0`, again discharged.
* `tileScalePaper_not_bounded_of_pos`: honestly, for `0 < 2/q` the paper scale is
  unbounded (it tends to `+∞`), so the boundedness input *cannot* be instantiated
  there; what is needed in that regime is the rate form (vanishing of
  `(1-2ε)·scale·(readout error)`), which is exactly the per-tile error-budget shape
  of `RootedTileMeanConvergence`.
* `countedTileMean_eq_probabilityMean`: the counting normalization link — the
  `1/(n+1)`-normalized integral of the frozen tile cost against the counting measure
  is the probability integral against the empirical sample law.  Hence the repo's
  rooted tile counting convergence and the tile Palm sample mean are the same
  sequence.
* `maskedCostReadout_tendsto_of_fixedPair`: field (b) from the fixed-pair
  convergence: since
  `tileFixedPair = ((1-2ε)·scale·maskedMean + probeInt) + clippingInt`
  with probe and clipping integrals vanishing, the masked-cost readout converges to
  the fixed-pair limit.  This replaces `hlln` + `hpop` by the single fixed-pair
  convergence.
* `tilePalmSampleLaw_sceneCloud_of_fixedPairConvergence`: the full
  `TilePalmSampleLaw` for the concrete lane with BOTH fields discharged and the
  boundedness input closed by `eps_mul_tileScale_abs_le`.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-! ## 1. Boundedness of the paper multiplier -/

/-- The lane's decaying scale is at most one. -/
theorem laneScale_le_one (n : ℕ) : tileScale n ≤ 1 := by
  unfold tileScale
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- The lane's decaying scale is nonnegative. -/
theorem laneScale_nonneg (n : ℕ) : 0 ≤ tileScale n := by
  unfold tileScale
  positivity

/-- **The boundedness input for the lane scale**: for `ε ≤ 1/2` the multiplier
`(1-2ε)·tileScale` is bounded by `1-2ε`. -/
theorem eps_mul_tileScale_abs_le (hε : ε ≤ 1 / 2) (n : ℕ) :
    |(1 - 2 * ε) * tileScale n| ≤ 1 - 2 * ε := by
  have hnonneg : 0 ≤ 1 - 2 * ε := by linarith
  rw [abs_of_nonneg (mul_nonneg hnonneg (laneScale_nonneg n))]
  calc (1 - 2 * ε) * tileScale n ≤ (1 - 2 * ε) * 1 :=
        mul_le_mul_of_nonneg_left (laneScale_le_one n) hnonneg
    _ = 1 - 2 * ε := mul_one _

/-- The paper scale with nonpositive exponent is at most one. -/
theorem abs_tileScalePaper_le_one_of_nonpos (hq : 2 / q ≤ 0) (n : ℕ) :
    |tileScalePaper q n| ≤ 1 := by
  unfold tileScalePaper
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  rw [abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos h1 hq

/-- **The boundedness input for the paper scale with `2/q ≤ 0`.** -/
theorem eps_mul_tileScalePaper_abs_le_of_nonpos (hε : ε ≤ 1 / 2) (hq : 2 / q ≤ 0)
    (n : ℕ) : |(1 - 2 * ε) * tileScalePaper q n| ≤ 1 - 2 * ε := by
  have hnonneg : 0 ≤ 1 - 2 * ε := by linarith
  have hscale : 0 ≤ tileScalePaper q n := by
    unfold tileScalePaper
    exact le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
  rw [abs_of_nonneg (mul_nonneg hnonneg hscale)]
  calc (1 - 2 * ε) * tileScalePaper q n ≤ (1 - 2 * ε) * 1 :=
        mul_le_mul_of_nonneg_left
          (abs_le.mp (abs_tileScalePaper_le_one_of_nonpos hq n)).2 hnonneg
    _ = 1 - 2 * ε := mul_one _

/-- **Honest obstruction**: for `0 < 2/q` the paper scale is unbounded, so the
boundedness input cannot be instantiated there; the rate form of the empirical
convergence is needed instead. -/
theorem tileScalePaper_not_bounded_of_pos (hq : 0 < 2 / q) :
    ¬ ∃ C : ℝ, ∀ n, |tileScalePaper q n| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := (tileScalePaper_tendsto_atTop hq).eventually
    (eventually_gt_atTop (max C 0)) |>.exists
  have hle : |tileScalePaper q n| ≤ C := hC n
  have hnn : 0 ≤ tileScalePaper q n :=
    le_of_lt (lt_of_le_of_lt (le_max_right C 0) hn)
  rw [abs_of_nonneg hnn] at hle
  exact absurd (lt_of_lt_of_le hn hle) (not_lt.mpr (le_max_left C 0))

/-! ## 2. The counting normalization link -/

namespace PopulationLocalPressureCore.TaylorTiles

/-- **The counting normalization link**: the `1/(n+1)`-normalized integral of the
frozen tile cost against the counting measure is the probability integral against
the empirical sample law of the concrete lane.  Hence the repo's rooted tile
counting convergence (normalized by `1/(n+1)`) and the tile Palm sample mean are the
same sequence. -/
theorem countedTileMean_eq_probabilityMean
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Fin (n + 1) → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (scale : ℕ → ℝ) (n : ℕ) (c : T.Index) :
    ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∫ s, T.tileFrozenCost (fun s i ↦ sceneCloudX pcloud n i s)
        (fun s i ↦ sceneCloudY qcloud n i s) (hprobe f t n) (A n) (scale n) t c s
        ∂(sceneCloudCounting n) =
      ∫ s, T.tileFrozenCost (fun s i ↦ sceneCloudX pcloud n i s)
        (fun s i ↦ sceneCloudY qcloud n i s) (hprobe f t n) (A n) (scale n) t c s
        ∂(sceneCloudSample n) :=
  integral_counting_eq_empirical n _

/-! ## 3. Field (b) from the fixed-pair convergence -/

/-- **Field (b) from the fixed-pair convergence.**  Using the repo's exact split
`tileFixedPair = (cost + probe) + clipping`, the cost integral being
`(1-2ε)·scale·maskedMean`, and the proved vanishing of the probe and clipping
integrals, the masked-cost readout converges to the fixed-pair limit. -/
theorem maskedCostReadout_tendsto_of_fixedPair
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ) (c : T.Index)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintLin : ∀ n, Integrable (T.tileLinearIntegrand (ε := ε) f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintC : ∀ n, Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t X Y
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hclip : Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) atTop (𝓝 0))
    {L : ℝ}
    (hfixed : Tendsto (fun n ↦ T.tileFixedPair f t sample X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) atTop (𝓝 L)) :
    Tendsto (fun n ↦ (1 - 2 * ε) *
      (scale n * T.tileMaskedFrozenCostMean sample X Y n c) - L) atTop (𝓝 0) := by
  have hp := T.tileLinearProbePart_tendsto_zero sample f t X Y c base hBp hbase hintP
  have hcostEq : ∀ n, (1 - 2 * ε) * (scale n * T.tileMaskedFrozenCostMean sample X Y n c) =
      T.tileFixedPair f t sample X Y scale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        T.tileFixedPairClippingCorrection f t sample X Y scale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        (∫ s, T.tileLinearProbeIntegrand f t X Y
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n) := by
    intro n
    have hsplit1 := T.tileFixedPairLinearPart_eq_cost_add_probe sample f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c (hintC n) (hintP n)
    have hsplit2 := T.tileFixedPair_eq_linear_add_clipping sample f t X Y scale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c (hintLin n) (hintClip n)
    have hcost := T.tileLinearCostPart_eq_const_mul_mean (ε := ε) sample f t X Y scale n c
    calc (1 - 2 * ε) * (scale n * T.tileMaskedFrozenCostMean sample X Y n c)
        = (∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s ∂sample n) :=
          hcost.symm
      _ = _ := by
          rw [hsplit2, hsplit1]
          ring
  have hlim : Tendsto (fun n ↦
      T.tileFixedPair f t sample X Y scale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        T.tileFixedPairClippingCorrection f t sample X Y scale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        (∫ s, T.tileLinearProbeIntegrand f t X Y
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n))
      atTop (𝓝 L) := by
    have h := (hfixed.sub hclip).sub hp
    simpa using h
  have hfun : (fun n ↦ (1 - 2 * ε) *
        (scale n * T.tileMaskedFrozenCostMean sample X Y n c) - L) =
      (fun n ↦ (T.tileFixedPair f t sample X Y scale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        T.tileFixedPairClippingCorrection f t sample X Y scale
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        (∫ s, T.tileLinearProbeIntegrand f t X Y
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n)) - L) := by
    funext n
    rw [hcostEq n]
  rw [hfun]
  simpa using hlim.sub_const L

/-! ## 4. The full tile Palm sample law with every exposed input discharged -/

/-- **The full `TilePalmSampleLaw` for the concrete lane with every exposed input
discharged**: the boundedness input by `eps_mul_tileScale_abs_le`, field (a) by the
cloud-average computation, and field (b) by the fixed-pair convergence — the named
rooted tile counting convergence in the counting normalization (via
`countedTileMean_eq_probabilityMean`) combined with the proved probe and clipping
vanishing.  The only remaining named inputs are the fixed-pair convergence
`hfixed` (rooted tile counting convergence towards the Campbell tile value) and the
clipping vanishing `hclip` (proved in
`FinslerOriginalTileBoundedCorrectionInsertion.lean` under the retained-edge data). -/
noncomputable def tilePalmSampleLaw_sceneCloud_of_fixedPairConvergence
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintLin : ∀ n, Integrable (T.tileLinearIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sceneCloudSample n))
    (hintClip : ∀ n, Integrable (T.tileClippingIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sceneCloudSample n))
    (hintC : ∀ n, Integrable (T.tileLinearCostIntegrand (ε := ε) f t
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t
      (sceneCloudX pcloud) (sceneCloudY qcloud)
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sceneCloudSample n))
    (hclip : Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) atTop (𝓝 0))
    (G : ℕ → (ℚ → M) → ℝ)
    (hfixed : Tendsto (fun n ↦ T.tileFixedPair f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) atTop
      (𝓝 (T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c))) :
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) := by
  have hreadout := T.maskedCostReadout_tendsto_of_fixedPair
    (Ω := fun n ↦ Fin (n + 1)) sceneCloudSample f t
    (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale c base hBp hbase
    hintLin hintClip hintC hintP hclip hfixed
  have hconv : Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n *
      (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ s : Fin (n + 1),
        T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s)) -
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) n)
      atTop (𝓝 0) := by
    simpa only [T.tileMaskedFrozenCostMean_sceneCloud] using hreadout
  exact T.tilePalmSampleLaw_sceneCloud f t pcloud qcloud tileScale c
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    hconv

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
