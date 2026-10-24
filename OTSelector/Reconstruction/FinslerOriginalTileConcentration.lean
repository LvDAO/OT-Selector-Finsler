import OTSelector.Reconstruction.FinslerOriginalFrozenCoreLLN
import OTSelector.Limit.FinslerProbabilityLowerBound

/-!
# Per-tile concentration: Markov/Chebyshev and the Efron--Stein reduction

This module attacks the two analytic inputs of
`FinslerOriginalTileSingleConvergence.lean` for the plan-weighted frozen tile mean.

**Random variable.**  The empirical frozen mean of one retained tile is the random
variable `tileValue`: for the outcome `s` of the `n+1`-point iid sample it is

  `tileValue s = fractionalAssignmentCost (maskedFrozenCost edgeEvent frozenCoreMatrix) (A s) / (n+1)`.

Its expectation is the deterministic sequence `∫ s, tileValue s ∂sample n`, i.e. the
`tileEmpiricalMean` of the counting-law module.

**Proved here.**

* `tileDeviation_le_secondMoment`: the **Markov/Chebyshev step** -- for any random
  variable `X` and any `δ > 0`, the deviation probability from the mean is at most
  the second moment around the mean divided by `δ²` (proved from Markov's
  inequality `mul_meas_ge_le_integral_of_nonneg` applied to `(X - m)²`);
* `tileDeviation_tendsto_zero_of_mean_and_secondMoment`: **the exact reduction**:
  the per-tile deviation probability from the population Campbell value tends to
  zero as soon as (i) the means converge to the population value and (ii) the
  second moment around the mean vanishes (the Efron--Stein input).

**Named remaining sub-gaps.**

* `TileMeanConvergence`: the per-tile iid LLN of the plan-weighted sum
  (expectation of the tile frozen mean converges to the Palm frozen readout);
* `TileSecondMomentVanishing`: the per-tile Efron--Stein concentration in second
  moment form.

`singleTileCountingLaw_of_mean_and_secondMoment` combines them into the per-tile
counting law in probability.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
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

namespace PopulationLocalPressureCore.TaylorTiles

/-- **The per-tile frozen mean as a random variable.**  For the outcome `s` of the
`n+1`-point iid sample, this is the plan-weighted frozen cost of the retained tile
`c` divided by the number of sample points. -/
noncomputable def tileValue
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) : ℝ :=
  T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s) (hprobe f t n) (A n)
    (scale n) t c s / ((n + 1 : ℕ) : ℝ)

/-- **Markov/Chebyshev step.**  The probability that a random variable deviates
from its mean by at least `δ` is at most its second moment about the mean divided
by `δ²`. -/
theorem tileDeviation_le_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (m : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun s ↦ (X s - m) ^ 2) μ) :
    μ.real {s | δ ≤ |X s - m|} ≤ (∫ s, (X s - m) ^ 2 ∂μ) / δ ^ 2 := by
  have hset : {s | δ ≤ |X s - m|} = {s | δ ^ 2 ≤ (X s - m) ^ 2} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    rw [← sq_abs (X s - m), sq_le_sq, abs_of_pos hδ, abs_abs]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun s ↦ (X s - m) ^ 2)
    (Eventually.of_forall fun s ↦ sq_nonneg (X s - m)) hint (δ ^ 2)
  rw [hset]
  have hpos : 0 < δ ^ 2 := pow_pos hδ 2
  rw [le_div_iff₀ hpos, mul_comm]
  exact hmarkov

/-- **The per-tile concentration reduction.**

For one fixed retained tile and accuracy `δ > 0`: if the expected tile frozen mean
is eventually within `δ/2` of the population Campbell value and the second moment
of the tile frozen mean about its own expectation vanishes, then the deviation
probability from the population value tends to zero.  The remaining analytic
inputs are exactly `TileMeanConvergence` and `TileSecondMomentVanishing`. -/
theorem tileDeviation_tendsto_zero_of_mean_and_secondMoment
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X : ∀ n, Ω n → ℝ) (m : ℕ → ℝ) {L δ : ℝ} (hδ : 0 < δ)
    (hmean : ∀ᶠ n in atTop, |m n - L| ≤ δ / 2)
    (hint : ∀ n, Integrable (fun s ↦ (X n s - m n) ^ 2) (sample n))
    (hsecond : Tendsto (fun n ↦ ∫ s, (X n s - m n) ^ 2 ∂sample n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (sample n).real {s | δ ≤ |X n s - L|}) atTop (𝓝 0) := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hupper : Tendsto
      (fun n ↦ (∫ s, (X n s - m n) ^ 2 ∂sample n) / (δ / 2) ^ 2) atTop (𝓝 0) := by
    have := hsecond.div_const ((δ / 2) ^ 2)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ hupper
  filter_upwards [hmean] with n hn
  -- the deviation set is contained in the concentration set
  have hsub : {s | δ ≤ |X n s - L|} ⊆ {s | δ / 2 ≤ |X n s - m n|} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    have h1 : |X n s - L| ≤ |X n s - m n| + |m n - L| := abs_sub_le _ _ _
    linarith
  calc (sample n).real {s | δ ≤ |X n s - L|}
      ≤ (sample n).real {s | δ / 2 ≤ |X n s - m n|} :=
        measureReal_mono hsub (measure_ne_top (sample n) _)
    _ ≤ (∫ s, (X n s - m n) ^ 2 ∂sample n) / (δ / 2) ^ 2 :=
        tileDeviation_le_secondMoment (sample n) (X n) (m n) hδ2 (hint n)

/-- **The per-tile iid LLN (named remaining sub-gap).**  The expectation of the
plan-weighted frozen tile mean converges to the population Campbell value: the
per-tile iid counting law together with the relative Taylor expansion and the Palm
readout identification of the limiting stationary matching. -/
def TileMeanConvergence
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
    Tendsto (fun n ↦ ∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n)
      atTop (𝓝 (popVal f t c))

/-- **The per-tile Efron--Stein input (named remaining sub-gap).**  The second
moment of the plan-weighted frozen tile mean about its own expectation vanishes
along the sample: per-tile concentration at the paper scale. -/
def TileSecondMomentVanishing
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
    Tendsto (fun n ↦ ∫ s, (T.tileValue f t sample X Y scale hprobe A n c s -
      ∫ s', T.tileValue f t sample X Y scale hprobe A n c s' ∂sample n) ^ 2
      ∂sample n) atTop (𝓝 0)

/-- **The per-tile counting law in probability.**  For each fixed retained tile
the random frozen tile mean converges in probability to the population Campbell
value. -/
def SingleTileCountingLaw
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (d : ℝ), 0 < d →
    Tendsto (fun n ↦ (sample n).real
      {s | d ≤ |T.tileValue f t sample X Y scale hprobe A n c s - popVal f t c|})
      atTop (𝓝 0)

/-- **Mean convergence plus vanishing second moment imply the per-tile counting
law.**  This is the exact composition of the two remaining analytic sub-gaps: the
per-tile iid LLN `TileMeanConvergence` and the per-tile Efron--Stein concentration
`TileSecondMomentVanishing` give the single-tile counting law in probability. -/
theorem singleTileCountingLaw_of_mean_and_secondMoment
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      Integrable (fun s ↦ (T.tileValue f t sample X Y scale hprobe A n c s -
        ∫ s', T.tileValue f t sample X Y scale hprobe A n c s' ∂sample n) ^ 2)
        (sample n))
    (hmean : T.TileMeanConvergence popVal sample X Y scale hprobe A)
    (hsecond : T.TileSecondMomentVanishing sample X Y scale hprobe A) :
    T.SingleTileCountingLaw popVal sample X Y scale hprobe A := by
  intro f t c d hd
  have hm : Tendsto (fun n ↦ ∫ s, T.tileValue f t sample X Y scale hprobe A n c s
      ∂sample n) atTop (𝓝 (popVal f t c)) := hmean f t c
  have hdist : ∀ᶠ n in atTop,
      |(∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) -
        popVal f t c| ≤ d / 2 := by
    have hpos : 0 < d / 2 := by linarith
    have := hm.eventually (Metric.ball_mem_nhds _ hpos)
    filter_upwards [this] with n hn
    simpa [Real.dist_eq] using hn.le
  exact tileDeviation_tendsto_zero_of_mean_and_secondMoment (sample := sample)
    (fun n s ↦ T.tileValue f t sample X Y scale hprobe A n c s)
    (fun n ↦ ∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n)
    hd hdist (fun n ↦ hint f t c n) (hsecond f t c)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
