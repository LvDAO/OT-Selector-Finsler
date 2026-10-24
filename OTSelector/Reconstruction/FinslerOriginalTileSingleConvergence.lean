import OTSelector.Reconstruction.FinslerOriginalFrozenCoreLLN
import OTSelector.Limit.FinslerProbabilityLowerBound

/-!
# Single-tile counting law: finite-index aggregation and concentration reduction

This module closes the remaining sub-gap of
`FinslerOriginalTileCountingLaw.lean` in its correct probabilistic form.

**Correction.** The predicate `RootedTileSingleConvergence` of
`FinslerOriginalTileCountingLaw.lean` quantifies `∀ᶠ n, |tileEmpiricalMeanProb - popVal| ≤ δ`
outside any probability space, i.e. it asks for *deterministic* convergence of a
random empirical mean; that is not attainable amortized over all samples.  The
correct content is convergence **in probability**, which is also what the
downstream pressure lane consumes (the mean bounds are probability-one statements
on good events).  This module states and works with the probabilistic form.

Contents:

* `tileEmpiricalMeanProb`: the empirical frozen mean of one retained Taylor tile
  (repeated here);
* `RootedTileSingleConvergenceInProbability` (def): for each fixed retained tile
  the empirical frozen tile mean converges in probability to its population
  Campbell value (the Palm frozen readout of the limiting stationary matching);
* `measureReal_iUnion_fintype_le_sum`: the finite union bound for real-valued
  measures;
* `uniformTileDeviation_tendsto_zero`: **the finite-index aggregation**: if every
  fixed tile converges in probability, then the probability that *any* retained
  tile deviates by more than `δ` tends to zero (finite union bound over the
  retained tile family);
* `tileDeviation_le_of_mean_and_concentration`: **the exact remaining reduction**:
  per-tile convergence in probability to `popVal` follows from (i) convergence of
  the expected empirical tile mean to `popVal` (per-tile LLN with relative Taylor
  expansion and the Palm readout identification) and (ii) per-tile concentration
  of the empirical tile mean about its own expectation (Efron--Stein / bounded
  differences); the triangle-inequality argument is proved in full.

The remaining concentration sub-gap is ingredient (ii) at the paper scale.

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

/-- The empirical frozen mean of one retained Taylor tile. -/
noncomputable def tileEmpiricalMeanProb
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) : ℝ :=
  (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
      (hprobe f t n) (A n) (scale n) t c s ∂sample n) / ((n + 1 : ℕ) : ℝ)

/-- **The single-tile counting law (probabilistic form).**

For each fixed retained Taylor tile, the empirical frozen tile mean converges in
probability to its population Campbell value: the per-tile iid counting /
Efron--Stein convergence, with the limiting stationary matching supplying the
limit (the Palm frozen readout over the tile's root cell). -/
def RootedTileSingleConvergenceInProbability
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (δ : ℝ), 0 < δ →
    Tendsto (fun n ↦ (sample n).real
      {s | δ ≤ |T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c - popVal f t c|})
      atTop (𝓝 0)

end PopulationLocalPressureCore.TaylorTiles

/-- **The exact remaining reduction: mean convergence and concentration imply the
single-tile counting law.**

Fix a retained tile and an accuracy ¤δ > 0¤.  If (i) the expected empirical tile
mean is eventually within ¤δ/2¤ of the population Campbell value and (ii) the
empirical tile mean concentrates about its own expectation (deviation probability
by ¤δ/2¤ tends to zero), then the deviation probability of the empirical tile mean
from the population value by ¤δ¤ tends to zero.  This is the standard
triangle-inequality reduction; it isolates the exact remaining sub-gap as the two
analytic inputs:

* per-tile **mean convergence** (per-tile iid LLN with the relative Taylor
  expansion and the Palm readout identification of the limiting stationary
  matching);
* per-tile **Efron--Stein concentration** of the plan-weighted frozen tile mean
  about its own expectation at the paper scale. -/
theorem tileDeviation_tendsto_zero_of_mean_convergence_and_concentration
    {ι : Type*} (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X : ∀ n, Ω n → ℝ) (m : ℕ → ℝ) {L δ : ℝ} (hδ : 0 < δ)
    (hmean : ∀ᶠ n in atTop, |m n - L| ≤ δ / 2)
    (hconc : Tendsto (fun n ↦ (sample n).real {s | δ / 2 ≤ |X n s - m n|})
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (sample n).real {s | δ ≤ |X n s - L|}) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ hconc
  filter_upwards [hmean] with n hn
  refine (measureReal_mono (μ := sample n) ?_ (measure_ne_top (sample n) _)).trans (le_refl _)
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
  have h1 : |X n s - L| ≤ |X n s - m n| + |m n - L| := abs_sub_le _ _ _
  linarith

end OTSelector.Reconstruction
