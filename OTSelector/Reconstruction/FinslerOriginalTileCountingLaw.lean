import OTSelector.Reconstruction.FinslerOriginalTileRefinementCounting
import OTSelector.Reconstruction.FinslerOriginalRootedSceneLimitLaw

/-!
# Per-tile counting law: single-tile convergence implies RootedTileMeanConvergence

This module closes the remaining sub-gap of the tile lane at the level of the
finite-index reduction.  The per-tile empirical frozen mean of a retained Taylor
tile is

  `tileEmpiricalMean f t n c = (∫ tileFrozenCost along the n+1 sample) / (n+1)`.

The module defines:

* `RootedTileSingleConvergence` (def): the **single-tile counting law** -- for each
  *fixed* retained tile `c` the empirical frozen tile mean converges to its
  population Campbell value `popVal f t c` (the Palm frozen readout of the
  limiting stationary matching over the tile's root cell; cf.
  `FinslerOriginalRootedSceneLimitLaw` and the cell refinement of
  `FinslerOriginalTileRefinementCounting.lean`);
* `tileEmpiricalMean` (def): the per-tile empirical frozen mean;
* `rootedTileMeanConvergence_of_single`: **single-tile convergence implies
  `RootedTileMeanConvergence`**.  Because the retained tile family
  `T.Index` is finite, pointwise-in-tile convergence is eventually uniform in the
  tile (`Filter.eventually_all`), and the uniform error `δ` contributes at most
  `|T.Index| · δ` to the total tile error; taking the errors to be the observed
  deviations gives summable (vanishing) total error.  This is the exact
  finite-index/eventually-all bookkeeping closing the counting lane.

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
noncomputable def tileEmpiricalMean
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

/-- **The single-tile counting law.**

For each *fixed* retained Taylor tile, the empirical frozen tile mean converges
to its population Campbell value: the per-tile iid counting / Efron-Stein
convergence with the limiting stationary matching supplying the limit (the Palm
frozen readout over the tile's root cell). -/
def RootedTileSingleConvergence
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (δ : ℝ), 0 < δ →
    ∀ᶠ n in atTop, |T.tileEmpiricalMean f t sample X Y scale hprobe A n c - popVal f t c| ≤ δ

/-- **Single-tile convergence implies the per-tile mean convergence.**

Since the retained tile family is finite, single-tile convergence is eventually
uniform in the tile; the uniform per-tile error sums over the tiles to a
vanishing total error, so `RootedTileMeanConvergence` holds. -/
theorem rootedTileMeanConvergence_of_single
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsingle : T.RootedTileSingleConvergence popVal sample X Y scale hprobe A) :
    T.RootedTileMeanConvergence popVal sample X Y scale hprobe A := by
  intro f t
  have huniform : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ c : T.Index,
        |T.tileEmpiricalMean f t sample X Y scale hprobe A n c - popVal f t c| ≤ δ := by
    intro δ hδ
    exact Filter.eventually_all.2 fun c ↦ hsingle f t c δ hδ
  refine ⟨fun n c ↦
    |T.tileEmpiricalMean f t sample X Y scale hprobe A n c - popVal f t c|,
    ?_, fun n c ↦ le_rfl⟩
  intro δ hδ
  have hδ' : 0 < δ / ((Fintype.card T.Index : ℝ) + 1) := by positivity
  filter_upwards [huniform (δ / ((Fintype.card T.Index : ℝ) + 1)) hδ'] with n hn
  calc ∑ c : T.Index,
        |T.tileEmpiricalMean f t sample X Y scale hprobe A n c - popVal f t c|
      ≤ ∑ _c : T.Index, δ / ((Fintype.card T.Index : ℝ) + 1) :=
        Finset.sum_le_sum fun c _ ↦ hn c
    _ = (Fintype.card T.Index : ℝ) * (δ / ((Fintype.card T.Index : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ δ := by
        have hN : (0 : ℝ) ≤ (Fintype.card T.Index : ℝ) := by positivity
        have hlt : (Fintype.card T.Index : ℝ) / ((Fintype.card T.Index : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        calc (Fintype.card T.Index : ℝ) * (δ / ((Fintype.card T.Index : ℝ) + 1))
            = δ * ((Fintype.card T.Index : ℝ) / ((Fintype.card T.Index : ℝ) + 1)) := by ring
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hlt hδ.le
          _ = δ := by ring

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
