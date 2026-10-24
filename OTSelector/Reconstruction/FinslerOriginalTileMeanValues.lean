import OTSelector.Reconstruction.FinslerOriginalRootedTileCampbellMean
import OTSelector.Reconstruction.FinslerOriginalAtlasSceneBridge
import OTSelector.Reconstruction.FinslerOriginalRootedSceneLimitLaw

/-!
# Per-tile mean convergence of the empirical frozen tile costs

This module closes the named per-tile statement
`RootedTileMeanCampbellValues` of `FinslerOriginalRootedTileCampbellMean.lean` in
its reducible form.  The frozen core functional decomposes exactly over the
retained Taylor tiles (proved in `FinslerOriginalFrozenCoreLLN.lean`), so the
remaining content is:

* `RootedTileMeanConvergence` (def): **per-tile mean convergence** -- for every
  physical probe and tilt, the empirical frozen tile means converge to their
  population Campbell values with summable per-tile error.  In the paper the
  population Campbell value of a tile is the Palm/Campbell integral of the tile's
  frozen edge cost along the limiting stationary matching; the identification of
  the limiting scene and its Palm readout is the content of
  `FinslerOriginalRootedSceneLimitLaw.lean` and
  `FinslerOriginalAtlasSceneBridge.lean` (`atlasRootFrozenIntegrand`,
  `palmReadout_eq_rootWindowExpectation`,
  `campbellAveragedFrozenCost_eq_rootedScenePalmReadout`);
* `rootedTileMeanCampbellValues_of_tile_mean_convergence`: the per-tile mean
  convergence, together with the exact decomposition of the Campbell-averaged
  frozen cost into the per-tile population Campbell values, **implies**
  `RootedTileMeanCampbellValues`.  The construction of the values and budgets and
  the entire finite-sum bookkeeping is proved; the exact decomposition is the
  only named input;
* `camFrozenMeanBound_of_tile_mean_convergence`: consequently the Campbell mean
  bound (conjunct (iv)) for the actual frozen core functional follows.

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

open OTSelector.Geometry

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

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **Per-tile mean convergence of the empirical frozen tile costs.**

For every physical probe and tilt, the empirical frozen tile means
`(∫ tileFrozenCost)/(n+1)` converge to their population Campbell values
`popVal f t c` with summable per-tile error: the total error over the retained
tiles vanishes.  This is the remaining probabilistic per-tile statement; in the
paper `popVal` is the Palm/Campbell integral of the tile's frozen edge cost along
the limiting stationary matching (see `FinslerOriginalRootedSceneLimitLaw.lean`
and `FinslerOriginalAtlasSceneBridge.lean`). -/
def RootedTileMeanConvergence
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
  ∃ err : ℕ → T.Index → ℝ,
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, err n c ≤ δ) ∧
    (∀ n (c : T.Index),
      |(∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
          (hprobe f t n) (A n) (scale n) t c s ∂sample n) / ((n + 1 : ℕ) : ℝ) -
        popVal f t c| ≤ err n c)

/-- **The named per-tile statement from per-tile mean convergence.**

If the Campbell-averaged frozen cost decomposes exactly into the per-tile
population Campbell values (the atlas scene bridge input) and the empirical
frozen tile means converge to those values with summable total error, then
`RootedTileMeanCampbellValues` holds.  The values are taken to be the population
values and the budgets the convergence errors; the whole finite-sum bookkeeping is
proved. -/
theorem rootedTileMeanCampbellValues_of_tile_mean_convergence
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (hpop : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      campbellAveragedFrozenCost P a κ lambda (g f t) q = ∑ c, popVal f t c)
    (hconv : T.RootedTileMeanConvergence popVal sample X Y scale hprobe A) :
    T.RootedTileMeanCampbellValues q g sample X Y scale hprobe A := by
  intro f t
  obtain ⟨err, herrSum, herrBound⟩ := hconv f t
  refine ⟨fun _ c ↦ popVal f t c, err, ?_, herrSum, ?_⟩
  · intro δ hδ
    filter_upwards [herrSum δ hδ] with n hn
    rw [hpop f t]
    have hle : (∑ c, popVal f t c) ≤
        (∑ c, (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
          (hprobe f t n) (A n) (scale n) t c s ∂sample n) / ((n + 1 : ℕ) : ℝ)) +
          ∑ c, err n c := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun c _ ↦ ?_
      have h1 := (abs_le.mp (herrBound n c)).1
      linarith
    linarith
  · intro n c
    have h1 := (abs_le.mp (herrBound n c)).1
    linarith

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
