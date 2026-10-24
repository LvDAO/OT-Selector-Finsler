import OTSelector.Reconstruction.FinslerOriginalUniformPlanResidualDischarge
open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

open OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.Reconstruction.PopulationLocalPressureCore.TaylorTiles

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
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
  {ε : ℝ} {q : ℝ}
/-!
# Producers investigation: `hε : ε ≤ 1/2` and the window-region field `hp`

## hε

Repo search results: `ε ≤ 1/2` occurs only as an ASSUMED hypothesis / structure field,
never as a conclusion:

* `FinslerOriginalAnalyticLaneBundleReduction:135`: structure field `hε : ε ≤ 1 / 2`;
* `FinslerOriginalAnalyticBundleFromLaneProducers` (lines 95, 128, 157, 186): explicit
  binder `(hε : ε ≤ 1 / 2)`;
* `FinslerOriginalUniformPlanResidualDischarge:125`: bundle field `hε : ε ≤ 1 / 2`;
* `TaylorTiles` imposes NO upper bound on `ε` (`nonempty_taylorTiles` only needs
  `0 < ε`, and V15 carries `(εt : ℝ) (T : Dl.TaylorTiles εt)` with no `εt` bound).

So `hε` is genuinely independent.  What IS available is the MONOTONICITY producer: a
smaller retained radius `ε₀ ≤ 1/2` (e.g. a previous tile scale) gives `ε ≤ 1/2`.
`epsilon_le_half_of_le` records it.

## hp

`hp : ∀ (c : T.Index) (n) (s), (u (X n 0 s), u (Y n 0 s)) ∈ (T.core c).window.region`
is the third conjunct of the tile's `edgeEvent`; the repo's
`T.edgeEvent X Y k` membership EXTRACTS it (`mem_window_region_of_edgeEvent`).  The
converse containment (retained scene edges always lie in each tile's window region) is
NOT produced anywhere: `window.region_subset` only goes region → clock interval.  So
`hp` remains a genuine geometric side condition.

No `sorry`, `admit` or added axiom.
-/

/-- **Monotonicity producer for `hε`**: the retained radius `ε` inherits
`ε ≤ 1/2` from an outer radius `ε₀ ≤ 1/2`. -/
theorem epsilon_le_half_of_le {ε ε₀ : ℝ} (h : ε ≤ ε₀) (h₀ : ε₀ ≤ 1 / 2) :
    ε ≤ 1 / 2 :=
  le_trans h h₀

/-- **Window-region membership extracted from the tile's edge event.**  This is exactly
the third conjunct of `T.edgeEvent`, i.e. the repo source of the `hp` field. -/
theorem mem_window_region_of_edgeEvent
    {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
    {ε : ℝ} (T : D.TaylorTiles ε) {n : ℕ} (X Y : Fin n → M) (k : T.Index)
    (ij : Fin n × Fin n) (h : ij ∈ T.edgeEvent X Y k) :
    (u (X ij.1), u (Y ij.2)) ∈ (T.core k).window.region :=
  h.2.2

end OTSelector.Reconstruction
