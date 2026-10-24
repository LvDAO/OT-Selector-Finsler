import OTSelector.Reconstruction.FinslerOriginalTileMeanValues
import OTSelector.Reconstruction.FinslerOriginalAtlasSceneBridge

/-!
# Per-tile Campbell decomposition and iid counting convergence

This module reduces the two named inputs of
`FinslerOriginalTileMeanValues.lean` to their exact remaining sub-gaps.

## (a) Per-tile Campbell decomposition

The atlas scene bridge proves that the Campbell-averaged frozen cost of the
glued root function is the sum of the population-weighted seed-piece integrals,
`cam = ∑' j, ∫ piece_j, θ_j^(-2/q) G_j`
(`campbellAveragedFrozenCost_atlasPiecewiseRoot_eq_tsum`).  Refining each
population seed piece into the finitely many retained Taylor tiles -- whose root
cells are subsets of the piece and partition its roots -- gives the per-tile
population Campbell values `tilePopValue` and the decomposition
`cam = ∑_{c : T.Index} tilePopValue c + tail`, where the tail is the part of the
countable atlas not covered by the finite retained tiling.  The module defines
`tilePopValue` and proves the decomposition from the bridge identity plus the
cell-refinement and tail hypotheses.

## (b) Per-tile iid counting convergence

The per-tile iid counting convergence `RootedTileMeanConvergence` (from
`FinslerOriginalTileMeanValues.lean`) remains the probabilistic content: the
empirical frozen tile means converge to the per-tile population Campbell values
with summable error along tile refinement.  The module proves that (a) and (b)
together imply `RootedTileMeanCampbellValues`, closing the named input of
`FinslerOriginalRootedTileCampbellMean.lean`; the only remaining sub-gaps are the
cell refinement with vanishing tail and the per-tile iid counting law.

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

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **The per-tile population Campbell value.**

The population value of the retained Taylor tile `c = (i, k)` is the integral of
the atlas frozen root integrand (of the seed piece owning the tile's root cell)
against the population root law with the pressure weight `θ^(-2/q)`, over the
tile's root cell. -/
noncomputable def tilePopValue (G : ℕ → (ℚ → M) → ℝ) (c : T.Index) : ℝ :=
  ∫ z in (T.partition c.1).cell c.2,
    populationAtlasTheta P a κ lambda ((T.core c).seedIndex) z ^ (-2 / q) *
      G ((T.core c).seedIndex) z ∂lambda

/-- **Per-tile Campbell decomposition of the Campbell-averaged frozen cost.**

Combining the atlas scene bridge identity
`campbellAveragedFrozenCost_atlasPiecewiseRoot_eq_tsum` with a cell-refinement
decomposition of each population seed piece into its retained Taylor tiles, the
Campbell-averaged frozen cost of the glued root function is the finite sum of the
per-tile population Campbell values plus the tail of the countable atlas not
covered by the finite retained tiling. -/
theorem campbellAveragedFrozenCost_eq_tileSum_add_tail
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (G : ℕ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbellMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {tail : ℝ}
    (hdecomp : (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) + tail) :
    campbellAveragedFrozenCost P a κ lambda
        (atlasPiecewiseRoot P a κ lambda G) q =
      (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) + tail := by
  rw [campbellAveragedFrozenCost_atlasPiecewiseRoot_eq_tsum
    P a κ lambda G hF hcomplete hu ha hinj]
  exact hdecomp

/-! ## (b) Composition with the per-tile iid counting convergence -/

/-- **`RootedTileMeanCampbellValues` from the per-tile Campbell decomposition and
the per-tile iid counting convergence.**

With the glued root function as the frozen root integrand `g`, the cell-refinement
decomposition `cam = tileSum + tail` and the per-tile counting convergence of the
empirical frozen tile means to `tilePopValue` (with summable error), the named
Prop `RootedTileMeanCampbellValues` holds as soon as the tail vanishes.  This
reduces the named input of
`FinslerOriginalRootedTileCampbellMean.lean` to exactly: (i) cell refinement of
the population seed pieces with vanishing atlas tail, and (ii) the per-tile iid
counting law `RootedTileMeanConvergence`. -/
theorem rootedTileMeanCampbellValues_of_tile_decomposition
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileCampbell2Metric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c))
    (hconv : T.RootedTileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    T.RootedTileMeanCampbellValues q g sample X Y scale hprobe A := by
  refine rootedTileMeanCampbellValues_of_tile_mean_convergence (T := T) g sample X Y scale
    hprobe A (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) ?_ hconv
  intro f t
  have h := campbellAveragedFrozenCost_eq_tileSum_add_tail (q := q) (T := T) G hF
    hcomplete hu ha hinj (tail := 0) (by rw [add_zero]; exact hdecomp f t)
  calc campbellAveragedFrozenCost P a κ lambda (g f t) q
      = campbellAveragedFrozenCost P a κ lambda
          (atlasPiecewiseRoot P a κ lambda G) q := by rw [hgt f t]
    _ = (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) + 0 := h
    _ = ∑ c, T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c := add_zero _

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
