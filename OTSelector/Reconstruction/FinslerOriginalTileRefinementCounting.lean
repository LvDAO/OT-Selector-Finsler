import OTSelector.Reconstruction.FinslerOriginalTileCountingConvergence

/-!
# Cell refinement with vanishing tail for the retained Taylor tiling

This module attacks the two sub-gaps of
`FinslerOriginalTileCountingConvergence.lean`.

## (a1) Cell refinement

The retained Taylor tiles of one coefficient refine the coefficient's root set
into disjoint measurable cells (`FiniteRootNeighborhoodPartition.union_eq`,
`disjoint`, `measurable_cell`), and the coefficient's root set is contained in its
population seed root piece (`OriginalPopulationCoefficientCore.roots_subset_piece`).
Hence, almost everywhere on the seed piece, every root lies in exactly one
retained cell: the cell refinement covering.  This module proves that covering,
and reduces the per-piece integral decomposition to a named measure-theoretic
per-piece identity together with the vanishing of the atlas tail.

## (b) Per-tile counting convergence

The per-tile iid counting convergence stays the named probabilistic content
`RootedTileMeanConvergence`.  The module states the exact composition: per-piece
cell refinement + vanishing atlas tail + per-tile counting convergence imply the
per-tile Campbell decomposition and hence `RootedTileMeanCampbellValues`.

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

/-- **The retained cells refine the population seed piece almost everywhere.**

The retained Taylor cells of a coefficient partition its root set
(`FiniteRootNeighborhoodPartition.union_eq`), the root set is contained in the
coefficient's population seed root piece
(`OriginalPopulationCoefficientCore.roots_subset_piece`), and if the piece is
almost everywhere contained in the root set then almost every root of the piece
lies in exactly one retained cell.  This is the cell refinement covering for the
per-tile Campbell decomposition. -/
theorem ae_piece_mem_iUnion_cells (c : T.Index)
    (hrev : ∀ᵐ z ∂lambda.restrict
      (populationSeedRootPiece P a κ lambda (T.core c).seedIndex),
      z ∈ (T.core c).roots) :
    ∀ᵐ z ∂lambda.restrict
      (populationSeedRootPiece P a κ lambda (T.core c).seedIndex),
      z ∈ ⋃ k : Fin (T.partition c.1).count, (T.partition c.1).cell k := by
  filter_upwards [hrev] with z hz
  rw [(T.partition c.1).union_eq]
  exact hz

/-- **Per-piece cell refinement of the population integral** (named per-piece
measure-theoretic identity).

On each retained coefficient, the population-weighted frozen root-integral over
the coefficient's seed piece equals the sum of the tile cell integrals.  The
covering is proved in `ae_piece_mem_iUnion_cells`; this identity is the
cell-refinement step
`∫ piece = ∑ k, ∫ cell k`
(with the a.e. piece/root-set identification and integrability as its inputs). -/
def PieceCellRefinement (G : ℕ → (ℚ → M) → ℝ) : Prop :=
  ∀ i : Fin D.haar.continuous.count,
    (∫ z in populationSeedRootPiece P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex,
      populationAtlasTheta P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
        G (D.haar.continuous.coefficient i).seedIndex z ∂lambda) =
    ∑ k : Fin (T.partition i).count,
      ∫ z in (T.partition i).cell k,
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z ∂lambda

/-- **Per-tile Campbell decomposition from cell refinement and vanishing tail.**

If (i) the seed-piece integrals refine into the retained tile cell integrals
(`PieceCellRefinement`), (ii) the atlas tail beyond the finite retained
coefficient family vanishes, and (iii) the finite coefficient family indexes the
selected population seed pieces, then the named per-tile Campbell decomposition
`cam = ∑_{c : T.Index} tilePopValue c` holds.  This is exactly the hypothesis
`hdecomp` consumed by
`campbellAveragedFrozenCost_eq_tileSum_add_tail` of
`FinslerOriginalTileCountingConvergence.lean`. -/
theorem campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (G : ℕ → (ℚ → M) → ℝ)
    (hrefine : T.PieceCellRefinement (q := q) G)
    (htail : (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      ∑ i : Fin D.haar.continuous.count,
        ∫ z in populationSeedRootPiece P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex,
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda) :
    (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      ∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c := by
  rw [htail]
  have h1 : (∑ i : Fin D.haar.continuous.count,
      ∫ z in populationSeedRootPiece P a κ lambda
          (D.haar.continuous.coefficient i).seedIndex,
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z ∂lambda) =
      ∑ i : Fin D.haar.continuous.count, ∑ k : Fin (T.partition i).count,
        ∫ z in (T.partition i).cell k,
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda :=
    Finset.sum_congr rfl fun i _ ↦ hrefine i
  rw [h1]
  exact Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ)
    (fun (i : Fin D.haar.continuous.count) (k : Fin (T.partition i).count) ↦
      ∫ z in (T.partition i).cell k,
        populationAtlasTheta P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
          G (D.haar.continuous.coefficient i).seedIndex z ∂lambda)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
