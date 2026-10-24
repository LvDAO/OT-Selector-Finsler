/-
# Discharging tile-lane covering and plan-feasibility fields

This module strengthens `tileLaneInputs_of_laneData` of
`FinslerOriginalTileLaneInputs.lean` for the actual lane:

* `hdecomp` is discharged to the cell-refinement theorem of
  `FinslerOriginalTileRefinementCounting.lean`: the population covering identity
  follows from the per-coefficient cell-refinement integral identity
  (`T.PieceCellRefinement`) together with the vanishing of the atlas tail outside
  the finite retained coefficient family (`htail`).  The covering part of
  `PieceCellRefinement` is available from `ae_piece_mem_iUnion_cells`; the
  per-piece integral refinement itself stays as the single named
  measure-theoretic input `hrefine`, and the finite-tail identity as `htail`.
* the thin-plan fields `hAnonneg`, `hrow`, `hcol` are discharged from the single
  matrix feasibility hypothesis `hds : Assign n s ∈ doublyStochastic ℝ (Fin (n+1))`
  (Mathlib: `nonneg_of_mem_doublyStochastic`, `sum_row_of_mem_doublyStochastic`,
  `sum_col_of_mem_doublyStochastic`).

## Exact remaining inputs

* `hintEntry`, `hintCost`, `hintRes`: entrywise/pair-sum integrability (the probe
  base is only bounded in the lane data, not measurable, so these stay explicit);
* `hprobePair`, `hΨ`, `hΨb`: probe pair functionality and pair-kernel
  measurability/boundedness (discharge `hExch`);
* `hscale0`, `hscale`, `hphys`, `hprobeB`: normalization bounds (discharge `hresv`);
* `hopt`: optimality of the thin plan for the concrete tile cost (the assignment
  is optimal against the uniform plan for each `(f,t,n,c,s)`);
* `hrefine`, `htail`: per-piece cell-refinement integral identity and finite atlas
  tail identity (discharge `hdecomp`);
* `hds`: feasibility of the assignment matrix.

No `sorry`, `admit` or added axiom occurs.
-/
import OTSelector.Reconstruction.FinslerOriginalTileLaneInputs
import OTSelector.Reconstruction.FinslerOriginalTileRefinementCounting


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
  [MeasurableSpace.CountablySeparated (ℚ → M)]

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **The population covering identity from cell refinement and vanishing tail.**

The `hdecomp` field of the tile lane holds for the actual lane once the
per-coefficient cell-refinement integral identity `T.PieceCellRefinement` and the
finite atlas tail identity hold: this is
`campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement` of
`FinslerOriginalTileRefinementCounting.lean`, which is exactly the population
covering identity consumed by the readout lane. -/
theorem hdecomp_of_cell_refinement
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
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c) :=
  fun _ _ ↦ campbellAveragedFrozenCost_eq_tileSum_of_cell_refinement
    (T := T) G hrefine htail

def tileLaneInputs_of_cellRefinement    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    {μ ν : ℕ → Measure M} [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)), Measurable (Y n j))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (sample n).map (X n i) = μ n)
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (sample n).map (Y n j) = ν n)
    (hpair : ∀ (n : ℕ) (i j : Fin (n + 1)), IndepFun (X n i) (Y n j) (sample n))
    (probeKernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobePair : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)),
      normalizedProbe (K := K) base t n s c i j = probeKernel f t n c (X n i s, Y n j s))
    (hΨ : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (scale n) t (probeKernel f t n c)))
    (hΨb : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ Cb : ℝ, ∀ p : M × M, |T.tilePairKernel c (scale n) t (probeKernel f t n c) p| ≤ Cb)
    (S B Pc : ℝ) (hB : 0 ≤ B) (hε0 : 0 ≤ 1 - 2 * ε)
    (hC₀ : 0 ≤ (1 - 2 * ε) * S * B + Pc)
    (hscale0 : ∀ n, 0 ≤ scale n)
    (hscale : ∀ n, scale n ≤ S / ((n + 1 : ℕ) : ℝ))
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ B)
    (hprobeB : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)),
      t * normalizedProbe (K := K) base t n s c i j ≤ Pc / ((n + 1 : ℕ) : ℝ))
    (hds : ∀ (n : ℕ) (s : Ω n), Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n),
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')) n c s) (Assign n s) ≤
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')) n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    
        (hrefine : T.PieceCellRefinement (q := q) G)
    (htail : (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
      ∑ i : Fin D.haar.continuous.count,
        ∫ z in populationSeedRootPiece P a κ lambda
            (D.haar.continuous.coefficient i).seedIndex,
          populationAtlasTheta P a κ lambda
              (D.haar.continuous.coefficient i).seedIndex z ^ (-2 / q) *
            G (D.haar.continuous.coefficient i).seedIndex z ∂lambda)
    :
    TileLaneInputs (P := P) (a := a) (κ := κ) (lambda := lambda) (D := D) (ε := ε) (T := T) (K := K) (q := q) (base := base) (sample := sample) (X := X) (Y := Y) (scale := scale) (G := G) :=
  tileLaneInputs_of_laneData (K := K) (q := q) (T := T) sample G X Y scale base
    Assign hintEntry hintCost hintRes hX hY hXlaw hYlaw hpair probeKernel hprobePair
    hΨ hΨb S B Pc hB hε0 hC₀ hscale0 hscale hphys hprobeB
    (fun n s i j ↦ nonneg_of_mem_doublyStochastic (hds n s) (i := i) (j := j))
    (fun n s i ↦ sum_row_of_mem_doublyStochastic (hds n s) i)
    (fun n s j ↦ sum_col_of_mem_doublyStochastic (hds n s) j)
    hopt (hdecomp_of_cell_refinement (T := T) (q := q) G hrefine htail)

end PopulationLocalPressureCore.TaylorTiles
end OTSelector.Reconstruction
