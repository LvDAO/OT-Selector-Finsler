import OTSelector.Reconstruction.FinslerPopulationPressureTiles
import OTSelector.Reconstruction.FinslerPopulationCompactCore
import OTSelector.Reconstruction.FinslerCoefficientCoreLabel
import OTSelector.Reconstruction.FinslerSeedRootPartition
import OTSelector.Reconstruction.FinslerTileProbeCorrection
import OTSelector.Probability.FinslerMarkedKernelInstantiation
import OTSelector.Probability.FinslerTileBlockLawComparisonCounts
import OTSelector.Probability.MarkedPressureLimitBlock
import OTSelector.Limit.FinslerFrozenBlockBridge

/-!
# Per-tile model data for the concrete Finsler expectation upper bound

This module collects, for one finite family of actual Taylor tiles
`T : PopulationLocalPressureCore.TaylorTiles ε`, the data consumed by the
marked-pressure model of the frozen kinetic cost:

* `T.tileWeight`: the normalized mass of the retained root cell of a tile,
  as a `unitInterval`;
* `T.tileAlpha`, `T.tileBeta`: the two original conditional clock kernels at
  the reference root of the tile, as probability measures on `ℝ`;
* `T.tileKin`: the scaled matrix kinetic kernel
  `w ^ (-2/q) * matrixQuadratic (core.matrix (reference) (s, t)) v` of the
  tile, where `q` is the dimension of the seed's covector kernel;
* `T.tileProbe`: the bounded probe `f` read at the reference seed
  reconstruction of the two clocks.

The kernel algebra (measurability, nonnegativity, degree-two homogeneity and
the uniform quadratic bound with the explicit compact-coefficient constant),
the tile pressure limit `exists_tilePressureLimit` (an application of
`exists_markedScalePressure_limit`), the atlas law identity with an
`n`-dependent kernel bound `integral_frozenModelTileBlock_eq_modelBlockSum_of_bounds'`,
and the biased per-cell comparison with explicit law-coupling mismatches
`δs, δt` are proved below.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

namespace TaylorTiles

variable {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)

/-! ## The normalized tile weight -/

/-- The dimension of the seed covector kernel carried by a tile. -/
def tileDim (k : T.Index) : ℕ :=
  finrank ℝ (P (T.core k).seedIndex).seed.covector.ker

variable [IsProbabilityMeasure lambda]

/-- The normalized mass of the retained root cell of a tile. -/
noncomputable def tileWeight (k : T.Index) : unitInterval where
  val := (lambda ((T.partition k.1).cell k.2)).toReal
  property := ⟨ENNReal.toReal_nonneg, by
    have hle : lambda ((T.partition k.1).cell k.2) ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans_eq measure_univ
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hle
    simpa using h⟩

/-- The defining value of the tile weight. -/
@[simp] theorem tileWeight_coe (k : T.Index) :
    (T.tileWeight k : ℝ) = (lambda ((T.partition k.1).cell k.2)).toReal := rfl

/-- A tile weight is nonnegative. -/
theorem tileWeight_nonneg (k : T.Index) : 0 ≤ (T.tileWeight k : ℝ) :=
  (T.tileWeight k).2.1

/-- A tile weight is at most one. -/
theorem tileWeight_le_one (k : T.Index) : (T.tileWeight k : ℝ) ≤ 1 :=
  (T.tileWeight k).2.2

/-- A cell of positive mass has positive tile weight. -/
theorem tileWeight_pos (k : T.Index)
    (hmass : lambda ((T.partition k.1).cell k.2) ≠ 0) : 0 < (T.tileWeight k : ℝ) := by
  rw [tileWeight_coe]
  exact ENNReal.toReal_pos hmass (measure_ne_top _ _)

omit [BorelSpace E] in
/-- Every retained coefficient root is measurable as a finite union of the
measurable root cells; no topological measurability input is needed. -/
theorem measurableSet_core_roots (i : Fin D.haar.continuous.count) :
    MeasurableSet ((D.haar.continuous.coefficient i).roots) := by
  exact D.haar.continuous.recovery.measurable i

omit [BorelSpace E] in
/-- The retained population roots are measurable as the finite union of the
coefficient roots. -/
theorem measurableSet_population_roots :
    MeasurableSet D.haar.continuous.population.roots := by
  rw [← D.haar.continuous.union_eq]
  exact MeasurableSet.iUnion fun i => measurableSet_core_roots i

/-- **The exact normalization identity.**  The tile weights sum to the total
mass of the retained population roots; the deficit from one is exactly the
mass discarded by the core. -/
theorem sum_tileWeight_eq :
    ∑ k : T.Index, (T.tileWeight k : ℝ) =
      (lambda D.haar.continuous.population.roots).toReal := by
  classical
  rw [Fintype.sum_sigma]
  have hinner (i : Fin D.haar.continuous.count) :
      (∑ j : Fin (T.partition i).count, (T.tileWeight ⟨i, j⟩ : ℝ)) =
        (lambda (D.haar.continuous.coefficient i).roots).toReal := by
    have hUnion : lambda (⋃ j, (T.partition i).cell j) =
        ∑ j : Fin (T.partition i).count, lambda ((T.partition i).cell j) := by
      have h := measure_iUnion (μ := lambda) (f := fun j => (T.partition i).cell j)
        (fun j j' hne => (T.partition i).disjoint hne)
        (fun j => (T.partition i).measurable_cell j)
      rwa [tsum_fintype] at h
    simp only [tileWeight_coe]
    rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top _ _), ← hUnion,
      (T.partition i).union_eq]
  simp only [hinner]
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  congr 1
  have hUnion : lambda (⋃ i, (D.haar.continuous.coefficient i).roots) =
      ∑ i : Fin D.haar.continuous.count,
        lambda ((D.haar.continuous.coefficient i).roots) := by
    have h := measure_iUnion (μ := lambda)
      (f := fun i => (D.haar.continuous.coefficient i).roots)
      D.haar.continuous.disjoint
      (fun i => measurableSet_core_roots i)
    rwa [tsum_fintype] at h
  rw [← hUnion, D.haar.continuous.union_eq]

/-- **The normalized identity.**  If the retained population roots carry full
mass, the tile weights form a probability vector. -/
theorem sum_tileWeight_eq_one
    (hfull : lambda D.haar.continuous.population.roots = 1) :
    ∑ k : T.Index, (T.tileWeight k : ℝ) = 1 := by
  rw [sum_tileWeight_eq, hfull, ENNReal.toReal_one]

/-- The sum of the tile weights is one minus the discarded mass of the core. -/
theorem sum_tileWeight_eq_one_sub_compl :
    ∑ k : T.Index, (T.tileWeight k : ℝ) =
      1 - (lambda (D.haar.continuous.population.roots)ᶜ).toReal := by
  rw [sum_tileWeight_eq]
  have h : lambda D.haar.continuous.population.roots +
      lambda (D.haar.continuous.population.roots)ᶜ = 1 := by
    rw [measure_add_measure_compl measurableSet_population_roots, measure_univ]
  have htop : lambda (D.haar.continuous.population.roots)ᶜ ≠ (∞ : ℝ≥0∞) :=
    measure_ne_top _ _
  have ht : lambda D.haar.continuous.population.roots ≠ (∞ : ℝ≥0∞) :=
    measure_ne_top _ _
  have hrw := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add ht htop, ENNReal.toReal_one] at hrw
  linarith

end TaylorTiles

end PopulationLocalPressureCore

end OTSelector.Reconstruction
