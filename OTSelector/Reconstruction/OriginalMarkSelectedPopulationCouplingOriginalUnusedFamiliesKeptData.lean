import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingOriginalUnusedFamilies
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsGlobalKept

/-! The original RN datum is exactly the actual block-deleted physical datum. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Physical placement preserves all original clock-count inputs to the
actual excess; no equality of the raw and physical opposite clouds is asserted. -/
theorem originalReserveBlockExcess_map_positions {q : ℕ} (K : Set (Fin q → ℝ))
    (own other : Fin 2) (S T : Set ℝ) (scene : LegalMarkedOptimalInputScene q)
    (source opposite : MarkedCloudSpace q ℝ) (Fs Ft : (Fin q → ℝ) → (Fin q → ℝ)) :
    originalReserveBlockExcess K own other S T
      ((scene, originalMappedReserveCloud q Ft opposite),
        (originalMappedReserveCloud q Fs source).1,
        fun i ↦ ((originalMappedReserveCloud q Fs source).2 i).2) =
      originalReserveBlockExcess K own other S T ((scene,opposite),source.1,fun i ↦ (source.2 i).2) := rfl

/-- The complete global original Fin kept set is unchanged by physical placement. -/
theorem originalReserveBlocksKeptFin_map_positions {q : ℕ} {B : Type*} [Fintype B]
    (K : Set (Fin q → ℝ)) (own other : Fin 2) (S T C : B → Set ℝ)
    (scene : LegalMarkedOptimalInputScene q) (source opposite : MarkedCloudSpace q ℝ)
    (Fs Ft : (Fin q → ℝ) → (Fin q → ℝ)) :
    originalReserveBlocksKeptFin K own other S T C
      ((scene, originalMappedReserveCloud q Ft opposite),
        (originalMappedReserveCloud q Fs source).1,
        fun i ↦ ((originalMappedReserveCloud q Fs source).2 i).2) =
      originalReserveBlocksKeptFin K own other S T C
        ((scene,opposite),source.1,fun i ↦ (source.2 i).2) := rfl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] in
/-- The same scene, physically placed original words and exact first/last
class deletions give literally the datum used by the clock-block producer. -/
theorem originalUnusedBlockReserveData_eq_originalOrientedClockBlockKeptData
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    (G : OriginalStageClockGrid) {μ ν : Measure ℝ}
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) :
    originalUnusedBlockReserveData S w b R ell G h₀ hN p =
      originalOrientedClockBlockKeptData S w G μ ν b R ell p.1
        (originalMappedReserveCloud _ (originalOrientedRawCubePhysicalMap b R) p.2.1)
        (originalMappedReserveCloud _ (originalOrientedRawCubePhysicalMap b R) p.2.2)
        (fun block ↦ G.sourceCell (G.firstBlockClass block))
        (fun block ↦ G.targetCell (G.lastBlockClass block)) := rfl

end OTSelector.Reconstruction
