import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingOriginalUnusedFamiliesKeptData
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloors
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockOriginalDeletedCounts

/-! Literal FULL-array observations and actual reserve good counts for signed screening. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Unchanged FULL labels, their genuine original reserve embeddings and the
literal main-plus-reserve readouts. This record contains observed finite data,
without a matching, a stage plan, a scalar floor or a local repair. -/
structure OriginalClockBlockFullArrayData {q : ℕ} {μ ν : Measure ℝ}
    (G : OriginalStageClockGrid)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) (m n : ℕ) where
  source : Fin m → LegalMarkedPhysicalPoint q
  target : Fin n → LegalMarkedPhysicalPoint q
  source_injective : Injective source
  target_injective : Injective target
  sourceEmbedding : Fin p.2.1.1 ↪ Fin m
  targetEmbedding : Fin p.2.2.1 ↪ Fin n
  source_original : ∀ j, source (sourceEmbedding j) =
    (originalMappedReserveCloud q (originalOrientedRawCubePhysicalMap b R) p.2.1).2 j
  target_original : ∀ j, target (targetEmbedding j) =
    (originalMappedReserveCloud q (originalOrientedRawCubePhysicalMap b R) p.2.2).2 j
  source_counting : (∑ i, Measure.dirac (source i)) =
    (legalInputColorMeasure _ p.1.2 0).restrict {x | x.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}+
      ∑ j : Fin p.2.1.1, Measure.dirac
        ((originalMappedReserveCloud q (originalOrientedRawCubePhysicalMap b R) p.2.1).2 j)
  target_counting : (∑ j, Measure.dirac (target j)) =
    (legalInputColorMeasure _ p.1.2 1).restrict {x | x.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}+
      ∑ j : Fin p.2.2.1, Measure.dirac
        ((originalMappedReserveCloud q (originalOrientedRawCubePhysicalMap b R) p.2.2).2 j)
  source_grid : ∀ i, G.sourceLabel (source i).2 < G.count
  target_grid : ∀ j, G.targetLabel (target j).2 < G.count
  monochrome : ∀ k : Fin G.count, (∀ i, (source i).2 ∉ G.sourceCell k) ∨
    (∀ j, (target j).2 ∉ G.targetCell k)
  source_carrier : ∀ i, (source i).1 ∈ originalCenteredPhysicalCubeRegion b (2*R)
  target_carrier : ∀ j, (target j).1 ∈ originalCenteredPhysicalCubeRegion b (2*R)
  source_blocks : ∀ block : G.ClockSlabBlock μ ν,
    (Finset.univ.filter (fun i ↦ (source i).2 ∈ G.sourceBlockCell μ ν block)).card =
      originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2*R)) (G.sourceBlockCell μ ν block) 0 p.1+
        originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2) (G.sourceBlockCell μ ν block)
  target_blocks : ∀ block : G.ClockSlabBlock μ ν,
    (Finset.univ.filter (fun j ↦ (target j).2 ∈ G.targetBlockCell μ ν block)).card =
      originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2*R)) (G.targetBlockCell μ ν block) 1 p.1+
        originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2) (G.targetBlockCell μ ν block)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The good counts are exactly raw prefixes, actual requested excesses,
actual endpoint deletion capacities and literal full-current cut errors. -/
structure OriginalClockBlockGoodCounts
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (G : OriginalStageClockGrid) (μ ν : Measure ℝ)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R θ e : ℝ)
    (p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) : Prop where
  source_capacity : ∀ block : G.ClockSlabBlock μ ν,
    originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
      (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
      ((p.1,p.2.2),p.2.1.1,fun i ↦ (p.2.1.2 i).2) ≤
        originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2) (G.sourceCell (G.firstBlockClass block))
  target_capacity : ∀ block : G.ClockSlabBlock μ ν,
    originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
      (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
      ((p.1,p.2.1),p.2.2.1,fun i ↦ (p.2.2.2 i).2) ≤
        originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2) (G.targetCell (G.lastBlockClass block))
  source_prefix : ∀ k : Fin (G.count+1),
    |(originalReserveBlockCount p.2.1.1 (fun i ↦ (p.2.1.2 i).2) (Ico (G.cut 0) (G.cut k.val)) : ℝ)-
      θ*(volume.real (originalCenteredPhysicalCubeRegion b (2*R)))*μ.real (Ico (G.cut 0) (G.cut k.val))| ≤
        e*(volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
  target_prefix : ∀ k : Fin (G.count+1),
    |(originalReserveBlockCount p.2.2.1 (fun i ↦ (p.2.2.2 i).2) (Ioc (G.cut 0) (G.cut k.val)) : ℝ)-
      θ*(volume.real (originalCenteredPhysicalCubeRegion b (2*R)))*ν.real (Ioc (G.cut 0) (G.cut k.val))| ≤
        e*(volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
  deletions : (((∑ block : G.ClockSlabBlock μ ν,
    (originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
      (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
      ((p.1,p.2.2),p.2.1.1,fun i ↦ (p.2.1.2 i).2) +
    originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
      (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
      ((p.1,p.2.1),p.2.2.1,fun i ↦ (p.2.2.2 i).2))) : ℕ) : ℝ) ≤
        e*(volume.real (originalCenteredPhysicalCubeRegion b (2*R)))
  cuts : ∀ k : Fin (G.count+1), |originalOrientedStageFullCutError S w b R (G.cut k.val) p.1| ≤
    e*(volume.real (originalCenteredPhysicalCubeRegion b (2*R)))

end OTSelector.Reconstruction
