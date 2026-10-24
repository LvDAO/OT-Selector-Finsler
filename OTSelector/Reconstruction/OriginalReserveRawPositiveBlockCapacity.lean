import OTSelector.Reconstruction.OriginalReserveRawClassCapacity
import OTSelector.Reconstruction.OriginalReservePositiveBlockCapacityUnion

/-! True positive-block extreme reserve classes have enough original points at every positive intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- An actual first-source or last-target reserve class has fewer than half
its original theta-volume mean, over the genuine positive Hall blocks. -/
def originalRawReservePositiveBlockExtremeFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ R : ℝ) (G : OriginalStageClockGrid) : Set (TwoMarkedCloudSpace q ℝ ℝ) :=
  {cloud | ∃ block : G.ClockSlabBlock α β, block ∈ G.positiveSlabBlocks α β ∧
    ((originalReserveBlockCount cloud.1.1 (fun i ↦ (cloud.1.2 i).2)
      (G.sourceCell (G.firstBlockClass block)) : ℝ) <
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          α.real (G.sourceCell (G.firstBlockClass block)) / 2 ∨
    (originalReserveBlockCount cloud.2.1 (fun i ↦ (cloud.2.2 i).2)
      (G.targetCell (G.lastBlockClass block)) : ℝ) <
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          β.real (G.targetCell (G.lastBlockClass block)) / 2)}

/-- All positive blocks' true extreme classes satisfy their half-mean count
conditions simultaneously outside a quadratically negligible event. -/
theorem tendsto_originalRawReservePositiveBlockExtremeFailure {q : ℕ} (hq : 4 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ : ℝ} (hθ : 0 < θ) (G : OriginalStageClockGrid)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k) :
    Tendsto (fun R : ℝ ↦ R^2 * (twoMarkedCloudLaw q ℝ ℝ α β
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        (originalRawReservePositiveBlockExtremeFailure α β b θ R G)) atTop (𝓝 0) := by
  let B := ↥(G.positiveSlabBlocks α β)
  let P : ℝ → Measure (TwoMarkedCloudSpace q ℝ ℝ) := fun R ↦
    twoMarkedCloudLaw q ℝ ℝ α β
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)
  let bad : B ⊕ B → ℝ → Set (TwoMarkedCloudSpace q ℝ ℝ) := fun i R ↦ i.elim
    (fun item ↦ {cloud | (originalReserveBlockCount cloud.1.1 (fun j ↦ (cloud.1.2 j).2)
      (G.sourceCell (G.firstBlockClass item.val)) : ℝ) <
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          α.real (G.sourceCell (G.firstBlockClass item.val)) / 2})
    (fun item ↦ {cloud | (originalReserveBlockCount cloud.2.1 (fun j ↦ (cloud.2.2 j).2)
      (G.targetCell (G.lastBlockClass item.val)) : ℝ) <
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          β.real (G.targetCell (G.lastBlockClass item.val)) / 2})
  have hi (i : B ⊕ B) : Tendsto (fun R ↦ R^2 * (P R).real (bad i R)) atTop (𝓝 0) := by
    cases i with
    | inl item =>
      exact tendsto_originalRawSourceReserveNatBlockCount_lower hq α β b hθ
        measurableSet_Ico (G.positiveSlabBlock_extreme_class_masses hmono hH item.val item.property).1
    | inr item =>
      exact tendsto_originalRawTargetReserveNatBlockCount_lower hq α β b hθ
        measurableSet_Ioc (G.positiveSlabBlock_extreme_class_masses hmono hH item.val item.property).2
  have hu := tendsto_quadratic_finite_union_measureReal_zero P bad hi
  convert hu using 1
  funext R
  apply congrArg (fun A : Set (TwoMarkedCloudSpace q ℝ ℝ) ↦ R^2 * (P R).real A)
  ext cloud
  constructor
  · rintro ⟨block, hb, hs | ht⟩
    · exact ⟨Sum.inl ⟨block, hb⟩, hs⟩
    · exact ⟨Sum.inr ⟨block, hb⟩, ht⟩
  · rintro ⟨i, hi⟩
    cases i with
    | inl item => exact ⟨item.val, item.property, Or.inl hi⟩
    | inr item => exact ⟨item.val, item.property, Or.inr hi⟩

/-- The same positive-block count event has unchanged probability in any
independent auxiliary experiment. The complete main law may be retained. -/
theorem tendsto_originalRawReservePositiveBlockExtremeFailure_prod {q : ℕ} (hq : 4 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ : ℝ} (hθ : 0 < θ) (G : OriginalStageClockGrid)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k)
    {Z : Type*} [MeasurableSpace Z] (P : ℝ → ProbabilityMeasure Z) :
    Tendsto (fun R : ℝ ↦ R^2 * ((P R : Measure Z).prod
      (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))).real
        {p | p.2 ∈ originalRawReservePositiveBlockExtremeFailure α β b θ R G}) atTop (𝓝 0) := by
  convert tendsto_originalRawReservePositiveBlockExtremeFailure hq α β b hθ G hmono hH using 1
  funext R
  apply congrArg (fun t : ℝ ↦ R^2 * t)
  rw [measureReal_def, measureReal_def,
    show {p : Z × TwoMarkedCloudSpace q ℝ ℝ |
      p.2 ∈ originalRawReservePositiveBlockExtremeFailure α β b θ R G} =
      univ ×ˢ originalRawReservePositiveBlockExtremeFailure α β b θ R G by ext p; simp,
    Measure.prod_prod, measure_univ, one_mul]

end OTSelector.Reconstruction
