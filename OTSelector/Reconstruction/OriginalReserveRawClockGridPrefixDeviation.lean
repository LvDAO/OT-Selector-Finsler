import OTSelector.Reconstruction.OriginalReserveRawClassDeviation
import OTSelector.Reconstruction.OriginalReservePositiveBlockCapacityUnion

/-! Actual raw finite-grid reserve prefix concentration for every positive intensity and arbitrary independent main auxiliary. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A true source-Ico or target-Ioc original reserve prefix deviates from its
actual theta-volume mean. Every grid cut is included, including zero Hall cuts. -/
def originalReserveRawClockGridPrefixDeviationFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (θ R : ℝ)
    (G : OriginalStageClockGrid) (r : ℝ) :
    Set (TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | ∃ k : Fin (G.count + 1),
    r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
      |(originalReserveBlockCount p.1.1 (fun i ↦ (p.1.2 i).2)
          (Ico (G.cut 0) (G.cut k)) : ℝ) -
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          α.real (Ico (G.cut 0) (G.cut k))| ∨
    r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
      |(originalReserveBlockCount p.2.1 (fun i ↦ (p.2.2 i).2)
          (Ioc (G.cut 0) (G.cut k)) : ℝ) -
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          β.real (Ioc (G.cut 0) (G.cut k))|}

/-- The actual finite-grid reserve fluctuation event is Borel and reads only
original counts and marks, before conditioning on own spatial coordinates. -/
theorem measurableSet_originalReserveRawClockGridPrefixDeviationFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (θ R : ℝ)
    (G : OriginalStageClockGrid) (r : ℝ) :
    MeasurableSet (originalReserveRawClockGridPrefixDeviationFailure α β b θ R G r) := by
  have h (k : Fin (G.count+1)) : MeasurableSet
      {p : TwoMarkedCloudSpace q ℝ ℝ |
        r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount p.1.1 (fun i ↦ (p.1.2 i).2) (Ico (G.cut 0) (G.cut k)) : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real (Ico (G.cut 0) (G.cut k))| ∨
        r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount p.2.1 (fun i ↦ (p.2.2 i).2) (Ioc (G.cut 0) (G.cut k)) : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real (Ioc (G.cut 0) (G.cut k))|} := by
    apply MeasurableSet.union
    · exact measurableSet_lt measurable_const
        (((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
          (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ico)).sub measurable_const).abs
    · exact measurableSet_lt measurable_const
        (((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
          (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ioc)).sub measurable_const).abs
  simpa only [originalReserveRawClockGridPrefixDeviationFailure, Set.ofPred_exists] using MeasurableSet.iUnion h

/-- True raw reserve Poisson laws give simultaneous finite-grid prefix
concentration for every theta>0. No matching law, selected law or theta<1 is an input. -/
theorem tendsto_originalReserveRawClockGridPrefixDeviationFailure {q : ℕ} (hq : 4 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ r : ℝ} (hθ : 0 < θ) (G : OriginalStageClockGrid) (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦
      R^2 * (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        (originalReserveRawClockGridPrefixDeviationFailure α β b θ R G r)) atTop (𝓝 0) := by
  let I := Fin (G.count+1)
  let P : ℝ → Measure (TwoMarkedCloudSpace q ℝ ℝ) := fun R ↦ twoMarkedCloudLaw q ℝ ℝ α β
    (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)
  let bad : I ⊕ I → ℝ → Set (TwoMarkedCloudSpace q ℝ ℝ) :=
    fun i R ↦ i.elim
      (fun k : I ↦ {p | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
        |(originalReserveBlockCount p.1.1 (fun i ↦ (p.1.2 i).2) (Ico (G.cut 0) (G.cut k)) : ℝ) -
          θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real (Ico (G.cut 0) (G.cut k))|})
      (fun k : I ↦ {p | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
        |(originalReserveBlockCount p.2.1 (fun i ↦ (p.2.2 i).2) (Ioc (G.cut 0) (G.cut k)) : ℝ) -
          θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real (Ioc (G.cut 0) (G.cut k))|})
  have hi (i : I ⊕ I) : Tendsto (fun R ↦ R^2 * (P R).real (bad i R)) atTop (𝓝 0) := by
    cases i with
    | inl k =>
      exact tendsto_originalRawSourceReserveNatBlockCount_deviation hq α β b hθ hr measurableSet_Ico
    | inr k =>
      exact tendsto_originalRawTargetReserveNatBlockCount_deviation hq α β b hθ hr measurableSet_Ioc
  have hu := tendsto_quadratic_finite_union_measureReal_zero P bad hi
  convert hu using 1
  funext R
  apply congrArg (fun A : Set (TwoMarkedCloudSpace q ℝ ℝ) ↦ R^2 * (P R).real A)
  ext p
  constructor
  · rintro ⟨k, hs | ht⟩
    · exact ⟨Sum.inl k, hs⟩
    · exact ⟨Sum.inr k, ht⟩
  · rintro ⟨i, hp⟩
    cases i with
    | inl k => exact ⟨k, Or.inl hp⟩
    | inr k => exact ⟨k, Or.inr hp⟩

/-- Any actual independent probability auxiliary, including the unchanged
unit main scene and arbitrary other experiment data, preserves this exact raw
prefix event probability. No own-position-dependent witness enters its aux. -/
theorem tendsto_originalReserveRawClockGridPrefixDeviationFailure_prod
    {q : ℕ} (hq : 4 < q) (α β : Measure ℝ)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ r : ℝ} (hθ : 0 < θ) (G : OriginalStageClockGrid) (hr : 0 < r)
    {Z : Type*} [MeasurableSpace Z] (P : ℝ → ProbabilityMeasure Z) :
    Tendsto (fun R : ℝ ↦
      R^2 * (((P R : Measure Z)).prod (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))).real
          {p | p.2 ∈ originalReserveRawClockGridPrefixDeviationFailure α β b θ R G r})
      atTop (𝓝 0) := by
  convert tendsto_originalReserveRawClockGridPrefixDeviationFailure hq α β b hθ G hr using 1
  funext R
  apply congrArg (fun t : ℝ ↦ R^2 * t)
  rw [measureReal_def, measureReal_def,
    show {p : Z × TwoMarkedCloudSpace q ℝ ℝ |
      p.2 ∈ originalReserveRawClockGridPrefixDeviationFailure α β b θ R G r} =
      univ ×ˢ originalReserveRawClockGridPrefixDeviationFailure α β b θ R G r by ext p; simp,
    Measure.prod_prod, measure_univ, one_mul]

end OTSelector.Reconstruction
