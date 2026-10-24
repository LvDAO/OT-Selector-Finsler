import OTSelector.Reconstruction.OriginalReserveFullUnitInputReserveDeviationLimit
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveClockSlack

/-! Genuine raw reserve class deviations at every positive intensity, independent of any main-scene model. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The unchanged original Nat and Fin prefix class counts coincide. -/
theorem originalReserveClockCount_eq_natBlockCount {q : ℕ} (C : Set ℝ)
    (cloud : MarkedCloudSpace q ℝ) :
    originalReserveClockCount q C cloud =
      originalReserveBlockCount cloud.1 (fun i ↦ (cloud.2 i).2) C := by
  rw [originalReserveBlockCount, originalReserveClassNatIndices_eq_map_fin, Finset.card_map]
  rfl

/-- The literal original Nat-index class count has its internally produced thinned Poisson law. -/
theorem map_originalReserveNatBlockCount (q : ℕ) (γ : Measure ℝ) [IsProbabilityMeasure γ]
    (rate : ℝ≥0) {C : Set ℝ} (hC : MeasurableSet C) :
    (markedPoissonLaw q ℝ γ rate).map
      (fun cloud ↦ originalReserveBlockCount cloud.1 (fun i ↦ (cloud.2 i).2) C) =
      poissonMeasure (rate * (γ C).toNNReal) := by
  have heq : (fun cloud : MarkedCloudSpace q ℝ ↦
      originalReserveBlockCount cloud.1 (fun i ↦ (cloud.2 i).2) C) = originalReserveClockCount q C :=
    funext (fun cloud ↦ (originalReserveClockCount_eq_natBlockCount C cloud).symm)
  rw [heq, map_originalReserveClockCount q γ rate hC]

/-- The genuine raw source class count law keeps every original observed index. -/
theorem hasLaw_originalRawSourceReserveNatBlockCount {q : ℕ}
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0)
    {C : Set ℝ} (hC : MeasurableSet C) :
    HasLaw (fun cloud : TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveBlockCount cloud.1.1 (fun i ↦ (cloud.1.2 i).2) C)
      (poissonMeasure (rate * (α C).toNNReal)) (twoMarkedCloudLaw q ℝ ℝ α β rate) := by
  have hm : Measurable (fun cloud : MarkedCloudSpace q ℝ ↦
      originalReserveBlockCount cloud.1 (fun i ↦ (cloud.2 i).2) C) :=
    measurable_originalReserveBlockCount measurable_fst (by fun_prop) hC
  refine ⟨(hm.comp measurable_fst).aemeasurable, ?_⟩
  change (twoMarkedCloudLaw q ℝ ℝ α β rate).map
    ((fun cloud : MarkedCloudSpace q ℝ ↦ originalReserveBlockCount cloud.1 (fun i ↦ (cloud.2 i).2) C) ∘ Prod.fst) = _
  rw [← Measure.map_map hm measurable_fst, twoMarkedCloudLaw, Measure.map_fst_prod,
    measure_univ, one_smul, map_originalReserveNatBlockCount q α rate hC]

/-- Every positive raw reserve intensity has quadratically negligible source
class-fluctuation probability. The main scene is absent from this law statement. -/
theorem tendsto_originalRawSourceReserveNatBlockCount_deviation {q : ℕ} (hq : 4 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) {C : Set ℝ} (hC : MeasurableSet C) :
    Tendsto (fun R : ℝ ↦
      let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
      R^2 * (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | r * V < |(originalReserveBlockCount cloud.1.1 (fun i ↦ (cloud.1.2 i).2) C : ℝ) -
          θ * V * α.real C|}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg) ?_
    (tendsto_originalReserveClassDeviation_bound_quadratic_zero hq b (r := r) hθ.le α C)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hV : 0 < volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toReal
    rw [volume_originalOrientedTraffic_cube b R]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    positivity
  have hm : Measurable (fun cloud : TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveBlockCount cloud.1.1 (fun i ↦ (cloud.1.2 i).2) C) :=
    measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC
  have hb := poissonCount_deviation_probability_of_hasLaw _ _ hm _
    (hasLaw_originalRawSourceReserveNatBlockCount α β
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) hC) (mul_pos hr hV)
  have hb' :
      (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount cloud.1.1 (fun i ↦ (cloud.1.2 i).2) C : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C|} ≤
      Real.sqrt (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real C) /
        (r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) := by
    simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
      Real.coe_toNNReal _ hθ.le, measureReal_def] using hb
  exact mul_le_mul_of_nonneg_left hb' (sq_nonneg R)

/-- The genuine raw target class count law keeps every original observed index. -/
theorem hasLaw_originalRawTargetReserveNatBlockCount {q : ℕ}
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0)
    {C : Set ℝ} (hC : MeasurableSet C) :
    HasLaw (fun cloud : TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveBlockCount cloud.2.1 (fun i ↦ (cloud.2.2 i).2) C)
      (poissonMeasure (rate * (β C).toNNReal)) (twoMarkedCloudLaw q ℝ ℝ α β rate) := by
  have hm : Measurable (fun cloud : MarkedCloudSpace q ℝ ↦
      originalReserveBlockCount cloud.1 (fun i ↦ (cloud.2 i).2) C) :=
    measurable_originalReserveBlockCount measurable_fst (by fun_prop) hC
  refine ⟨(hm.comp measurable_snd).aemeasurable, ?_⟩
  change (twoMarkedCloudLaw q ℝ ℝ α β rate).map
    ((fun cloud : MarkedCloudSpace q ℝ ↦ originalReserveBlockCount cloud.1 (fun i ↦ (cloud.2 i).2) C) ∘ Prod.snd) = _
  rw [← Measure.map_map hm measurable_snd, twoMarkedCloudLaw, Measure.map_snd_prod,
    measure_univ, one_smul, map_originalReserveNatBlockCount q β rate hC]

/-- Every positive raw reserve intensity has quadratically negligible target
class-fluctuation probability. The main scene is absent from this law statement. -/
theorem tendsto_originalRawTargetReserveNatBlockCount_deviation {q : ℕ} (hq : 4 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) {C : Set ℝ} (hC : MeasurableSet C) :
    Tendsto (fun R : ℝ ↦
      let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
      R^2 * (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | r * V < |(originalReserveBlockCount cloud.2.1 (fun i ↦ (cloud.2.2 i).2) C : ℝ) -
          θ * V * β.real C|}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg) ?_
    (tendsto_originalReserveClassDeviation_bound_quadratic_zero hq b (r := r) hθ.le β C)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hV : 0 < volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toReal
    rw [volume_originalOrientedTraffic_cube b R]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    positivity
  have hm : Measurable (fun cloud : TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveBlockCount cloud.2.1 (fun i ↦ (cloud.2.2 i).2) C) :=
    measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC
  have hb := poissonCount_deviation_probability_of_hasLaw _ _ hm _
    (hasLaw_originalRawTargetReserveNatBlockCount α β
      (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) hC) (mul_pos hr hV)
  have hb' :
      (twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).real
        {cloud | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount cloud.2.1 (fun i ↦ (cloud.2.2 i).2) C : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C|} ≤
      Real.sqrt (θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real C) /
        (r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) := by
    simpa only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
      Real.coe_toNNReal _ hθ.le, measureReal_def] using hb
  exact mul_le_mul_of_nonneg_left hb' (sq_nonneg R)

end OTSelector.Reconstruction
