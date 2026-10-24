import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeInnerValue
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape
import OTSelector.Probability.BlockDataTransport

/-! Exact Poisson expectation of the actual inner oriented cube, with original marks unchanged. -/

open Set Function MeasureTheory ProbabilityTheory
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
variable {q : ℕ}

/-- Transport the actual Poisson prefix to the conditional law inside the oriented cube. -/
theorem map_originalOrientedShape_inner_prefix
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 < s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1 / 2))
    (α : Measure ℝ) [IsProbabilityMeasure α] (r : ℝ≥0) :
    (markedPoissonLaw q ℝ α (r * Real.toNNReal (s ^ q))).map
      (fun z ↦ mapBlockData
        (Prod.map (originalOrientedShapeUnitInnerMap b s) id) (cloudEncode z)) =
      shapeBlockLaw q α r (originalOrientedShapeUnitInner b s) := by
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have hU : Measurable (originalOrientedShapeUnitInnerMap b s) :=
    measurable_originalOrientedShapeUnitInnerMap b s
  have hpoint :
      ((cubeMeasure (Fin q) 1).prod α).map
        (Prod.map (originalOrientedShapeUnitInnerMap b s) id) =
      (restrictedPointLaw (cubeMeasure (Fin q) 1)
        (originalOrientedShapeUnitInner b s)).prod α := by
    rw [← Measure.map_prod_map _ _ hU measurable_id,
      map_originalOrientedShapeUnitInnerMap b hs hsub, Measure.map_id]
  have hweight : restrictionWeight (cubeMeasure (Fin q) 1)
      (originalOrientedShapeUnitInner b s) = Real.toNNReal (s ^ q) := by
    unfold restrictionWeight
    rw [originalOrientedShapeUnitInner_mass b hs.le hsub]
    simp [ENNReal.ofReal]
  have hencode :
      (markedPoissonLaw q ℝ α (r * Real.toNNReal (s ^ q))).map cloudEncode =
      blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
        (fun n ↦ poissonMeasure (r * Real.toNNReal (s ^ q)) {n}) := by
    rw [blockDataLaw_eq_map_cloud]
    rfl
  calc
    _ = ((markedPoissonLaw q ℝ α (r * Real.toNNReal (s ^ q))).map cloudEncode).map
        (mapBlockData (Prod.map (originalOrientedShapeUnitInnerMap b s) id)) := by
      rw [Measure.map_map (measurable_mapBlockData (hU.prodMap measurable_id))
        measurable_cloudEncode]
      rfl
    _ = (blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
        (fun n ↦ poissonMeasure (r * Real.toNNReal (s ^ q)) {n})).map
        (mapBlockData (Prod.map (originalOrientedShapeUnitInnerMap b s) id)) := by
      rw [hencode]
    _ = blockDataLaw
        ((restrictedPointLaw (cubeMeasure (Fin q) 1)
          (originalOrientedShapeUnitInner b s)).prod α)
        (fun n ↦ poissonMeasure (r * Real.toNNReal (s ^ q)) {n}) :=
      blockDataLaw_mapPoints _ _ (hU.prodMap measurable_id) hpoint _
    _ = _ := by unfold shapeBlockLaw; rw [hweight]

/-- The two colors remain independent under the actual inner-cube readout. -/
theorem map_originalOrientedShape_two_inner_prefix
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 < s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1 / 2))
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) :
    (twoMarkedCloudLaw q ℝ ℝ α β (r * Real.toNNReal (s ^ q))).map
      (Prod.map
        (fun z ↦ mapBlockData (Prod.map (originalOrientedShapeUnitInnerMap b s) id)
          (cloudEncode z))
        (fun z ↦ mapBlockData (Prod.map (originalOrientedShapeUnitInnerMap b s) id)
          (cloudEncode z))) =
      (shapeBlockLaw q α r (originalOrientedShapeUnitInner b s)).prod
        (shapeBlockLaw q β r (originalOrientedShapeUnitInner b s)) := by
  have hU : Measurable (originalOrientedShapeUnitInnerMap b s) :=
    measurable_originalOrientedShapeUnitInnerMap b s
  have hread : Measurable
      (fun z : MarkedCloudSpace q ℝ ↦ mapBlockData
        (Prod.map (originalOrientedShapeUnitInnerMap b s) id) (cloudEncode z)) :=
    (measurable_mapBlockData (hU.prodMap measurable_id)).comp measurable_cloudEncode
  unfold twoMarkedCloudLaw
  rw [← Measure.map_prod_map _ _ hread hread,
    map_originalOrientedShape_inner_prefix b hs hsub α r,
    map_originalOrientedShape_inner_prefix b hs hsub β r]

/-- The inner-cube mean is exactly the pressure of the frame-transformed kinetic kernel. -/
theorem integral_originalOrientedShape_inner_eq_pressure
    (hq : 0 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 < s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1 / 2))
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c * v i) = c ^ 2 * kin a d v)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    (∫ ω, shapeLegalMarkedTilted q id id (originalOrientedShapeUnitInner b s)
        r kin g t ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) =
      legalMarkedPressure q id id α β (r * Real.toNNReal (s ^ q))
        (originalScreeningFrameKinetic b kin) g t := by
  let c : ℝ≥0 := r * Real.toNNReal (s ^ q)
  let read := fun z : MarkedCloudSpace q ℝ ↦ mapBlockData
    (Prod.map (originalOrientedShapeUnitInnerMap b s) id) (cloudEncode z)
  let pick := Prod.map read read
  let S := originalOrientedShapeUnitInner b s
  let law := (shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)
  let V := fun d : BlockData ((Fin q → ℝ) × ℝ) × BlockData ((Fin q → ℝ) × ℝ) ↦
    blockLegalTilted q id id r kin g t d.1 d.2
  have hS : MeasurableSet S := measurableSet_originalOrientedShapeUnitInner b s
  have hread : Measurable read :=
    (measurable_mapBlockData
      ((measurable_originalOrientedShapeUnitInnerMap b s).prodMap measurable_id)).comp
      measurable_cloudEncode
  have hpick : Measurable pick := hread.prodMap hread
  have hmap : (twoMarkedCloudLaw q ℝ ℝ α β c).map pick = law :=
    map_originalOrientedShape_two_inner_prefix b hs hsub α β r
  have hV : Measurable V :=
    measurable_blockLegalTilted q measurable_id measurable_id r hk hg t
  have hunit : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β c,
      (∀ i, ((pick ω).1.2 i).1 ∈ unitCube q) ∧
      (∀ j, ((pick ω).2.2 j).1 ∈ unitCube q) := by
    have hshape := ae_shapeBlockLaw_unitCube_two q α β r hS
    change ∀ᵐ d ∂law, (∀ i, (d.1.2 i).1 ∈ unitCube q) ∧
      (∀ j, (d.2.2 j).1 ∈ unitCube q) at hshape
    rw [← hmap] at hshape
    exact ae_of_ae_map hpick.aemeasurable hshape
  have hcount : (c : ℝ) = (r : ℝ) * s ^ q := by
    simp only [c, NNReal.coe_mul, Real.coe_toNNReal _ (pow_nonneg hs.le q)]
  have hAE : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β c,
      V (pick ω) = legalMarkedTilted q id id c
        (originalScreeningFrameKinetic b kin) g t ω := by
    filter_upwards [hunit, ae_points_mem_unitCube_twoMarkedCloudLaw q α β c] with ω hu hc
    simp only [pick, Prod.map_fst, Prod.map_snd] at hu
    change blockLegalTilted q id id r kin g t (read ω.1) (read ω.2) = _
    rw [← unclampedBlockLegalTilted_eq_block q id id r kin g t _ _ hu.1 hu.2]
    dsimp only [read]
    rw [unclamped_originalOrientedShape_inner_value hq b r.coe_nonneg hs.le kin hhom g t,
      ← hcount]
    rw [unclampedBlockLegalTilted_eq_block q id id c (originalScreeningFrameKinetic b kin)
      g t _ _ (fun i ↦ hc.1 i) (fun j ↦ hc.2 j)]
    exact blockLegalTilted_cloudPrefix q id id c (originalScreeningFrameKinetic b kin) g t ω
  have hshapePick : Measurable
      (Prod.map (shapeCloud (A := ℝ) S) (shapeCloud (A := ℝ) S)) :=
    (measurable_shapeCloud hS).prodMap (measurable_shapeCloud hS)
  calc
    _ = ∫ d, V d ∂law := by
      rw [show law = (twoMarkedCloudLaw q ℝ ℝ α β r).map
        (Prod.map (shapeCloud S) (shapeCloud S)) from
        (map_shapeCloud_twoMarkedCloudLaw q α β r hS).symm,
        integral_map hshapePick.aemeasurable hV.aestronglyMeasurable]
      rfl
    _ = ∫ ω, V (pick ω) ∂twoMarkedCloudLaw q ℝ ℝ α β c := by
      rw [← hmap, integral_map hpick.aemeasurable hV.aestronglyMeasurable]
    _ = _ := by rw [integral_congr_ae hAE]; rfl

end OTSelector.Reconstruction
