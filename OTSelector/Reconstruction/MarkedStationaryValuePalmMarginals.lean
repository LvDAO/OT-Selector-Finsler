import OTSelector.Reconstruction.MarkedStationaryValuePalmScene
import Mathlib.MeasureTheory.Group.Prod

/-!
# Original paired-edge Palm clock marginals

The source and target intensity measures are the actual projections of the
same original physical plan. The paired-edge Palm retains both clocks and the
full displacement. Haar skew translation identifies the target intensity
without any displacement moment premise.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

local instance markedStationaryValuePalmMarginalsLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The target intensity kernel is the actual target projection of the same
original first scene plan. -/
def physicalSceneTargetKernel :
    Kernel (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) ((ι → ℝ) × ℝ) :=
  (localFiniteMeasureKernel.comap Prod.fst measurable_fst).map Prod.snd

instance physicalSceneTargetKernelIsSFinite :
    IsSFiniteKernel (physicalSceneTargetKernel (ι := ι)) := by
  unfold physicalSceneTargetKernel
  infer_instance

/-- The actual target intensity measure of the original first plan. -/
def physicalSceneTargetIntensity
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure ((ι → ℝ) × ℝ) := P.bind physicalSceneTargetKernel

/-- Read the source point and its original scalar clock from the anchored
paired edge. -/
def physicalPairSourcePoint (p : (ι → ℝ) × PhysicalPairPalmMark ι) : (ι → ℝ) × ℝ :=
  (p.1, p.2.1.1)

/-- Reconstruct the actual original target point using the full original
displacement vector and the original target clock. -/
def physicalPairTargetPoint (p : (ι → ℝ) × PhysicalPairPalmMark ι) : (ι → ℝ) × ℝ :=
  (p.1 + p.2.2, p.2.1.2)

omit [Fintype ι] in
theorem measurable_physicalPairSourcePoint : Measurable (physicalPairSourcePoint (ι := ι)) :=
  measurable_fst.prodMk measurable_snd.fst.fst

omit [Fintype ι] in
theorem measurable_physicalPairTargetPoint : Measurable (physicalPairTargetPoint (ι := ι)) :=
  (measurable_fst.add measurable_snd.snd).prodMk measurable_snd.fst.snd

/-- The actual source intensity is the source-clock projection of the
constructed original paired-edge Campbell measure. -/
theorem physicalSceneSourceIntensity_eq_map_pairCampbell
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    physicalSceneSourceIntensity P =
      (physicalScenePairCampbell P).map physicalPairSourcePoint := by
  ext B hB
  rw [physicalSceneSourceIntensity,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    Measure.map_apply measurable_physicalPairSourcePoint hB,
    physicalScenePairCampbell,
    Measure.bind_apply (measurable_physicalPairSourcePoint hB)
      (Kernel.measurable _).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with scene
  have hs : physicalSceneSourceKernel scene =
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).map Prod.fst :=
    Kernel.map_apply _ measurable_fst scene
  rw [hs, physicalScenePairKernel_apply, Measure.map_apply measurable_fst hB,
    Measure.map_apply measurable_physicalPairAnchor (measurable_physicalPairSourcePoint hB)]
  rfl

/-- The actual target intensity is reconstructed from the same Campbell
measure by the full original transverse displacement. -/
theorem physicalSceneTargetIntensity_eq_map_pairCampbell
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    physicalSceneTargetIntensity P =
      (physicalScenePairCampbell P).map physicalPairTargetPoint := by
  ext B hB
  rw [physicalSceneTargetIntensity,
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    Measure.map_apply measurable_physicalPairTargetPoint hB,
    physicalScenePairCampbell,
    Measure.bind_apply (measurable_physicalPairTargetPoint hB)
      (Kernel.measurable _).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with scene
  have ht : physicalSceneTargetKernel scene =
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).map Prod.snd :=
    Kernel.map_apply _ measurable_snd scene
  rw [ht, physicalScenePairKernel_apply, Measure.map_apply measurable_snd hB,
    Measure.map_apply measurable_physicalPairAnchor (measurable_physicalPairTargetPoint hB)]
  have heq : physicalPairTargetPoint ∘ physicalPairAnchor =
      (Prod.snd : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) → (ι → ℝ) × ℝ) := by
    funext e
    change (e.1.1 + (e.2.1 - e.1.1), e.2.2) = e.2
    congr 1
    abel
  change _ = (scene.1 : Measure _) ((physicalPairTargetPoint ∘ physicalPairAnchor) ⁻¹' B)
  rw [heq]

/-- Haar measure absorbs the arbitrary retained full displacement in the
paired mark. No first or second displacement moment is required. -/
theorem measurePreserving_physicalPairPalm_target_shift
    (ν : Measure (PhysicalPairPalmMark ι)) [SFinite ν] :
    MeasurePreserving
      (fun p : (ι → ℝ) × PhysicalPairPalmMark ι ↦ (p.1 + p.2.2, p.2))
      ((volume : Measure (ι → ℝ)).prod ν) ((volume : Measure (ι → ℝ)).prod ν) := by
  have hskew : MeasurePreserving
      (fun p : PhysicalPairPalmMark ι × (ι → ℝ) ↦ (p.1, p.2 + p.1.2))
      (ν.prod (volume : Measure (ι → ℝ))) (ν.prod (volume : Measure (ι → ℝ))) := by
    exact (MeasurePreserving.id ν).skew_product
      (measurable_snd.add measurable_fst.snd)
      (.of_forall (fun m ↦ (measurePreserving_add_right volume m.2).map_eq))
  have hswap₁ : MeasurePreserving Prod.swap
      ((volume : Measure (ι → ℝ)).prod ν) (ν.prod (volume : Measure (ι → ℝ))) :=
    Measure.measurePreserving_swap
  have hswap₂ : MeasurePreserving Prod.swap
      (ν.prod (volume : Measure (ι → ℝ))) ((volume : Measure (ι → ℝ)).prod ν) :=
    Measure.measurePreserving_swap
  have h := hswap₂.comp (hskew.comp hswap₁)
  simpa only [Function.comp_def, Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap] using h

private theorem map_volume_prod_physicalPairSourcePoint
    (ν : Measure (PhysicalPairPalmMark ι)) [SFinite ν] :
    ((volume : Measure (ι → ℝ)).prod ν).map physicalPairSourcePoint =
      (volume : Measure (ι → ℝ)).prod (ν.map (fun m ↦ m.1.1)) := by
  change ((volume : Measure (ι → ℝ)).prod ν).map (fun p ↦ (p.1, p.2.1.1)) = _
  simpa only [Measure.map_id, Prod.map_def, id_eq, physicalPairSourcePoint] using
    (Measure.map_prod_map (volume : Measure (ι → ℝ)) ν measurable_id measurable_fst.fst).symm

private theorem map_volume_prod_physicalPairTargetPoint
    (ν : Measure (PhysicalPairPalmMark ι)) [SFinite ν] :
    ((volume : Measure (ι → ℝ)).prod ν).map physicalPairTargetPoint =
      (volume : Measure (ι → ℝ)).prod (ν.map (fun m ↦ m.1.2)) := by
  let shift : (ι → ℝ) × PhysicalPairPalmMark ι → (ι → ℝ) × PhysicalPairPalmMark ι :=
    fun p ↦ (p.1 + p.2.2, p.2)
  let clock : (ι → ℝ) × PhysicalPairPalmMark ι → (ι → ℝ) × ℝ :=
    fun p ↦ (p.1, p.2.1.2)
  have hshift := measurePreserving_physicalPairPalm_target_shift ν
  have hclock : Measurable clock := measurable_fst.prodMk measurable_snd.fst.snd
  calc
    _ = (((volume : Measure (ι → ℝ)).prod ν).map shift).map clock := by
      rw [Measure.map_map hclock hshift.measurable]
      rfl
    _ = ((volume : Measure (ι → ℝ)).prod ν).map clock := by rw [hshift.map_eq]
    _ = _ := by
      simpa only [Measure.map_id, Prod.map_def, id_eq, clock] using
        (Measure.map_prod_map (volume : Measure (ι → ℝ)) ν
          measurable_id measurable_fst.snd).symm

/-- Actual source and target intensities factor through the corresponding
original clock marginals of the constructed paired-edge Palm measure. -/
theorem physicalScene_intensities_eq_volume_prod_cubePalm_clock_marginals
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P)
    (hunit : (∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂P) < ∞) :
    physicalSceneSourceIntensity P = (volume : Measure (ι → ℝ)).prod
      ((cubePalm ι (physicalScenePairCampbell P)).map (fun m ↦ m.1.1)) ∧
    physicalSceneTargetIntensity P = (volume : Measure (ι → ℝ)).prod
      ((cubePalm ι (physicalScenePairCampbell P)).map (fun m ↦ m.1.2)) := by
  have hfinite : IsFiniteMeasure (cubePalm ι (physicalScenePairCampbell P)) := by
    constructor
    rwa [cubePalm_apply ι _ MeasurableSet.univ, physicalScenePairCampbell_unitCube]
  have hcamp := physicalScenePairCampbell_eq_volume_prod_cubePalm P hstat hunit
  constructor
  · rw [physicalSceneSourceIntensity_eq_map_pairCampbell]
    conv_lhs => rw [hcamp]
    exact map_volume_prod_physicalPairSourcePoint (cubePalm ι (physicalScenePairCampbell P))
  · rw [physicalSceneTargetIntensity_eq_map_pairCampbell]
    conv_lhs => rw [hcamp]
    exact map_volume_prod_physicalPairTargetPoint (cubePalm ι (physicalScenePairCampbell P))

private theorem eq_of_volume_prod_eq
    (α β : Measure ℝ) [SFinite α] [SFinite β]
    (h : (volume : Measure (ι → ℝ)).prod α = (volume : Measure (ι → ℝ)).prod β) : α = β := by
  ext B hB
  have heq := congrArg (fun μ : Measure ((ι → ℝ) × ℝ) ↦ μ (palmUnitCube ι ×ˢ B)) h
  simpa only [Measure.prod_prod, volume_palmUnitCube, one_mul] using heq

/-- The actual prescribed source and target intensities determine the exact
two original scalar-clock marginals of the constructed full-displacement Palm.
The Campbell/Palm identity is produced internally from actual stationarity. -/
theorem cubePalm_physicalScenePairCampbell_clock_marginals
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P)
    (hunit : (∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂P) < ∞)
    (α β : Measure ℝ) [SFinite α] [SFinite β]
    (hsource : physicalSceneSourceIntensity P = (volume : Measure (ι → ℝ)).prod α)
    (htarget : physicalSceneTargetIntensity P = (volume : Measure (ι → ℝ)).prod β) :
    (cubePalm ι (physicalScenePairCampbell P)).map (fun m ↦ m.1.1) = α ∧
    (cubePalm ι (physicalScenePairCampbell P)).map (fun m ↦ m.1.2) = β := by
  have hfinite : IsFiniteMeasure (cubePalm ι (physicalScenePairCampbell P)) := by
    constructor
    rwa [cubePalm_apply ι _ MeasurableSet.univ, physicalScenePairCampbell_unitCube]
  obtain ⟨hs, ht⟩ :=
    physicalScene_intensities_eq_volume_prod_cubePalm_clock_marginals P hstat hunit
  exact ⟨eq_of_volume_prod_eq _ _ (hs.symm.trans hsource),
    eq_of_volume_prod_eq _ _ (ht.symm.trans htarget)⟩

/-- Prescribed actual probability intensities supply the finite moment and
normalize the actual paired-edge Palm internally, together with both exact
original scalar-clock marginals. -/
theorem probability_cubePalm_physicalScenePairCampbell_clock_marginals
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hsource : physicalSceneSourceIntensity P = (volume : Measure (ι → ℝ)).prod α)
    (htarget : physicalSceneTargetIntensity P = (volume : Measure (ι → ℝ)).prod β) :
    IsProbabilityMeasure (cubePalm ι (physicalScenePairCampbell P)) ∧
    (cubePalm ι (physicalScenePairCampbell P)).map (fun m ↦ m.1.1) = α ∧
    (cubePalm ι (physicalScenePairCampbell P)).map (fun m ↦ m.1.2) = β := by
  have hunit : (∫⁻ scene,
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι} ∂P) < ∞ := by
    rw [← physicalSceneSourceIntensity_unitCube, hsource, Measure.prod_prod,
      volume_palmUnitCube, measure_univ, mul_one]
    exact ENNReal.one_lt_top
  exact ⟨isProbabilityMeasure_cubePalm_physicalScenePairCampbell P α hsource,
    cubePalm_physicalScenePairCampbell_clock_marginals P hstat hunit α β hsource htarget⟩

end OTSelector.Reconstruction
