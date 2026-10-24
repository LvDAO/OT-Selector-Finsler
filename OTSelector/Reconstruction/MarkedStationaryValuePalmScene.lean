import OTSelector.Reconstruction.MarkedStationaryValuePalmCube
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootPhysicalScene

/-!
# Actual multidimensional pair Campbell/Palm measures of physical plan scenes

The original first plan of the scene is read as its actual S-finite measure.
Anchoring each edge at its original source records both original clocks and its
full transverse displacement. Spatial covariance is proved from the actual
physical reroot; Campbell factorization is then derived, not a carrier field.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]
local instance markedStationaryValuePalmSceneLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Original source and target clocks together with the full transverse
physical displacement of the same original edge. -/
abbrev PhysicalPairPalmMark (ι : Type*) := (ℝ × ℝ) × (ι → ℝ)

/-- Anchor the actual edge at its source without altering its original clocks
or replacing its transverse displacement by a scalar. -/
def physicalPairAnchor
    (e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) : (ι → ℝ) × PhysicalPairPalmMark ι :=
  (e.1.1, ((e.1.2, e.2.2), e.2.1 - e.1.1))

omit [Fintype ι] in
theorem measurable_physicalPairAnchor : Measurable (physicalPairAnchor (ι := ι)) :=
  measurable_fst.fst.prodMk
    ((measurable_fst.snd.prodMk measurable_snd.snd).prodMk
      (measurable_snd.fst.sub measurable_fst.fst))

/-- The actual first physical plan yields a canonical measurable S-finite
edge-location/paired-mark kernel. -/
def physicalScenePairKernel :
    Kernel (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))
      ((ι → ℝ) × PhysicalPairPalmMark ι) :=
  (localFiniteMeasureKernel.comap Prod.fst measurable_fst).map physicalPairAnchor

instance physicalScenePairKernelIsSFinite : IsSFiniteKernel (physicalScenePairKernel (ι := ι)) := by
  unfold physicalScenePairKernel
  infer_instance

/-- The constructed kernel is literally the same actual plan's pushforward. -/
theorem physicalScenePairKernel_apply
    (scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :
    physicalScenePairKernel scene = (scene.1 : Measure _).map physicalPairAnchor := by
  exact Kernel.map_apply _ measurable_physicalPairAnchor scene

/-- The actual pair Campbell measure of the original scene law. -/
def physicalScenePairCampbell
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure ((ι → ℝ) × PhysicalPairPalmMark ι) := P.bind physicalScenePairKernel

/-- Actual physical rerooting translates the source position and preserves
both original clocks and the entire displacement vector exactly. -/
theorem physicalScenePairKernel_reroot (v : ι → ℝ)
    (scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :
    physicalScenePairKernel (physicalSceneReroot v scene) =
      (physicalScenePairKernel scene).map
        (fun p : (ι → ℝ) × PhysicalPairPalmMark ι ↦ (p.1 - v, p.2)) := by
  rw [physicalScenePairKernel_apply, physicalScenePairKernel_apply]
  change ((scene.1 : Measure _).map (physicalSceneEdgeReroot v)).map physicalPairAnchor = _
  have hshift : Measurable (fun p : (ι → ℝ) × PhysicalPairPalmMark ι ↦ (p.1 - v, p.2)) :=
    (measurable_fst.sub measurable_const).prodMk measurable_snd
  rw [Measure.map_map measurable_physicalPairAnchor (physicalSceneEdgeReroot v).continuous.measurable,
    Measure.map_map hshift measurable_physicalPairAnchor]
  congr 1
  funext e
  change (e.1.1 - v, ((e.1.2, e.2.2), (e.2.1 - v) - (e.1.1 - v))) =
    (e.1.1 - v, ((e.1.2, e.2.2), e.2.1 - e.1.1))
  rw [sub_sub_sub_cancel_right]

/-- A stationary actual physical scene supplies spatial invariance of its
constructed multidimensional paired-edge Campbell measure. -/
theorem measurePreserving_physicalScenePairCampbell
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P) (a : ι → ℝ) :
    MeasurePreserving (fun p : (ι → ℝ) × PhysicalPairPalmMark ι ↦ (a + p.1, p.2))
      (physicalScenePairCampbell P) (physicalScenePairCampbell P) := by
  have hloc : Measurable (fun p : (ι → ℝ) × PhysicalPairPalmMark ι ↦ (a + p.1, p.2)) :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  apply measurePreserving_bind_of_covariant P physicalScenePairKernel
    (Kernel.measurable _) (hstat (-a)) hloc
  exact .of_forall (fun scene ↦ by
    simpa only [sub_neg_eq_add, add_comm] using physicalScenePairKernel_reroot (-a) scene)

/-- Its actual unit-cube mass is the original scene's expected source-window
edge mass, including all original target positions. -/
theorem physicalScenePairCampbell_unitCube
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    physicalScenePairCampbell P (palmUnitCube ι ×ˢ univ) =
      ∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι} ∂P := by
  rw [physicalScenePairCampbell, Measure.bind_apply
    ((measurableSet_palmUnitCube ι).prod MeasurableSet.univ) (Kernel.measurable _).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with scene
  rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
    ((measurableSet_palmUnitCube ι).prod MeasurableSet.univ)]
  congr 1
  ext e
  simp only [mem_preimage, physicalPairAnchor, mem_prod, mem_univ, and_true, mem_ofPred_eq]

/-- The actual conditional stationary scene produces its own full-dimensional
paired-edge Campbell/Palm factorization from its original unit-window moment. -/
theorem physicalScenePairCampbell_eq_volume_prod_cubePalm
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v) P P)
    (hunit : (∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.1 ∈ palmUnitCube ι} ∂P) < ∞) :
    physicalScenePairCampbell P = (volume : Measure (ι → ℝ)).prod
      (cubePalm ι (physicalScenePairCampbell P)) := by
  exact campbell_eq_volume_prod_cubePalm ι (physicalScenePairCampbell P)
    (measurePreserving_physicalScenePairCampbell P hstat)
    (by rwa [physicalScenePairCampbell_unitCube])

/-- Every nonnegative weighted kinetic or paired-mark Palm readout is exactly
the original scene's expected source-unit-window readout of the same edges. -/
theorem lintegral_cubePalm_physicalScenePairCampbell
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ m, f m ∂cubePalm ι (physicalScenePairCampbell P)) =
      ∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι},
        f (physicalPairAnchor e).2 ∂(scene.1 : Measure _) ∂P := by
  have hU : MeasurableSet (palmUnitCube ι ×ˢ (univ : Set (PhysicalPairPalmMark ι))) :=
    (measurableSet_palmUnitCube ι).prod MeasurableSet.univ
  have hW : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
      e.1.1 ∈ palmUnitCube ι} := (measurableSet_palmUnitCube ι).preimage measurable_fst.fst
  have hF : Measurable (fun p : (ι → ℝ) × PhysicalPairPalmMark ι ↦ f p.2) := hf.comp measurable_snd
  rw [cubePalm, lintegral_map hf measurable_snd, ← lintegral_indicator hU,
    physicalScenePairCampbell, Measure.lintegral_bind (Kernel.measurable _).aemeasurable
      (hF.indicator hU).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with scene
  rw [physicalScenePairKernel_apply, lintegral_map (hF.indicator hU) measurable_physicalPairAnchor]
  have heq : (fun e ↦ (palmUnitCube ι ×ˢ univ).indicator
      (fun p : (ι → ℝ) × PhysicalPairPalmMark ι ↦ f p.2) (physicalPairAnchor e)) =
      ({e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι}).indicator
        (fun e ↦ f (physicalPairAnchor e).2) := by
    funext e
    by_cases he : e.1.1 ∈ palmUnitCube ι
    · have hleft : physicalPairAnchor e ∈ palmUnitCube ι ×ˢ (univ : Set (PhysicalPairPalmMark ι)) :=
        ⟨he, mem_univ _⟩
      have hright : e ∈ {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι} := he
      rw [indicator_of_mem hleft, indicator_of_mem hright]
    · have hleft : physicalPairAnchor e ∉ palmUnitCube ι ×ˢ (univ : Set (PhysicalPairPalmMark ι)) :=
        fun h ↦ he h.1
      have hright : e ∉ {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ palmUnitCube ι} := he
      rw [indicator_of_notMem hleft, indicator_of_notMem hright]
  rw [heq, lintegral_indicator hW]


/-- The same original first plan supplies its actual source intensity kernel. -/
def physicalSceneSourceKernel :
    Kernel (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) ((ι → ℝ) × ℝ) :=
  (localFiniteMeasureKernel.comap Prod.fst measurable_fst).map Prod.fst

instance physicalSceneSourceKernelIsSFinite : IsSFiniteKernel (physicalSceneSourceKernel (ι := ι)) := by
  unfold physicalSceneSourceKernel
  infer_instance

def physicalSceneSourceIntensity
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure ((ι → ℝ) × ℝ) := P.bind physicalSceneSourceKernel

/-- The true source intensity and the pair Campbell measure have the same
unit spatial mass, with every original clock retained. -/
theorem physicalSceneSourceIntensity_unitCube
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    physicalSceneSourceIntensity P (palmUnitCube ι ×ˢ univ) =
      ∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι} ∂P := by
  rw [physicalSceneSourceIntensity, Measure.bind_apply
    ((measurableSet_palmUnitCube ι).prod MeasurableSet.univ) (Kernel.measurable _).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards with scene
  have hkernel : physicalSceneSourceKernel scene =
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).map
        (Prod.fst : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) → ((ι → ℝ) × ℝ)) :=
    Kernel.map_apply _ measurable_fst scene
  rw [hkernel, Measure.map_apply measurable_fst
    ((measurableSet_palmUnitCube ι).prod MeasurableSet.univ)]
  congr 1
  ext e
  simp only [mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]

/-- The original unit source intensity normalizes the constructed actual
qdim paired-edge Palm measure. No Palm probability is assumed separately. -/
theorem isProbabilityMeasure_cubePalm_physicalScenePairCampbell
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (hsource : physicalSceneSourceIntensity P = (volume : Measure (ι → ℝ)).prod α) :
    IsProbabilityMeasure (cubePalm ι (physicalScenePairCampbell P)) := by
  constructor
  rw [cubePalm_apply ι _ MeasurableSet.univ, physicalScenePairCampbell_unitCube,
    ← physicalSceneSourceIntensity_unitCube, hsource, Measure.prod_prod,
    volume_palmUnitCube, measure_univ, mul_one]

/-- Actual plan-supported clock or displacement properties pass to the
constructed paired-edge Palm measure on the same original scene law. -/
theorem ae_cubePalm_of_physicalScenePlan
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {S : Set (PhysicalPairPalmMark ι)} (hS : MeasurableSet S)
    (hplan : ∀ᵐ scene ∂P, ∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
      (physicalPairAnchor e).2 ∈ S) :
    ∀ᵐ m ∂cubePalm ι (physicalScenePairCampbell P), m ∈ S := by
  have hzero : physicalScenePairCampbell P (univ ×ˢ Sᶜ) = 0 := by
    rw [physicalScenePairCampbell, Measure.bind_apply
      (MeasurableSet.univ.prod hS.compl) (Kernel.measurable _).aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hplan] with scene hscene
    rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor
      (MeasurableSet.univ.prod hS.compl)]
    have hpre : physicalPairAnchor ⁻¹' (univ ×ˢ Sᶜ) =
        {e | ¬ (physicalPairAnchor e).2 ∈ S} := by
      ext e
      simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_compl_iff, mem_ofPred_eq]
    rw [hpre]
    exact ae_iff.mp hscene
  rw [ae_iff]
  change cubePalm ι (physicalScenePairCampbell P) Sᶜ = 0
  rw [cubePalm_apply ι _ hS.compl]
  apply le_antisymm _ bot_le
  exact (measure_mono (prod_mono_left (subset_univ _))).trans hzero.le

/-- Actual forwardness of the original plan yields actual forwardness of its
constructed full-dimensional paired-edge Palm law. -/
theorem ae_cubePalm_physicalScene_forward
    (P : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hforward : ∀ᵐ scene ∂P, ∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
      e.1.2 < e.2.2) :
    ∀ᵐ m ∂cubePalm ι (physicalScenePairCampbell P), m.1.1 < m.1.2 := by
  exact ae_cubePalm_of_physicalScenePlan P
    (measurableSet_lt measurable_fst.fst measurable_fst.snd) hforward

end OTSelector.Reconstruction
