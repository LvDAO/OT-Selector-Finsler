import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedEnergy

/-! Genuine target-window Haar averages of the same original paired-mark energy. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local instance markedStationaryValuePalmRootedTargetEnergyLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

omit [Fintype ι] in
/-- An actual rooted target-window energy is exactly the original physical
plan's weighted target readout. No new endpoint law or energy is substituted. -/
theorem setLIntegral_physicalSceneRootedPlan_target_energy
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U},
      f (physicalPairAnchor e).2 ∂physicalSceneRootedPlan Γ coord u N z) =
      ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.2)
        (fun p ↦ f ((u p.1, u p.2), coord p.2 - coord p.1)) U z := by
  have hW : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U} :=
    hU.preimage measurable_snd.fst
  have hF : Measurable (fun e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦
      f (physicalPairAnchor e).2) := hf.comp (measurable_physicalPairAnchor.snd)
  rw [← lintegral_indicator hW, physicalSceneRootedPlan, lintegral_smul_measure,
    lintegral_map (hF.indicator hW) (measurable_physicalSceneRootedObservation coord hcoord u hu z)]
  congr 1
  apply lintegral_congr
  intro p
  change ({e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U}.indicator
    (fun e ↦ f (physicalPairAnchor e).2) (physicalSceneRootedObservation coord u z p)) =
      U.indicator (fun _ ↦ f ((u p.1, u p.2), coord p.2 - coord p.1)) (coord p.2 - z)
  by_cases hx : coord p.2 - z ∈ U
  · have hp : physicalSceneRootedObservation coord u z p ∈
        {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U} := hx
    rw [indicator_of_mem hp, indicator_of_mem hx, physicalPairAnchor_rootedObservation]
  · have hp : physicalSceneRootedObservation coord u z p ∉
        {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U} := hx
    rw [indicator_of_notMem hp, indicator_of_notMem hx]

/-- Haar averaging converts the original full global paired-mark energy to
the actual rooted target-window energy with the original normalization. -/
theorem lintegral_physicalSceneRootedPlan_targetEnergy_le
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U},
      f (physicalPairAnchor e).2 ∂physicalSceneRootedPlan Γ coord u N z
      ∂cavityRootMeasure volume D N) ≤
      volume U * ∫⁻ p, f ((u p.1, u p.2), coord p.2 - coord p.1) ∂Γ := by
  simp_rw [setLIntegral_physicalSceneRootedPlan_target_energy Γ coord hcoord u hu N _ hf U hU]
  exact lintegral_cavityRoot_scaled_window_le volume Γ _ (hcoord.comp measurable_snd)
    _ (hf.comp (((hu.comp measurable_fst).prodMk (hu.comp measurable_snd)).prodMk
      ((hcoord.comp measurable_snd).sub (hcoord.comp measurable_fst)))) U hU D N hN

/-- A target-window energy is a measurable readout of the same original scene. -/
theorem measurable_physicalScene_targetWindow_energy
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) :
    Measurable (fun scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U},
        f (physicalPairAnchor e).2 ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))) := by
  exact (hf.comp measurable_physicalPairAnchor.snd).lintegral_kernel
    (κ := physicalScenePlanKernel.restrict (hU.preimage measurable_snd.fst))

/-- The actual original environment and root retain the same energy estimate,
including every realized target in the original plan. -/
theorem lintegral_physicalSceneRootedLocalSceneLaw_targetEnergy_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U},
      f (physicalPairAnchor e).2 ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      ∂(physicalSceneRootedLocalSceneLaw P Γplus Γminus hplus hminus coord hcoord u hu N hN D hD :
        Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤
      volume U * ∫⁻ w, ∫⁻ p, f ((u p.1, u p.2), coord p.2 - coord p.1) ∂Γplus w ∂P := by
  rw [lintegral_physicalSceneRootedLocalSceneLaw P Γplus Γminus hplus hminus
    coord hcoord u hu N hN D hD _ (measurable_physicalScene_targetWindow_energy hf hU)]
  apply (lintegral_mono (fun w ↦ lintegral_physicalSceneRootedPlan_targetEnergy_le
    (Γplus w) coord hcoord u hu N hN hf D U hU)).trans_eq
  exact lintegral_const_mul _ ((Measure.measurable_lintegral
    (hf.comp (((hu.comp measurable_fst).prodMk (hu.comp measurable_snd)).prodMk
      ((hcoord.comp measurable_snd).sub (hcoord.comp measurable_fst))))).comp hplus)


end OTSelector.Reconstruction
