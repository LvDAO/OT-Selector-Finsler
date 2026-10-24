import OTSelector.Reconstruction.MarkedStationaryValuePalmUnitMoment
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootAllocationScale
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceMass

/-!
# Actual original allocation limits produce their conditional pair Palm measures

Original allocation feasibility bounds the complete source-window mass before
any limit. Compact source bumps preserve this bound through weak convergence.
The actual macroscopic-root conditional kernels therefore have finite unit
moments. Their stationarity and Campbell/Palm factorization are then derived
from the same original Haar-rooted allocation experiment.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
variable (base : (ι → ℝ) × ℝ)
local instance markedStationaryValuePalmAllocationStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance markedStationaryValuePalmAllocationConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance markedStationaryValuePalmAllocationConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance markedStationaryValuePalmAllocationConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance markedStationaryValuePalmAllocationPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValuePalmAllocationPlanNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩

/-- The original macro-tagged experiment has the same full source-window bound
as its exact original countable-scene projection. -/
theorem lintegral_actualAllocationRootedMacroscopicScene_sourceWindow_le
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aplus w))
    (hfm : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (aminus w))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    {U : Set (ι → ℝ)} (hU : IsOpen U) :
    (∫⁻ s : (ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base),
      (s.2.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.1.1 ∈ U}
      ∂(actualAllocationRootedMacroscopicSceneLaw base P μ aplus aminus hplus hminus
        Y hY H hH coord hcoord u hu scale D hD : Measure ((ι → ℝ) ×
          (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))) ≤
        volume U * μ univ := by
  have hb := (lintegral_actualAllocationRootedCountableScene_sourceWindow_le base P μ
    aplus aminus hplus hminus Y hY p hfp hfm H hH coord hcoord u hu D hD hU).1
  have heq := map_actualAllocationRootedMacroscopicSceneLaw_scene base P μ aplus aminus
    hplus hminus Y hY H hH coord hcoord u hu scale D hD
  have hread : Measurable (fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ×
      LocalConfiguration base ↦ (s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ U}) :=
    (Measure.measurable_coe (hU.measurableSet.preimage measurable_fst.fst)).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  rw [← heq, ProbabilityMeasure.toMeasure_map, lintegral_map hread measurable_snd] at hb
  exact hb

section Limits
variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
variable (m : ℕ → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
variable (μ : Measure M) [IsFiniteMeasure μ]
variable (aplus aminus : ∀ k, Ω k → M → Fin (m k + 1) → ℝ)
variable (hplus : ∀ k j, Measurable (fun z : Ω k × M ↦ aplus k z.1 z.2 j))
variable (hminus : ∀ k j, Measurable (fun z : Ω k × M ↦ aminus k z.1 z.2 j))
variable (Y : ∀ k, Ω k → Fin (m k + 1) → M)
variable (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
variable (p : ∀ k, Ω k → Fin (m k + 1) → ℝ)
variable (hfp : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aplus k w))
variable (hfm : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aminus k w))
variable (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
variable (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
variable (u : M → ℝ) (hu : Measurable u)
variable (scale : ℕ → ℝ) (D : ℕ → Set (ι → ℝ))
variable (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
variable {ν : ProbabilityMeasure ((ι → ℝ) ×
    (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))}
variable (hlim : Tendsto (fun k ↦ actualAllocationRootedMacroscopicSceneLaw base (P k) μ
    (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
    (H k) (hH k) (coord k) (hcoord k) u hu (scale k) (D k) (hD k)) atTop (𝓝 ν))

include hlim p hfp hfm in
/-- Actual original feasibility supplies a finite unit-source moment of the
actual weak limit; no moment hypothesis is imposed on that limit. -/
theorem lintegral_actualAllocationRootedMacroscopicScene_limit_unitMass_lt_top :
    (∫⁻ s : (ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base),
      (s.2.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι} ∂(ν : Measure ((ι → ℝ) ×
          (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))) < ∞ := by
  let cloud (k : ℕ) := (actualAllocationRootedMacroscopicSceneLaw base (P k) μ
    (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
    (H k) (hH k) (coord k) (hcoord k) u hu (scale k) (D k) (hD k)).map
      (f := fun s ↦ s.2.1) measurable_snd.fst.aemeasurable
  let Q := ν.map (f := fun s ↦ s.2.1) measurable_snd.fst.aemeasurable
  have hweak : Tendsto cloud atTop (𝓝 Q) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_snd.fst
  let U : Set (ι → ℝ) := Metric.ball 0 2
  have hU : IsOpen U := Metric.isOpen_ball
  have hsub : palmUnitCube ι ⊆ U := by
    intro x hx
    have hnorm : ‖x‖ ≤ (1 : ℝ) := by
      apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1)).mpr
      intro i
      exact abs_le.mpr ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (hx.1 i), hx.2 i⟩
    simpa only [U, Metric.mem_ball, dist_zero_right] using hnorm.trans_lt (by norm_num : (1 : ℝ) < 2)
  have hbound (k : ℕ) : (∫⁻ scene,
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.1.1 ∈ U}
      ∂(cloud k : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ volume U * μ univ := by
    have hb := lintegral_actualAllocationRootedMacroscopicScene_sourceWindow_le base
      (P k) μ (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k) (p k)
      (hfp k) (hfm k) (H k) (hH k) (coord k) (hcoord k) u hu (scale k) (D k) (hD k) hU
    have hread : Measurable (fun scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.1.1 ∈ U}) :=
      (Measure.measurable_coe (hU.measurableSet.preimage measurable_fst.fst)).comp
        (measurable_localFiniteMeasure_coe.comp measurable_fst)
    change (∫⁻ scene, _ ∂((actualAllocationRootedMacroscopicSceneLaw base (P k) μ
      (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
      (H k) (hH k) (coord k) (hcoord k) u hu (scale k) (D k) (hD k)).map
        measurable_snd.fst.aemeasurable : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ _
    rw [ProbabilityMeasure.toMeasure_map, lintegral_map hread measurable_snd.fst]
    exact hb
  have hb := lintegral_sourceUnitMass_le_of_weak_sourceWindow_bound cloud hweak hU hsub
    (volume U * μ univ) hbound
  have hfinite : volume U * μ univ < ∞ :=
    ENNReal.mul_lt_top ((measure_mono Metric.ball_subset_closedBall).trans_lt
      ((isCompact_closedBall (0 : ι → ℝ) 2).measure_lt_top)) (measure_lt_top μ univ)
  have h := hb.trans_lt hfinite
  simpa only [Q, ProbabilityMeasure.toMeasure_map, lintegral_map
    measurable_physicalScene_sourceUnitMass measurable_snd.fst] using h

end Limits

/-- The actual original allocation experiment produces conditionally stationary
qdim Palm factorization with its unit moment, without either as a supplied
limit hypothesis. The original macro root is retained throughout. -/
theorem ae_conditional_actualAllocation_Palm_of_massCube_tendsto
    (hq : 0 < Fintype.card ι)
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (hm : Tendsto (fun k ↦ (m k : ℝ) + 1) atTop atTop)
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ k, Ω k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ω k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ω k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (p : ∀ k, Ω k → Fin (m k + 1) → ℝ)
    (hfp : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aplus k w))
    (hfm : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aminus k w))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    {ν : ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))}
    (hlim : Tendsto (fun k ↦ actualAllocationRootedMacroscopicSceneLaw base (P k) μ
      (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
      (H k) (hH k) (coord k) (hcoord k) u hu
      (((m k : ℝ) + 1) ^ (1 / (Fintype.card ι : ℝ)))
      (haarRootCube ι (haarRootRadius (Fintype.card ι) ((m k : ℝ) + 1)))
      (volume_haarRootCube_radius ι hq (by positivity))) atTop (𝓝 ν)) :
    let νpair := ν.map (f := fun s ↦ (s.1, s.2.1))
      (measurable_fst.prodMk measurable_snd.fst).aemeasurable
    ∀ᵐ w ∂(νpair : Measure ((ι → ℝ) ×
        CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).fst,
      (∀ v : ι → ℝ, MeasurePreserving (physicalSceneReroot v)
        ((νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w)
        ((νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w)) ∧
      (∫⁻ scene, (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι} ∂((νpair : Measure ((ι → ℝ) ×
          CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w)) < ∞ ∧
      physicalScenePairCampbell ((νpair : Measure ((ι → ℝ) ×
          CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w) =
        (volume : Measure (ι → ℝ)).prod (cubePalm ι
          (physicalScenePairCampbell ((νpair : Measure ((ι → ℝ) ×
            CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))).condKernel w))) := by
  let νpair := ν.map (f := fun s ↦ (s.1, s.2.1))
    (measurable_fst.prodMk measurable_snd.fst).aemeasurable
  have hstat := ae_conditional_actualAllocationReroot_of_massCube_tendsto base hq
    m P hm μ aplus aminus hplus hminus Y hY H hH coord hcoord u hu hlim
  have hmoment := lintegral_actualAllocationRootedMacroscopicScene_limit_unitMass_lt_top
    base m P μ aplus aminus hplus hminus Y hY p hfp hfm H hH coord hcoord u hu
    (fun k ↦ ((m k : ℝ) + 1) ^ (1 / (Fintype.card ι : ℝ)))
    (fun k ↦ haarRootCube ι (haarRootRadius (Fintype.card ι) ((m k : ℝ) + 1)))
    (fun k ↦ volume_haarRootCube_radius ι hq (by positivity)) hlim
  have hfinite : (∫⁻ s : (ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ),
      (s.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        {e | e.1.1 ∈ palmUnitCube ι} ∂(νpair : Measure ((ι → ℝ) ×
          CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) < ∞ := by
    have hread : Measurable (fun s : (ι → ℝ) ×
        CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
        (s.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          {e | e.1.1 ∈ palmUnitCube ι}) :=
      measurable_physicalScene_sourceUnitMass.comp measurable_snd
    simpa only [νpair, ProbabilityMeasure.toMeasure_map,
      lintegral_map hread (measurable_fst.prodMk measurable_snd.fst)] using hmoment
  filter_upwards [hstat, ae_condKernel_sourceUnitMass_lt_top
    (νpair : Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) hfinite]
    with w hw hm
  exact ⟨hw, hm, physicalScenePairCampbell_eq_volume_prod_cubePalm _ hw hm⟩

end OTSelector.Reconstruction

