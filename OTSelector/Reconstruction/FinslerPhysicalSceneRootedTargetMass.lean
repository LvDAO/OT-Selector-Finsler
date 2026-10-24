import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCountable
import OTSelector.MeasureTheory.NonproperMarginalLocalFiniteness

/-!
# Actual target-window moments without changing restricted columns

Haar rooting controls target spatial-window mass by the same original finite
physical plan mass. Restricting its source can only lower this bound. Under the
actual joint plan and integer-cloud law, original global feasibility supplies
uniform target-window first moments without a target law or independence premise.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance physicalSceneTargetMarginalStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance physicalSceneTargetMarginalConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance physicalSceneTargetMarginalConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance physicalSceneTargetMarginalConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance physicalSceneTargetMarginalPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

omit base in
theorem physicalSceneRootedPlan_targetWindow_eq_swap_sourceWindow
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) :
    physicalSceneRootedPlan Γ coord u N z {e | e.2.1 ∈ U} =
      physicalSceneRootedPlan (Γ.map Prod.swap) coord u N z {e | e.1.1 ∈ U} := by
  have hobs := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have ht : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U} :=
    hU.preimage measurable_snd.fst
  have hs : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} :=
    hU.preimage measurable_fst.fst
  unfold physicalSceneRootedPlan
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.map_apply hobs ht, Measure.map_apply hobs hs,
    Measure.map_apply measurable_swap (hs.preimage hobs)]
  rfl

omit base in
theorem lintegral_physicalSceneRootedPlan_targetWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, physicalSceneRootedPlan Γ coord u N z {e | e.2.1 ∈ U}
      ∂cavityRootMeasure volume D N) ≤ volume U * Γ univ := by
  simp_rw [physicalSceneRootedPlan_targetWindow_eq_swap_sourceWindow Γ coord hcoord u hu N _ hU]
  simpa only [Measure.map_apply measurable_swap MeasurableSet.univ, preimage_univ] using
    lintegral_physicalSceneRootedPlan_sourceWindow_le (Γ.map Prod.swap)
      coord hcoord u hu N hN D U hU

omit base in
theorem lintegral_restricted_physicalSceneRootedPlan_targetWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ] (H : Set M)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      {e | e.2.1 ∈ U} ∂cavityRootMeasure volume D N) ≤ volume U * Γ univ := by
  exact (lintegral_physicalSceneRootedPlan_targetWindow_le
    (Γ.restrict (H ×ˢ univ)) coord hcoord u hu N hN D U hU).trans
      (mul_le_mul_right (Measure.restrict_le_self univ) _)

omit base in
theorem lintegral_physicalSceneRestrictedRootedScene_targetWindow_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    {U : Set (ι → ℝ)} (hU : IsOpen U) :
    ((∫⁻ s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ), (s.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}
      ∂(physicalSceneRestrictedRootedLocalSceneLaw P Γplus Γminus hplus hminus
        H hH coord hcoord u hu N hN D hD : Measure _)) ≤
        volume U * ∫⁻ w, Γplus w univ ∂P) ∧
    ((∫⁻ s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ), (s.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}
      ∂(physicalSceneRestrictedRootedLocalSceneLaw P Γplus Γminus hplus hminus
        H hH coord hcoord u hu N hN D hD : Measure _)) ≤
        volume U * ∫⁻ w, Γminus w univ ∂P) := by
  have hopen : IsOpen {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U} :=
    hU.preimage (continuous_fst.comp continuous_snd)
  have hread := lintegral_physicalSceneRootedLocalSceneLaw_open P
    (fun w ↦ (Γplus w).restrict (H ×ˢ univ))
    (fun w ↦ (Γminus w).restrict (H ×ˢ univ))
    (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
    (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
    coord hcoord u hu N hN D hD hopen
  constructor
  · rw [show (∫⁻ s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ), (s.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}
        ∂(physicalSceneRestrictedRootedLocalSceneLaw P Γplus Γminus hplus hminus
          H hH coord hcoord u hu N hN D hD : Measure _)) = _ from hread.1]
    exact (lintegral_mono (fun w ↦ lintegral_restricted_physicalSceneRootedPlan_targetWindow_le
      (Γplus w) H coord hcoord u hu N hN D U hU.measurableSet)).trans_eq
        (lintegral_const_mul _ ((Measure.measurable_coe MeasurableSet.univ).comp hplus))
  · rw [show (∫⁻ s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ), (s.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}
        ∂(physicalSceneRestrictedRootedLocalSceneLaw P Γplus Γminus hplus hminus
          H hH coord hcoord u hu N hN D hD : Measure _)) = _ from hread.2]
    exact (lintegral_mono (fun w ↦ lintegral_restricted_physicalSceneRootedPlan_targetWindow_le
      (Γminus w) H coord hcoord u hu N hN D U hU.measurableSet)).trans_eq
        (lintegral_const_mul _ ((Measure.measurable_coe MeasurableSet.univ).comp hminus))

theorem lintegral_actualAllocationRootedCountableScene_targetWindow_le {n : ℕ}
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
    (u : M → ℝ) (hu : Measurable u)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    {U : Set (ι → ℝ)} (hU : IsOpen U) :
    ((∫⁻ s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base, (s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}
      ∂(actualAllocationRootedCountableSceneLaw base P μ aplus aminus hplus hminus
        Y hY H hH coord hcoord u hu D hD : Measure _)) ≤ volume U * μ univ) ∧
    ((∫⁻ s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base, (s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}
      ∂(actualAllocationRootedCountableSceneLaw base P μ aplus aminus hplus hminus
        Y hY H hH coord hcoord u hu D hD : Measure _)) ≤ volume U * μ univ) := by
  let Γp := physicalSceneGlobalAllocationFamily μ aplus Y
  let Γm := physicalSceneGlobalAllocationFamily μ aminus Y
  have hp := measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY
  have hm := measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY
  have hb := lintegral_physicalSceneRestrictedRootedScene_targetWindow_le P Γp Γm hp hm
    H hH coord hcoord u hu ((n : ℝ) + 1) (by positivity) D hD hU
  rw [lintegral_physicalSceneGlobalAllocationFamily_univ P μ aplus Y p hfp,
    lintegral_physicalSceneGlobalAllocationFamily_univ P μ aminus Y p hfm] at hb
  have heq := map_physicalSceneRootedCountableLocalSceneLaw_pair base P Γp Γm hp hm
    H hH coord hcoord u hu Y hY D hD
  have hE : IsOpen {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ U} :=
    hU.preimage (continuous_fst.comp continuous_snd)
  have hmp : Measurable (fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      (s.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}) := ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hE).comp continuous_fst).measurable
  have hmm : Measurable (fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      (s.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.2.1 ∈ U}) := ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hE).comp continuous_snd).measurable
  constructor
  · convert hb.1 using 1
    rw [← heq]
    exact (lintegral_map hmp measurable_fst).symm
  · convert hb.2 using 1
    rw [← heq]
    exact (lintegral_map hmm measurable_fst).symm

end OTSelector.Reconstruction
