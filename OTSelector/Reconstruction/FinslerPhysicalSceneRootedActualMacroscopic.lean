import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopic
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutIterated

/-!
# Same original allocation laws with their actual macroscopic root

The original feasible global allocations retain their realized restricted
columns while their actual macroscopic seed root is recorded. Exact projection
recovers the existing actual countable law; compact macroscopic roots and
original total source mass produce uniform joint tightness.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance actualMacroscopicPhysicalSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance actualMacroscopicPhysicalSceneConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance actualMacroscopicPhysicalSceneConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance actualMacroscopicPhysicalSceneConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance actualMacroscopicPhysicalScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- The actual original global allocation scene with its original macro root. -/
def actualAllocationRootedMacroscopicSceneLaw {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)) :=
  physicalSceneRootedMacroscopicSceneLaw base Penv
    (physicalSceneGlobalAllocationFamily μ aplus Y)
    (physicalSceneGlobalAllocationFamily μ aminus Y)
    (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY)
    (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY)
    H hH coord hcoord u hu scale Y hY D hD

/-- Dropping only the actual macro tag recovers the exact original allocation
scene, including the same actual random restricted target columns. -/
theorem map_actualAllocationRootedMacroscopicSceneLaw_scene {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure.map
      (actualAllocationRootedMacroscopicSceneLaw base Penv μ aplus aminus hplus hminus Y hY
        H hH coord hcoord u hu scale D hD) (f := Prod.snd) measurable_snd.aemeasurable =
      actualAllocationRootedCountableSceneLaw base Penv μ aplus aminus hplus hminus Y hY
        H hH coord hcoord u hu D hD :=
  map_physicalSceneRootedMacroscopicSceneLaw_scene base Penv _ _ _ _
    H hH coord hcoord u hu scale Y hY D hD

/-- Original global feasibility supplies the total-mass bound required for
joint tightness with a compact original macroscopic root carrier. -/
theorem isTightMeasureSet_actualAllocationRootedMacroscopicSceneLaw
    {I : Type*} {Ωn : I → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : I → ℕ) (Penv : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (Penv k)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ k, Ωn k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ωn k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ωn k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (p : ∀ k, Ωn k → Fin (m k + 1) → ℝ)
    (hfp : ∀ k, ∀ᵐ w ∂Penv k, IsSemidiscreteAllocation μ (p k w) (aplus k w))
    (hfm : ∀ k, ∀ᵐ w ∂Penv k, IsSemidiscreteAllocation μ (p k w) (aminus k w))
    (H : I → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u) (scale : I → ℝ)
    (D : I → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ k z, z ∈ D k → physicalSceneMacroscopicRoot (scale k) z ∈ K) :
    IsTightMeasureSet (range (fun k ↦
      (actualAllocationRootedMacroscopicSceneLaw base (Penv k) μ
        (aplus k) (aminus k) (hplus k) (hminus k) (Y k) (hY k)
        (H k) (hH k) (coord k) (hcoord k) u hu (scale k) (D k) (hD k) : Measure ((ι → ℝ) ×
          (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))))) :=
  isTightMeasureSet_physicalSceneRootedMacroscopicSceneLaw base m Penv
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (aplus k) (Y k))
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (aminus k) (Y k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aplus k) (hplus k) (Y k) (hY k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aminus k) (hminus k) (Y k) (hY k))
    H hH coord hcoord u hu scale Y hY D hD K hK hDK (μ univ) (measure_ne_top μ univ)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (Penv k) μ
      (aplus k) (Y k) (p k) (hfp k)).le)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (Penv k) μ
      (aminus k) (Y k) (p k) (hfm k)).le)

/-- The macro tag and both physical plans have exactly their original joint
experiment law after forgetting only the integer carrier. -/
theorem coe_map_actualAllocationRootedMacroscopicSceneLaw_pair {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ((actualAllocationRootedMacroscopicSceneLaw base Penv μ aplus aminus hplus hminus Y hY
        H hH coord hcoord u hu scale D hD).map
      (f := fun s ↦ (s.1, s.2.1))
      (measurable_fst.prodMk measurable_snd.fst).aemeasurable :
      Measure ((ι → ℝ) × CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) =
      (Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
        (fun v ↦ (physicalSceneMacroscopicRoot scale v.2,
          physicalSceneRootedLocalScene
            (fun w ↦ (physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ))
            (fun w ↦ (physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ))
            coord u ((n : ℝ) + 1) v)) := by
  change ((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMacroscopicObservation base
      (fun w ↦ (physicalSceneGlobalAllocationFamily μ aplus Y w).restrict (H ×ˢ univ))
      (fun w ↦ (physicalSceneGlobalAllocationFamily μ aminus Y w).restrict (H ×ˢ univ))
      coord u ((n : ℝ) + 1) scale Y)).map (fun s ↦ (s.1, s.2.1)) = _
  rw [Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
    (measurable_physicalSceneRootedMacroscopicObservation base _ _
      (measurable_physicalPlan_sourceRestriction _
        (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY) H hH)
      (measurable_physicalPlan_sourceRestriction _
        (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY) H hH)
      coord hcoord u hu ((n : ℝ) + 1) scale Y hY)]
  rfl

end OTSelector.Reconstruction
