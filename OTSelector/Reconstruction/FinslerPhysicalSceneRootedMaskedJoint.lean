import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopic
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessPopulation

/-!
# Jointly retaining the actual full, retained and discarded physical plans

The macro root, both full plans and original integer target cloud remain in the
first projection. Two further plan pairs are restrictions of those SAME global
plans to a measurable retained edge event and its complement. Their actual joint
law is tight from the original total source mass, without a new column law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance maskedJointSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedJointSceneConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance maskedJointSceneConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedJointSceneConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedJointScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)

/-- This joint observation uses the same environment and same root for all
original restrictions, keeping the full original scene as its exact first component. -/
def physicalSceneRootedMaskedMacroscopicObservation {n : ℕ}
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (H : Set M) (E : Set (M × M)) (coord : M → (ι → ℝ)) (u : M → ℝ)
    (N scale : ℝ) (Y : Ω → Fin (n + 1) → M) (v : Ω × (ι → ℝ)) :
    MacroScene × (PairScene × PairScene) :=
  (physicalSceneRootedMacroscopicObservation base
      (fun w ↦ (Γp w).restrict (H ×ˢ univ))
      (fun w ↦ (Γm w).restrict (H ×ˢ univ)) coord u N scale Y v,
    physicalSceneRootedLocalScene
      (fun w ↦ ((Γp w).restrict E).restrict (H ×ˢ univ))
      (fun w ↦ ((Γm w).restrict E).restrict (H ×ˢ univ)) coord u N v,
    physicalSceneRootedLocalScene
      (fun w ↦ ((Γp w).restrict Eᶜ).restrict (H ×ˢ univ))
      (fun w ↦ ((Γm w).restrict Eᶜ).restrict (H ×ˢ univ)) coord u N v)

/-- Each original physical restriction is measurable on the same environment. -/
theorem measurable_physicalSceneRootedMaskedMacroscopicObservation {n : ℕ}
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j)) :
    Measurable (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E coord u N scale Y) := by
  have hr (Γ : Ω → Measure (M × M)) (hΓ : Measurable Γ) (S : Set (M × M))
      (hS : MeasurableSet S) :
      Measurable (fun w ↦ ((Γ w).restrict S).restrict (H ×ˢ univ)) :=
    measurable_physicalPlan_sourceRestriction _
      (measurable_physicalPlan_endpointRestriction Γ hΓ S hS) H hH
  exact (measurable_physicalSceneRootedMacroscopicObservation base _ _
    (measurable_physicalPlan_sourceRestriction Γp hp H hH)
    (measurable_physicalPlan_sourceRestriction Γm hm H hH)
    coord hcoord u hu N scale Y hY).prodMk
    ((measurable_physicalSceneRootedLocalScene _ _ (hr Γp hp E hE) (hr Γm hm E hE)
      coord hcoord u hu N).prodMk
      (measurable_physicalSceneRootedLocalScene _ _ (hr Γp hp Eᶜ hE.compl) (hr Γm hm Eᶜ hE.compl)
        coord hcoord u hu N))

/-- The original probability experiment jointly records the retained and discarded
pieces of its own full physical plans, with no auxiliary coupling. -/
def physicalSceneRootedMaskedMacroscopicSceneLaw {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure (MacroScene × (PairScene × PairScene)) := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  exact ⟨(Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E coord u ((n : ℝ) + 1) scale Y),
    Measure.isProbabilityMeasure_map
      (measurable_physicalSceneRootedMaskedMacroscopicObservation base Γp Γm hp hm
        H hH E hE coord hcoord u hu ((n : ℝ) + 1) scale Y hY).aemeasurable⟩

/-- Forgetting only the auxiliary actual restrictions recovers the SAME full
original macro-tagged scene, including its original integer target cloud. -/
theorem map_physicalSceneRootedMaskedMacroscopicSceneLaw_full {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    (physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
      coord hcoord u hu scale Y hY D hD).map (f := Prod.fst) measurable_fst.aemeasurable =
      physicalSceneRootedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH
        coord hcoord u hu scale Y hY D hD := by
  apply Subtype.ext
  change ((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E coord u ((n : ℝ) + 1) scale Y)).map
      Prod.fst = _
  rw [Measure.map_map measurable_fst
    (measurable_physicalSceneRootedMaskedMacroscopicObservation base Γp Γm hp hm
      H hH E hE coord hcoord u hu ((n : ℝ) + 1) scale Y hY)]
  rfl

/-- Original total source mass controls joint tightness of full, retained and
lost plans on their unchanged original experiment, uniformly in both indices. -/
theorem isTightMeasureSet_physicalSceneRootedMaskedMacroscopicSceneLaw
    {I : Type*} {Ωn : I → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : I → ℕ) (P : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (P k)]
    (Γp Γm : ∀ k, Ωn k → Measure (M × M))
    [∀ k w, IsFiniteMeasure (Γp k w)] [∀ k w, IsFiniteMeasure (Γm k w)]
    (hp : ∀ k, Measurable (Γp k)) (hm : ∀ k, Measurable (Γm k))
    (H : I → Set M) (hH : ∀ k, MeasurableSet (H k))
    (E : I → Set (M × M)) (hE : ∀ k, MeasurableSet (E k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u) (scale : I → ℝ)
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M) (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (D : I → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ k z, z ∈ D k → physicalSceneMacroscopicRoot (scale k) z ∈ K)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hCp : ∀ k, (∫⁻ w, Γp k w univ ∂P k) ≤ C)
    (hCm : ∀ k, (∫⁻ w, Γm k w univ ∂P k) ≤ C) :
    IsTightMeasureSet (range (fun k ↦
      (physicalSceneRootedMaskedMacroscopicSceneLaw base (P k) (Γp k) (Γm k) (hp k) (hm k)
        (H k) (hH k) (E k) (hE k) (coord k) (hcoord k) u hu (scale k) (Y k) (hY k)
        (D k) (hD k) : Measure (MacroScene × (PairScene × PairScene))))) := by
  have hN (k : I) : 0 < (m k : ℝ) + 1 := by positivity
  let ΓpE := fun k w ↦ (Γp k w).restrict (E k)
  let ΓmE := fun k w ↦ (Γm k w).restrict (E k)
  let ΓpL := fun k w ↦ (Γp k w).restrict (E k)ᶜ
  let ΓmL := fun k w ↦ (Γm k w).restrict (E k)ᶜ
  have hΓpE (k : I) : Measurable (ΓpE k) :=
    measurable_physicalPlan_endpointRestriction _ (hp k) _ (hE k)
  have hΓmE (k : I) : Measurable (ΓmE k) :=
    measurable_physicalPlan_endpointRestriction _ (hm k) _ (hE k)
  have hΓpL (k : I) : Measurable (ΓpL k) :=
    measurable_physicalPlan_endpointRestriction _ (hp k) _ (hE k).compl
  have hΓmL (k : I) : Measurable (ΓmL k) :=
    measurable_physicalPlan_endpointRestriction _ (hm k) _ (hE k).compl
  have hpE (k : I) : (∫⁻ w, ΓpE k w univ ∂P k) ≤ C :=
    (lintegral_mono fun _ ↦ Measure.restrict_le_self univ).trans (hCp k)
  have hmE (k : I) : (∫⁻ w, ΓmE k w univ ∂P k) ≤ C :=
    (lintegral_mono fun _ ↦ Measure.restrict_le_self univ).trans (hCm k)
  have hpL (k : I) : (∫⁻ w, ΓpL k w univ ∂P k) ≤ C :=
    (lintegral_mono fun _ ↦ Measure.restrict_le_self univ).trans (hCp k)
  have hmL (k : I) : (∫⁻ w, ΓmL k w univ ∂P k) ≤ C :=
    (lintegral_mono fun _ ↦ Measure.restrict_le_self univ).trans (hCm k)
  have hfull := isTightMeasureSet_physicalSceneRootedMacroscopicSceneLaw base m P Γp Γm hp hm
    H hH coord hcoord u hu scale Y hY D hD K hK hDK C hC hCp hCm
  have hret := isTightMeasureSet_physicalSceneRestrictedRootedLocalSceneLaw P ΓpE ΓmE
    hΓpE hΓmE H hH coord hcoord u hu (fun k ↦ (m k : ℝ) + 1) hN D hD C hC hpE hmE
  have hlost := isTightMeasureSet_physicalSceneRestrictedRootedLocalSceneLaw P ΓpL ΓmL
    hΓpL hΓmL H hH coord hcoord u hu (fun k ↦ (m k : ℝ) + 1) hN D hD C hC hpL hmL
  exact isTightMeasureSet_original_triple_of_marginals
    (fun k ↦ (P k).prod (cavityRootMeasure volume (D k) ((m k : ℝ) + 1)))
    (fun k ↦ physicalSceneRootedMacroscopicObservation base
      (fun w ↦ (Γp k w).restrict (H k ×ˢ univ))
      (fun w ↦ (Γm k w).restrict (H k ×ˢ univ)) (coord k) u ((m k : ℝ) + 1) (scale k) (Y k))
    (fun k ↦ physicalSceneRootedLocalScene
      (fun w ↦ (ΓpE k w).restrict (H k ×ˢ univ))
      (fun w ↦ (ΓmE k w).restrict (H k ×ˢ univ)) (coord k) u ((m k : ℝ) + 1))
    (fun k ↦ physicalSceneRootedLocalScene
      (fun w ↦ (ΓpL k w).restrict (H k ×ˢ univ))
      (fun w ↦ (ΓmL k w).restrict (H k ×ˢ univ)) (coord k) u ((m k : ℝ) + 1))
    (fun k ↦ measurable_physicalSceneRootedMacroscopicObservation base _ _
      (measurable_physicalPlan_sourceRestriction _ (hp k) _ (hH k))
      (measurable_physicalPlan_sourceRestriction _ (hm k) _ (hH k))
      (coord k) (hcoord k) u hu ((m k : ℝ) + 1) (scale k) (Y k) (hY k))
    (fun k ↦ measurable_physicalSceneRootedLocalScene _ _
      (measurable_physicalPlan_sourceRestriction _ (hΓpE k) _ (hH k))
      (measurable_physicalPlan_sourceRestriction _ (hΓmE k) _ (hH k))
      (coord k) (hcoord k) u hu ((m k : ℝ) + 1))
    (fun k ↦ measurable_physicalSceneRootedLocalScene _ _
      (measurable_physicalPlan_sourceRestriction _ (hΓpL k) _ (hH k))
      (measurable_physicalPlan_sourceRestriction _ (hΓmL k) _ (hH k))
      (coord k) (hcoord k) u hu ((m k : ℝ) + 1)) hfull hret hlost

end OTSelector.Reconstruction
