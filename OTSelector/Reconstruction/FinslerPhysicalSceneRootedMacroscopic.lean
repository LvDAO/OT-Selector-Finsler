import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCountable
import OTSelector.Probability.JointLawTightness

/-!
# The actual original macroscopic root retained jointly with the scene

The macroscopic root is the original Haar seed-basis root divided by the
original spatial scale. It does not depend on any auxiliary accuracy core.
The same environment and root retain this tag jointly with both actual plans
and the original integer target carrier.
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
local instance macroscopicPhysicalSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance macroscopicPhysicalSceneConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance macroscopicPhysicalSceneConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance macroscopicPhysicalSceneConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance macroscopicPhysicalScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- The original macroscopic seed-basis root, before any auxiliary core choice. -/
def physicalSceneMacroscopicRoot (scale : ℝ) (root : ι → ℝ) : ι → ℝ :=
  fun i ↦ root i / scale

/-- The retained macroscopic root is continuous in the actual Haar root. -/
theorem continuous_physicalSceneMacroscopicRoot (scale : ℝ) :
    Continuous (physicalSceneMacroscopicRoot (ι := ι) scale) := by
  change Continuous (fun root : ι → ℝ ↦ fun i ↦ root i / scale)
  exact continuous_pi fun i ↦
    (continuous_apply i : Continuous (fun z : ι → ℝ ↦ z i)).div_const scale

/-- A microscopic reroot changes the original macro tag only by its original
inverse-scale displacement. -/
theorem physicalSceneMacroscopicRoot_add (scale : ℝ) (root shift : ι → ℝ) :
    physicalSceneMacroscopicRoot scale (root + shift) =
      physicalSceneMacroscopicRoot scale root + physicalSceneMacroscopicRoot scale shift := by
  ext i
  exact add_div _ _ _

/-- Rescaling a macroscopic root recovers the same original tag exactly. -/
theorem physicalSceneMacroscopicRoot_smul (scale : ℝ) (hscale : scale ≠ 0) (w : ι → ℝ) :
    physicalSceneMacroscopicRoot scale (scale • w) = w := by
  ext i
  simp [physicalSceneMacroscopicRoot, hscale]

/-- The actual tagged observation uses one original environment and root. -/
def physicalSceneRootedMacroscopicObservation {n : ℕ}
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (coord : M → (ι → ℝ)) (u : M → ℝ) (N scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (v : Ω × (ι → ℝ)) :
    (ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base) :=
  (physicalSceneMacroscopicRoot scale v.2,
    physicalSceneRootedCountableObservation base Γplus Γminus coord u N Y v)

/-- Retaining the original macro root preserves actual joint measurability. -/
theorem measurable_physicalSceneRootedMacroscopicObservation {n : ℕ}
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j)) :
    Measurable (physicalSceneRootedMacroscopicObservation base Γplus Γminus coord u N scale Y) :=
  ((continuous_physicalSceneMacroscopicRoot scale).measurable.comp measurable_snd).prodMk
    (measurable_physicalSceneRootedCountableObservation base Γplus Γminus hplus hminus
      coord hcoord u hu N Y hY)

/-- The original normalized Haar root keeps its true macroscopic tag jointly
with both actual source-restricted plans and the same original target carrier. -/
def physicalSceneRootedMacroscopicSceneLaw {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)) := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  exact ⟨(Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMacroscopicObservation base
      (fun w ↦ (Γplus w).restrict (H ×ˢ univ))
      (fun w ↦ (Γminus w).restrict (H ×ˢ univ)) coord u ((n : ℝ) + 1) scale Y),
    Measure.isProbabilityMeasure_map
      (measurable_physicalSceneRootedMacroscopicObservation base _ _
        (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
        (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
        coord hcoord u hu ((n : ℝ) + 1) scale Y hY).aemeasurable⟩

/-- Forgetting only the macro tag gives exactly the same actual countable
physical scene law, with its unchanged random restricted target columns. -/
theorem map_physicalSceneRootedMacroscopicSceneLaw_scene {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure.map
      (physicalSceneRootedMacroscopicSceneLaw base Penv Γplus Γminus hplus hminus H hH
        coord hcoord u hu scale Y hY D hD) (f := Prod.snd) measurable_snd.aemeasurable =
      physicalSceneRootedCountableLocalSceneLaw base Penv Γplus Γminus hplus hminus H hH
        coord hcoord u hu Y hY D hD := by
  apply Subtype.ext
  change ((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMacroscopicObservation base
      (fun w ↦ (Γplus w).restrict (H ×ˢ univ))
      (fun w ↦ (Γminus w).restrict (H ×ˢ univ)) coord u ((n : ℝ) + 1) scale Y)).map Prod.snd = _
  rw [Measure.map_map measurable_snd
    (measurable_physicalSceneRootedMacroscopicObservation base _ _
      (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
      (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
      coord hcoord u hu ((n : ℝ) + 1) scale Y hY)]
  rfl

/-- Actual root containment produces compact macro-tag carrying. No
auxiliary root-cell index or replacement root law is introduced. -/
theorem ae_cavityRootMeasure_macroscopicRoot_mem
    (scale : ℝ) (D K : Set (ι → ℝ)) (N : ℝ) (hK : MeasurableSet K)
    (hDK : ∀ z ∈ D, physicalSceneMacroscopicRoot scale z ∈ K) :
    ∀ᵐ z ∂cavityRootMeasure volume D N, physicalSceneMacroscopicRoot scale z ∈ K := by
  rw [ae_iff]
  have hm : MeasurableSet {z : ι → ℝ | ¬physicalSceneMacroscopicRoot scale z ∈ K} :=
    (hK.preimage (continuous_physicalSceneMacroscopicRoot scale).measurable).compl
  have hz : {z : ι → ℝ | ¬physicalSceneMacroscopicRoot scale z ∈ K} ∩ D = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun hz hD ↦ hz (hDK z hD)
  simp only [cavityRootMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hm, hz, measure_empty, mul_zero]

/-- The actual tagged law is carried by the original macroscopic root set. -/
theorem ae_physicalSceneRootedMacroscopicSceneLaw_macro_mem {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : MeasurableSet K)
    (hDK : ∀ z ∈ D, physicalSceneMacroscopicRoot scale z ∈ K) :
    ∀ᵐ s ∂(physicalSceneRootedMacroscopicSceneLaw base Penv Γplus Γminus hplus hminus H hH
      coord hcoord u hu scale Y hY D hD :
        Measure ((ι → ℝ) ×
          (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))), s.1 ∈ K := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  apply (ae_map_iff
    (measurable_physicalSceneRootedMacroscopicObservation base _ _
      (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
      (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
      coord hcoord u hu ((n : ℝ) + 1) scale Y hY).aemeasurable
    (hK.preimage measurable_fst)).mpr
  apply ae_of_ae_map (p := fun z ↦ physicalSceneMacroscopicRoot scale z ∈ K)
    measurable_snd.aemeasurable
  simpa only [Measure.map_snd_prod, measure_univ, one_smul] using
    ae_cavityRootMeasure_macroscopicRoot_mem scale D K ((n : ℝ) + 1) hK hDK

/-- Compact original macro roots and the actual finite-plan mass bound make
one tight joint tagged scene family, retaining every original correlation. -/
theorem isTightMeasureSet_physicalSceneRootedMacroscopicSceneLaw
    {I : Type*} {Ωn : I → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : I → ℕ) (Penv : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (Penv k)]
    (Γplus Γminus : ∀ k, Ωn k → Measure (M × M))
    [∀ k w, IsFiniteMeasure (Γplus k w)] [∀ k w, IsFiniteMeasure (Γminus k w)]
    (hplus : ∀ k, Measurable (Γplus k)) (hminus : ∀ k, Measurable (Γminus k))
    (H : I → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u) (scale : I → ℝ)
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (D : I → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ k z, z ∈ D k → physicalSceneMacroscopicRoot (scale k) z ∈ K)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hmassplus : ∀ k, (∫⁻ w, Γplus k w univ ∂Penv k) ≤ C)
    (hmassminus : ∀ k, (∫⁻ w, Γminus k w univ ∂Penv k) ≤ C) :
    IsTightMeasureSet (range (fun k ↦
      (physicalSceneRootedMacroscopicSceneLaw base (Penv k) (Γplus k) (Γminus k)
        (hplus k) (hminus k) (H k) (hH k) (coord k) (hcoord k) u hu (scale k)
        (Y k) (hY k) (D k) (hD k) : Measure ((ι → ℝ) ×
          (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))))) := by
  let P := fun k ↦ (Penv k).prod (cavityRootMeasure volume (D k) ((m k : ℝ) + 1))
  let tag := fun k (v : Ωn k × (ι → ℝ)) ↦ physicalSceneMacroscopicRoot (scale k) v.2
  have htag (k : I) : Measurable (tag k) :=
    (continuous_physicalSceneMacroscopicRoot (scale k)).measurable.comp measurable_snd
  have htagK (k : I) : ∀ᵐ v ∂P k, tag k v ∈ K := by
    have hrootN : 0 < (m k : ℝ) + 1 := by positivity
    have := isProbabilityMeasure_cavityRootMeasure volume (D k) ((m k : ℝ) + 1) hrootN (hD k)
    apply ae_of_ae_map (p := fun z ↦ physicalSceneMacroscopicRoot (scale k) z ∈ K)
      measurable_snd.aemeasurable
    simpa only [P, Measure.map_snd_prod, measure_univ, one_smul] using
      ae_cavityRootMeasure_macroscopicRoot_mem (scale k) (D k) K
        ((m k : ℝ) + 1) hK.measurableSet (hDK k)
  have htagTight : IsTightMeasureSet (range (fun k ↦ (P k).map (tag k))) := by
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro ε _hε
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨k, rfl⟩
    rw [Measure.map_apply (htag k) hK.measurableSet.compl]
    change (P k) {v | ¬tag k v ∈ K} ≤ ε
    rw [ae_iff.mp (htagK k)]
    exact zero_le
  exact isTightMeasureSet_original_joint_of_marginals P tag
    (fun k ↦ physicalSceneRootedCountableObservation base
      (fun w ↦ (Γplus k w).restrict (H k ×ˢ univ))
      (fun w ↦ (Γminus k w).restrict (H k ×ˢ univ)) (coord k) u ((m k : ℝ) + 1) (Y k))
    htag (fun k ↦ measurable_physicalSceneRootedCountableObservation base _ _
      (measurable_physicalPlan_sourceRestriction (Γplus k) (hplus k) (H k) (hH k))
      (measurable_physicalPlan_sourceRestriction (Γminus k) (hminus k) (H k) (hH k))
      (coord k) (hcoord k) u hu ((m k : ℝ) + 1) (Y k) (hY k)) htagTight
    (isTightMeasureSet_physicalSceneRootedCountableLocalSceneLaw base m Penv Γplus Γminus
      hplus hminus H hH coord hcoord u hu Y hY D hD C hC hmassplus hmassminus)

end OTSelector.Reconstruction
