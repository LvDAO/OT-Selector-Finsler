import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCounts
import OTSelector.Probability.CavitySemidiscreteConfigurationSupport

/-!
# Actual rooted plans and their original integer target cloud

Both source-restricted physical plans and the same original target array are
observed in one common environment and Haar root. Original feasibility supplies
finite mass and actual target carrying. Their joint laws therefore have a weak
subsequence whose two plans remain supported over the same integer cloud,
without prescribing replacement local column masses or a target marginal law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

open PointProcess PointProcess.LocalConfiguration

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)

local instance : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Both actual physical plans and the same original integer target array. -/
def physicalSceneRootedCountableObservation {n : ℕ}
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (coord : M → (ι → ℝ)) (u : M → ℝ) (N : ℝ)
    (Y : Ω → Fin (n + 1) → M) (v : Ω × (ι → ℝ)) :
    CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base :=
  (physicalSceneRootedLocalScene Γplus Γminus coord u N v,
    cavityRootedTargetConfiguration base (fun w j ↦ (coord (Y w j), u (Y w j))) v)

/-- The original physical observations and labels are jointly measurable. -/
theorem measurable_physicalSceneRootedCountableObservation {n : ℕ}
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j)) :
    Measurable (physicalSceneRootedCountableObservation base Γplus Γminus coord u N Y) :=
  (measurable_physicalSceneRootedLocalScene Γplus Γminus hplus hminus
    coord hcoord u hu N).prodMk
    (measurable_cavityRootedTargetConfiguration base _
      (fun j ↦ (hcoord.comp (hY j)).prodMk (hu.comp (hY j))))

/-- Actual source restriction, two plans and the original integer cloud use one
common original environment and Haar root. -/
def physicalSceneRootedCountableLocalSceneLaw {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base) := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  exact ⟨(P.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedCountableObservation base
      (fun w ↦ (Γplus w).restrict (H ×ˢ univ))
      (fun w ↦ (Γminus w).restrict (H ×ˢ univ)) coord u ((n : ℝ) + 1) Y),
    Measure.isProbabilityMeasure_map
      (measurable_physicalSceneRootedCountableObservation base _ _
        (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
        (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
        coord hcoord u hu ((n : ℝ) + 1) Y hY).aemeasurable⟩

/-- Forgetting integer labels recovers exactly the existing actual pair law. -/
theorem map_physicalSceneRootedCountableLocalSceneLaw_pair {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure.map
      (physicalSceneRootedCountableLocalSceneLaw base P Γplus Γminus hplus hminus
        H hH coord hcoord u hu Y hY D hD)
      (f := Prod.fst) measurable_fst.aemeasurable =
    physicalSceneRestrictedRootedLocalSceneLaw P Γplus Γminus hplus hminus
      H hH coord hcoord u hu ((n : ℝ) + 1) (by positivity) D hD := by
  apply Subtype.ext
  change ((P.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedCountableObservation base
      (fun w ↦ (Γplus w).restrict (H ×ˢ univ))
      (fun w ↦ (Γminus w).restrict (H ×ˢ univ)) coord u ((n : ℝ) + 1) Y)).map
    Prod.fst = _
  rw [Measure.map_map measurable_fst
    (measurable_physicalSceneRootedCountableObservation base _ _
      (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
      (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
      coord hcoord u hu ((n : ℝ) + 1) Y hY)]
  rfl

/-- One tight common law keeps the original plans and original integer labels. -/
theorem isTightMeasureSet_physicalSceneRootedCountableLocalSceneLaw
    {I : Type*} {Ω : I → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : I → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (Γplus Γminus : ∀ k, Ω k → Measure (M × M))
    [∀ k w, IsFiniteMeasure (Γplus k w)] [∀ k w, IsFiniteMeasure (Γminus k w)]
    (hplus : ∀ k, Measurable (Γplus k)) (hminus : ∀ k, Measurable (Γminus k))
    (H : I → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (D : I → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hmassplus : ∀ k, (∫⁻ w, Γplus k w univ ∂P k) ≤ C)
    (hmassminus : ∀ k, (∫⁻ w, Γminus k w univ ∂P k) ≤ C) :
    IsTightMeasureSet (range (fun k ↦
      (physicalSceneRootedCountableLocalSceneLaw base (P k) (Γplus k) (Γminus k)
        (hplus k) (hminus k) (H k) (hH k) (coord k) (hcoord k) u hu
        (Y k) (hY k) (D k) (hD k) : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))) := by
  exact isTightMeasureSet_original_joint_of_marginals
    (fun k ↦ (P k).prod (cavityRootMeasure volume (D k) ((m k : ℝ) + 1)))
    (fun k ↦ physicalSceneRootedLocalScene
      (fun w ↦ (Γplus k w).restrict (H k ×ˢ univ))
      (fun w ↦ (Γminus k w).restrict (H k ×ˢ univ)) (coord k) u ((m k : ℝ) + 1))
    (fun k ↦ cavityRootedTargetConfiguration base
      (fun w j ↦ (coord k (Y k w j), u (Y k w j))))
    (fun k ↦ measurable_physicalSceneRootedLocalScene _ _
      (measurable_physicalPlan_sourceRestriction (Γplus k) (hplus k) (H k) (hH k))
      (measurable_physicalPlan_sourceRestriction (Γminus k) (hminus k) (H k) (hH k))
      (coord k) (hcoord k) u hu ((m k : ℝ) + 1))
    (fun k ↦ measurable_cavityRootedTargetConfiguration base _
      (fun j ↦ ((hcoord k).comp (hY k j)).prodMk (hu.comp (hY k j))))
    (isTightMeasureSet_physicalSceneRestrictedRootedLocalSceneLaw P Γplus Γminus
      hplus hminus H hH coord hcoord u hu (fun k ↦ (m k : ℝ) + 1)
      (fun _ ↦ by positivity) D hD C hC hmassplus hmassminus)
    (isTightMeasureSet_physicalSceneRootedTargetConfiguration base m P _
      (fun k j ↦ ((hcoord k).comp (hY k j)).prodMk (hu.comp (hY k j))) D)


/-- The actual physical source restriction keeps its original target labels. -/
theorem physicalSceneRootedLocalPlan_supportedOver_targets {n : ℕ}
    (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
    (w : Ω) (Y : Fin (n + 1) → M)
    (hcarried : ∀ᵐ p ∂Γ w, p.2 ∈ range Y)
    (H : Set M) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ) :
    SupportedOverConfiguration Prod.snd
      (ofTuple base (fun j ↦ (coord (Y j) - z, u (Y j))))
      (physicalSceneRootedLocalPlan (fun w ↦ (Γ w).restrict (H ×ˢ univ))
        coord u N (w, z)) := by
  apply (supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mpr
  rw [coe_physicalSceneRootedLocalPlan]
  unfold physicalSceneRootedPlan
  apply Measure.ae_smul_measure
  apply (ae_map_iff
    (measurable_physicalSceneRootedObservation coord hcoord u hu z).aemeasurable
    ((isClosed_multiplicity_support _).measurableSet.preimage measurable_snd)).mpr
  filter_upwards [ae_restrict_of_ae hcarried] with p hp
  rcases hp with ⟨j, hj⟩
  exact (multiplicity_ofTuple_ne_zero_iff _ _).mpr ⟨j, by simp
    [physicalSceneRootedObservation, hj]⟩

/-- Both finite actual plans are carried by the same original integer cloud
before taking a limit. -/
theorem ae_physicalSceneRootedCountableLocalSceneLaw_supported {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    (hcarriedplus : ∀ᵐ w ∂P, ∀ᵐ p ∂Γplus w, p.2 ∈ range (Y w))
    (hcarriedminus : ∀ᵐ w ∂P, ∀ᵐ p ∂Γminus w, p.2 ∈ range (Y w)) :
    ∀ᵐ s ∂(physicalSceneRootedCountableLocalSceneLaw base P Γplus Γminus hplus hminus
        H hH coord hcoord u hu Y hY D hD : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
        SupportedOverConfiguration Prod.snd s.2 s.1.2 := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  apply (ae_map_iff
    (measurable_physicalSceneRootedCountableObservation base _ _
      (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
      (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
      coord hcoord u hu ((n : ℝ) + 1) Y hY).aemeasurable
    (((isClosed_supportedOverConfiguration Prod.snd continuous_snd).preimage
      (continuous_snd.prodMk continuous_fst.fst)).inter
      ((isClosed_supportedOverConfiguration Prod.snd continuous_snd).preimage
        (continuous_snd.prodMk continuous_fst.snd))).measurableSet).mpr
  have hf : ∀ᵐ v ∂P.prod (cavityRootMeasure volume D ((n : ℝ) + 1)),
      (∀ᵐ p ∂Γplus v.1, p.2 ∈ range (Y v.1)) ∧
      (∀ᵐ p ∂Γminus v.1, p.2 ∈ range (Y v.1)) := by
    apply ae_of_ae_map (p := fun w ↦
      (∀ᵐ p ∂Γplus w, p.2 ∈ range (Y w)) ∧
      (∀ᵐ p ∂Γminus w, p.2 ∈ range (Y w))) measurable_fst.aemeasurable
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using
      hcarriedplus.and hcarriedminus
  filter_upwards [hf] with v hv
  exact ⟨physicalSceneRootedLocalPlan_supportedOver_targets base Γplus v.1 (Y v.1) hv.1
      H coord hcoord u hu ((n : ℝ) + 1) v.2,
    physicalSceneRootedLocalPlan_supportedOver_targets base Γminus v.1 (Y v.1) hv.2
      H coord hcoord u hu ((n : ℝ) + 1) v.2⟩

/-- Actual mass and target carrying produce a common weak countable scene. -/
theorem exists_tendsto_subseq_physicalSceneRootedCountableLocalSceneLaw
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (Γplus Γminus : ∀ k, Ω k → Measure (M × M))
    [∀ k w, IsFiniteMeasure (Γplus k w)] [∀ k w, IsFiniteMeasure (Γminus k w)]
    (hplus : ∀ k, Measurable (Γplus k)) (hminus : ∀ k, Measurable (Γminus k))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hmassplus : ∀ k, (∫⁻ w, Γplus k w univ ∂P k) ≤ C)
    (hmassminus : ∀ k, (∫⁻ w, Γminus k w univ ∂P k) ≤ C)
    (hcarriedplus : ∀ k, ∀ᵐ w ∂P k, ∀ᵐ p ∂Γplus k w, p.2 ∈ range (Y k w))
    (hcarriedminus : ∀ k, ∀ᵐ w ∂P k, ∀ᵐ p ∂Γminus k w, p.2 ∈ range (Y k w)) :
    ∃ Q, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ physicalSceneRootedCountableLocalSceneLaw base (P (φ k))
        (Γplus (φ k)) (Γminus (φ k)) (hplus (φ k)) (hminus (φ k))
        (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k)) u hu
        (Y (φ k)) (hY (φ k)) (D (φ k)) (hD (φ k))) atTop (𝓝 Q) ∧
      ∀ᵐ s ∂(Q : Measure
        (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
        SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
          SupportedOverConfiguration Prod.snd s.2 s.1.2 := by
  let laws := fun k ↦ physicalSceneRootedCountableLocalSceneLaw base (P k)
    (Γplus k) (Γminus k) (hplus k) (hminus k) (H k) (hH k)
    (coord k) (hcoord k) u hu (Y k) (hY k) (D k) (hD k)
  have htight := isTightMeasureSet_physicalSceneRootedCountableLocalSceneLaw
    base m P Γplus Γminus hplus hminus H hH coord hcoord u hu Y hY D hD
    C hC hmassplus hmassminus
  obtain ⟨Q, φ, hφ, hweak⟩ := exists_tendsto_subseq_probabilityMeasure_of_isTight laws htight
  refine ⟨Q, φ, hφ, hweak, ?_⟩
  have hs (k : ℕ) := ae_physicalSceneRootedCountableLocalSceneLaw_supported base (P k)
    (Γplus k) (Γminus k) (hplus k) (hminus k) (H k) (hH k) (coord k) (hcoord k)
    u hu (Y k) (hY k) (D k) (hD k) (hcarriedplus k) (hcarriedminus k)
  exact (ae_supportedOverConfiguration_of_weak_tendsto Q (laws ∘ φ) hweak
    Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.1) continuous_snd continuous_fst.fst
    (fun k ↦ (hs (φ k)).mono fun _ h ↦ h.1)).and
    (ae_supportedOverConfiguration_of_weak_tendsto Q (laws ∘ φ) hweak
      Prod.snd continuous_snd Prod.snd (fun s ↦ s.1.2) continuous_snd continuous_fst.snd
      (fun k ↦ (hs (φ k)).mono fun _ h ↦ h.2))


/-- Original feasible global allocations use their same sampled target tuple. -/
theorem ae_physicalSceneGlobalAllocationFamily_targets
    [MeasurableSingletonClass M] {n : ℕ}
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (a : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂P, IsSemidiscreteAllocation μ (p w) (a w)) :
    ∀ᵐ w ∂P, ∀ᵐ e ∂physicalSceneGlobalAllocationFamily μ a Y w, e.2 ∈ range (Y w) := by
  filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq P μ a Y p hfeas, hfeas]
    with w heq hw
  rw [heq]
  exact (ae_physicalSceneAllocationPlan_carried hw (Y w) MeasurableSet.univ
    (finite_range (Y w)).measurableSet (Eventually.of_forall fun _ ↦ mem_univ _)
    (fun j ↦ mem_range_self j)).mono fun _ h ↦ h.2

/-- The original allocation scene also retains its same integer target labels. -/
def actualAllocationRootedCountableSceneLaw {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base) :=
  physicalSceneRootedCountableLocalSceneLaw base P
    (physicalSceneGlobalAllocationFamily μ aplus Y)
    (physicalSceneGlobalAllocationFamily μ aminus Y)
    (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY)
    (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY)
    H hH coord hcoord u hu Y hY D hD

/-- Original feasibility constructs one weak limit with the same countable
target carrier for both actual source-restricted physical plans. -/
theorem exists_tendsto_subseq_actualAllocationRootedCountableSceneLaw
    [MeasurableSingletonClass M]
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ k, Ω k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ω k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ω k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ω k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (p : ∀ k, Ω k → Fin (m k + 1) → ℝ)
    (hfeasplus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aplus k w))
    (hfeasminus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aminus k w))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1)) :
    ∃ Q, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ actualAllocationRootedCountableSceneLaw base (P (φ k)) μ
        (aplus (φ k)) (aminus (φ k)) (hplus (φ k)) (hminus (φ k))
        (Y (φ k)) (hY (φ k)) (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k))
        u hu (D (φ k)) (hD (φ k))) atTop (𝓝 Q) ∧
      ∀ᵐ s ∂(Q : Measure
        (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
        SupportedOverConfiguration Prod.snd s.2 s.1.1 ∧
          SupportedOverConfiguration Prod.snd s.2 s.1.2 := by
  exact exists_tendsto_subseq_physicalSceneRootedCountableLocalSceneLaw base m P
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (aplus k) (Y k))
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (aminus k) (Y k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aplus k) (hplus k) (Y k) (hY k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aminus k) (hminus k) (Y k) (hY k))
    H hH coord hcoord u hu Y hY D hD (μ univ) (measure_ne_top μ univ)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P k) μ
      (aplus k) (Y k) (p k) (hfeasplus k)).le)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P k) μ
      (aminus k) (Y k) (p k) (hfeasminus k)).le)
    (fun k ↦ ae_physicalSceneGlobalAllocationFamily_targets (P k) μ
      (aplus k) (Y k) (p k) (hfeasplus k))
    (fun k ↦ ae_physicalSceneGlobalAllocationFamily_targets (P k) μ
      (aminus k) (Y k) (p k) (hfeasminus k))


/-- The original countable allocation scene projects to its exact original
source-restricted two-plan law. -/
theorem map_actualAllocationRootedCountableSceneLaw_pair {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure.map
      (actualAllocationRootedCountableSceneLaw base P μ aplus aminus hplus hminus
        Y hY H hH coord hcoord u hu D hD)
      (f := Prod.fst) measurable_fst.aemeasurable =
    actualAllocationRootedSceneLaw P μ aplus aminus hplus hminus Y hY
      H hH coord hcoord u hu ((n : ℝ) + 1) (by positivity) D hD :=
  map_physicalSceneRootedCountableLocalSceneLaw_pair base P
    (physicalSceneGlobalAllocationFamily μ aplus Y)
    (physicalSceneGlobalAllocationFamily μ aminus Y)
    (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY)
    (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY)
    H hH coord hcoord u hu Y hY D hD

end OTSelector.Reconstruction
