import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedJoint
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMacroscopic
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitProjectedExtension

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
local instance actualMaskedJointSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance actualMaskedJointSceneConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance actualMaskedJointSceneConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance actualMaskedJointSceneConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance actualMaskedJointScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)

/-- The unchanged original global allocation experiment jointly records its
own full, retained and lost physical plans and its original integer target cloud. -/
def actualAllocationRootedMaskedMacroscopicSceneLaw {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hp : ∀ j, Measurable (fun z : Ω × M ↦ ap z.1 z.2 j))
    (hm : ∀ j, Measurable (fun z : Ω × M ↦ am z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    ProbabilityMeasure (MacroScene × (PairScene × PairScene)) :=
  physicalSceneRootedMaskedMacroscopicSceneLaw base Penv
    (physicalSceneGlobalAllocationFamily μ ap Y) (physicalSceneGlobalAllocationFamily μ am Y)
    (measurable_physicalSceneGlobalAllocationFamily μ ap hp Y hY)
    (measurable_physicalSceneGlobalAllocationFamily μ am hm Y hY)
    H hH E hE coord hcoord u hu scale Y hY D hD

/-- Forgetting the same actual retained/lost pieces gives exactly the previously
fixed original macro-tagged allocation scene and its random restricted columns. -/
theorem map_actualAllocationRootedMaskedMacroscopicSceneLaw_full {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hp : ∀ j, Measurable (fun z : Ω × M ↦ ap z.1 z.2 j))
    (hm : ∀ j, Measurable (fun z : Ω × M ↦ am z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    (actualAllocationRootedMaskedMacroscopicSceneLaw base Penv μ ap am hp hm Y hY
      H hH E hE coord hcoord u hu scale D hD).map (f := Prod.fst) measurable_fst.aemeasurable =
        actualAllocationRootedMacroscopicSceneLaw base Penv μ ap am hp hm Y hY
          H hH coord hcoord u hu scale D hD :=
  map_physicalSceneRootedMaskedMacroscopicSceneLaw_full base Penv _ _ _ _ H hH E hE
    coord hcoord u hu scale Y hY D hD

/-- Actual original feasibility supplies the source mass needed for joint
retained/lost tightness; the caller supplies no auxiliary mass or column law. -/
theorem isTightMeasureSet_actualAllocationRootedMaskedMacroscopicSceneLaw
    {I : Type*} {Ωn : I → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : I → ℕ) (P : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (P k)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (ap am : ∀ k, Ωn k → M → Fin (m k + 1) → ℝ)
    (hp : ∀ k j, Measurable (fun z : Ωn k × M ↦ ap k z.1 z.2 j))
    (hm : ∀ k j, Measurable (fun z : Ωn k × M ↦ am k z.1 z.2 j))
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M) (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (p : ∀ k, Ωn k → Fin (m k + 1) → ℝ)
    (hfp : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (ap k w))
    (hfm : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (am k w))
    (H : I → Set M) (hH : ∀ k, MeasurableSet (H k))
    (E : I → Set (M × M)) (hE : ∀ k, MeasurableSet (E k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u) (scale : I → ℝ)
    (D : I → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ k z, z ∈ D k → physicalSceneMacroscopicRoot (scale k) z ∈ K) :
    IsTightMeasureSet (range (fun k ↦
      (actualAllocationRootedMaskedMacroscopicSceneLaw base (P k) μ
        (ap k) (am k) (hp k) (hm k) (Y k) (hY k) (H k) (hH k) (E k) (hE k)
        (coord k) (hcoord k) u hu (scale k) (D k) (hD k) :
          Measure (MacroScene × (PairScene × PairScene))))) :=
  isTightMeasureSet_physicalSceneRootedMaskedMacroscopicSceneLaw base m P
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (ap k) (Y k))
    (fun k ↦ physicalSceneGlobalAllocationFamily μ (am k) (Y k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (ap k) (hp k) (Y k) (hY k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (am k) (hm k) (Y k) (hY k))
    H hH E hE coord hcoord u hu scale Y hY D hD K hK hDK
    (μ univ) (measure_ne_top μ univ)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P k) μ
      (ap k) (Y k) (p k) (hfp k)).le)
    (fun k ↦ (lintegral_physicalSceneGlobalAllocationFamily_univ (P k) μ
      (am k) (Y k) (p k) (hfm k)).le)

/-- Every fixed auxiliary edge mask has an actual joint two-stage limit OVER
THE GIVEN full-scene inner and outer laws. Only their own subsequences are
refined; the full scene and the original realized random columns remain fixed. -/
theorem exists_iterated_actualAllocationRootedMaskedScene_over_given_full_limits
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hp : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 j))
    (hm : ∀ ℓ n j, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 j))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M) (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂P n, IsSemidiscreteAllocation μ (p n w) (am ℓ n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (scale : ℕ → ℝ)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hDK : ∀ n z, z ∈ D n → physicalSceneMacroscopicRoot (scale n) z ∈ K)
    (Qfull : ℕ → ProbabilityMeasure MacroScene) (Rfull : ProbabilityMeasure MacroScene)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, StrictMono (φ ℓ))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ actualAllocationRootedMacroscopicSceneLaw base
      (P (φ ℓ n)) μ (ap ℓ (φ ℓ n)) (am ℓ (φ ℓ n)) (hp ℓ (φ ℓ n)) (hm ℓ (φ ℓ n))
      (Y (φ ℓ n)) (hY (φ ℓ n)) (H (φ ℓ n)) (hH (φ ℓ n))
      (coord (φ ℓ n)) (hcoord (φ ℓ n)) u hu (scale (φ ℓ n)) (D (φ ℓ n)) (hD (φ ℓ n)))
      atTop (𝓝 (Qfull ℓ)))
    (houter : Tendsto (fun ℓ ↦ Qfull (ψ ℓ)) atTop (𝓝 Rfull)) :
    let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base (P n) μ
      (ap ℓ n) (am ℓ n) (hp ℓ n) (hm ℓ n) (Y n) (hY n)
      (H n) (hH n) E hE (coord n) (hcoord n) u hu (scale n) (D n) (hD n)
    ∃ Q : ℕ → ProbabilityMeasure (MacroScene × (PairScene × PairScene)),
    ∃ θ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (θ ℓ) ∧ StrictMono (fun n ↦ φ ℓ (θ ℓ n)) ∧
        Tendsto (fun n ↦ laws ℓ (φ ℓ (θ ℓ n))) atTop (𝓝 (Q ℓ)) ∧
        (Q ℓ).map (f := Prod.fst) measurable_fst.aemeasurable = Qfull ℓ) ∧
      ∃ R : ProbabilityMeasure (MacroScene × (PairScene × PairScene)), ∃ η : ℕ → ℕ,
        StrictMono η ∧ StrictMono (fun ℓ ↦ ψ (η ℓ)) ∧
        Tendsto (fun ℓ ↦ Q (ψ (η ℓ))) atTop (𝓝 R) ∧
        R.map (f := Prod.fst) measurable_fst.aemeasurable = Rfull := by
  let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base (P n) μ
    (ap ℓ n) (am ℓ n) (hp ℓ n) (hm ℓ n) (Y n) (hY n)
    (H n) (hH n) E hE (coord n) (hcoord n) u hu (scale n) (D n) (hD n)
  let full := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base (P n) μ
    (ap ℓ n) (am ℓ n) (hp ℓ n) (hm ℓ n) (Y n) (hY n)
    (H n) (hH n) (coord n) (hcoord n) u hu (scale n) (D n) (hD n)
  have htight : IsTightMeasureSet (range (fun q : ℕ × ℕ ↦ (laws q.1 q.2 :
      Measure (MacroScene × (PairScene × PairScene))))) :=
    isTightMeasureSet_actualAllocationRootedMaskedMacroscopicSceneLaw base
      (fun q : ℕ × ℕ ↦ m q.2) (fun q : ℕ × ℕ ↦ P q.2) μ
      (fun q ↦ ap q.1 q.2) (fun q ↦ am q.1 q.2)
      (fun q ↦ hp q.1 q.2) (fun q ↦ hm q.1 q.2)
      (fun q ↦ Y q.2) (fun q ↦ hY q.2) (fun q ↦ p q.2)
      (fun q ↦ hfp q.1 q.2) (fun q ↦ hfm q.1 q.2)
      (fun q ↦ H q.2) (fun q ↦ hH q.2) (fun _ ↦ E) (fun _ ↦ hE)
      (fun q ↦ coord q.2) (fun q ↦ hcoord q.2) u hu
      (fun q ↦ scale q.2) (fun q ↦ D q.2) (fun q ↦ hD q.2) K hK (fun q ↦ hDK q.2)
  exact exists_iterated_weak_extension_of_exact_projection laws full Prod.fst continuous_fst
    (fun ℓ n ↦ map_actualAllocationRootedMaskedMacroscopicSceneLaw_full base (P n) μ
      (ap ℓ n) (am ℓ n) (hp ℓ n) (hm ℓ n) (Y n) (hY n)
      (H n) (hH n) E hE (coord n) (hcoord n) u hu (scale n) (D n) (hD n))
    htight Qfull Rfull φ hφ ψ hψ hinner houter

end OTSelector.Reconstruction
