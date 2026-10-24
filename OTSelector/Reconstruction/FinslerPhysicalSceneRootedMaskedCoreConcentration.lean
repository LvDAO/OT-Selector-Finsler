import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreCarrierObservation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedJoint
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel

/-!
# The actual retained joint law has its original shrinking source offsets

The original compact source carrier survives the literal same-plan observation.
The relevant almost-everywhere predicate is proved measurable using the already
constructed kernel of actual locally finite measures, so it transfers through
the unchanged original joint pushforward law.
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
local notation "V" => ι → ℝ
local notation "Edge" => ((V × ℝ) × (V × ℝ))

/-- The exact original source-offset carrier is measurable on any actual tagged
locally finite plan family. No measurability premise is hidden in its AE transfer. -/
theorem measurableSet_physicalSceneCoreOffsetCarrier
    {S : Type*} [MeasurableSpace S]
    (tag : S → V) (htag : Measurable tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Measurable plan)
    (scale : ℝ) {K : Set V} (hK : MeasurableSet K) :
    MeasurableSet {s | ∀ᵐ e ∂(plan s : Measure Edge), tag s + scale⁻¹ • e.1.1 ∈ K} := by
  let κ : Kernel S Edge := localFiniteMeasureKernel.comap plan hplan
  let bad : Set (S × Edge) := {q | tag q.1 + scale⁻¹ • q.2.1.1 ∉ K}
  have hbad : MeasurableSet bad :=
    hK.compl.preimage ((htag.comp measurable_fst).add
      (measurable_snd.fst.fst.const_smul scale⁻¹))
  have hm : Measurable (fun s ↦ κ s (Prod.mk s ⁻¹' bad)) :=
    Kernel.measurable_kernel_prodMk_left hbad
  convert measurableSet_eq_fun hm
    (measurable_const : Measurable (fun _ : S ↦ (0 : ℝ≥0∞))) using 1
  ext s
  simp only [ae_iff, κ, Kernel.comap_apply, localFiniteMeasureKernel_apply, bad,
    preimage_ofPred_eq, mem_ofPred_eq]

variable (base : (ι → ℝ) × ℝ)
local instance maskedCoreOffsetStandardBorel : StandardBorelSpace (V × ℝ) := inferInstance
local instance maskedCoreOffsetConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance maskedCoreOffsetConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedCoreOffsetConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedCoreOffsetPlanPolish : PolishSpace (LocalFiniteMeasure Edge) :=
  LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene (V × ℝ) (V × ℝ)
local notation "MacroScene" => V × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The same original probability experiment supplies the exact shrinking
source-offset carrier for BOTH of its actual retained plans. -/
theorem ae_physicalSceneRootedMaskedMacroscopicSceneLaw_coreOffset {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {scale : ℝ} (hscale : scale ≠ 0)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set V) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    {K : Set V} (hK : MeasurableSet K)
    (hcarriedp : ∀ w, ∀ᵐ e ∂((Γp w).restrict E).restrict (H ×ˢ univ), coord e.1 ∈ K)
    (hcarriedm : ∀ w, ∀ᵐ e ∂((Γm w).restrict E).restrict (H ×ˢ univ), coord e.1 ∈ K) :
    ∀ᵐ s ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
      (fun x ↦ scale • coord x) (hcoord.const_smul scale) u hu scale Y hY D hD : Measure JointScene),
      (∀ᵐ e ∂(s.2.1.1 : Measure Edge), s.1.1 + scale⁻¹ • e.1.1 ∈ K) ∧
      (∀ᵐ e ∂(s.2.1.2 : Measure Edge), s.1.1 + scale⁻¹ • e.1.1 ∈ K) := by
  have hset : MeasurableSet {s : JointScene |
      (∀ᵐ e ∂(s.2.1.1 : Measure Edge), s.1.1 + scale⁻¹ • e.1.1 ∈ K) ∧
      (∀ᵐ e ∂(s.2.1.2 : Measure Edge), s.1.1 + scale⁻¹ • e.1.1 ∈ K)} :=
    (measurableSet_physicalSceneCoreOffsetCarrier (fun s : JointScene ↦ s.1.1)
      measurable_fst.fst (fun s ↦ s.2.1.1) measurable_snd.fst.fst scale hK).inter
      (measurableSet_physicalSceneCoreOffsetCarrier (fun s : JointScene ↦ s.1.1)
        measurable_fst.fst (fun s ↦ s.2.1.2) measurable_snd.fst.snd scale hK)
  change ∀ᵐ s ∂((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E
      (fun x ↦ scale • coord x) u ((n : ℝ) + 1) scale Y)), _
  apply (ae_map_iff
    (measurable_physicalSceneRootedMaskedMacroscopicObservation base Γp Γm hp hm H hH E hE
      (fun x ↦ scale • coord x) (hcoord.const_smul scale) u hu ((n : ℝ) + 1) scale Y hY).aemeasurable
    hset).mpr
  exact ae_of_all _ fun v ↦
    ⟨ae_physicalSceneRootedPlan_originalCore _ coord hcoord u hu hscale
        ((n : ℝ) + 1) v.2 hK (hcarriedp v.1),
      ae_physicalSceneRootedPlan_originalCore _ coord hcoord u hu hscale
        ((n : ℝ) + 1) v.2 hK (hcarriedm v.1)⟩

end OTSelector.Reconstruction
