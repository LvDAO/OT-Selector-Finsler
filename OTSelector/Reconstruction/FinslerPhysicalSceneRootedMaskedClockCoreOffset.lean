import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreCarrierObservation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedJoint
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel

/-! Original clock-conditioned carriers on the same actual masked joint law. -/

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
theorem measurableSet_physicalSceneClockCoreOffsetCarrier
    {S : Type*} [MeasurableSpace S]
    (tag : S → V) (htag : Measurable tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Measurable plan)
    (scale : ℝ) {T : Set (ℝ × ℝ)} (hT : MeasurableSet T)
    {K : Set V} (hK : MeasurableSet K) :
    MeasurableSet {s | ∀ᵐ e ∂(plan s : Measure Edge), (e.1.2, e.2.2) ∈ T → tag s + scale⁻¹ • e.1.1 ∈ K} := by
  let κ : Kernel S Edge := localFiniteMeasureKernel.comap plan hplan
  let bad : Set (S × Edge) :=
    {q | (q.2.1.2, q.2.2.2) ∈ T ∧ tag q.1 + scale⁻¹ • q.2.1.1 ∉ K}
  have hbad : MeasurableSet bad :=
    (hT.preimage (measurable_snd.fst.snd.prodMk measurable_snd.snd.snd)).inter
      (hK.compl.preimage ((htag.comp measurable_fst).add
        (measurable_snd.fst.fst.const_smul scale⁻¹)))
  have hm : Measurable (fun s ↦ κ s (Prod.mk s ⁻¹' bad)) :=
    Kernel.measurable_kernel_prodMk_left hbad
  convert measurableSet_eq_fun hm
    (measurable_const : Measurable (fun _ : S ↦ (0 : ℝ≥0∞))) using 1
  ext s
  simp only [ae_iff, κ, Kernel.comap_apply, localFiniteMeasureKernel_apply, bad,
    preimage_ofPred_eq, mem_ofPred_eq, not_imp]

/-- Restricting the original source carrier condition to an actual clock event
commutes with the literal same-plan rooted observation. -/
theorem ae_physicalSceneRootedPlan_originalCore_on_clockSet
    (Γ : Measure (M × M)) (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {scale : ℝ} (hscale : scale ≠ 0)
    (N : ℝ) (root : V) {T : Set (ℝ × ℝ)} (hT : MeasurableSet T)
    {K : Set V} (hK : MeasurableSet K)
    (hcarried : ∀ᵐ e ∂Γ, (u e.1, u e.2) ∈ T → coord e.1 ∈ K) :
    ∀ᵐ e ∂physicalSceneRootedPlan Γ (fun x ↦ scale • coord x) u N root,
      (e.1.2, e.2.2) ∈ T →
        physicalSceneMacroscopicRoot scale root + scale⁻¹ • e.1.1 ∈ K := by
  apply Measure.ae_smul_measure
  have hf := measurable_physicalSceneRootedObservation
    (fun x ↦ scale • coord x) (hcoord.const_smul scale) u hu root
  have hpred : MeasurableSet {e : Edge | (e.1.2, e.2.2) ∈ T →
      physicalSceneMacroscopicRoot scale root + scale⁻¹ • e.1.1 ∈ K} :=
    (hT.preimage (measurable_fst.snd.prodMk measurable_snd.snd)).imp
      (hK.preimage (measurable_const.add (measurable_fst.fst.const_smul scale⁻¹)))
  apply (ae_map_iff hf.aemeasurable hpred).mpr
  filter_upwards [hcarried] with e he
  rwa [physicalSceneRootedObservation_original_coordinate hscale]

variable (base : (ι → ℝ) × ℝ)
local instance clockCoreOffsetStandardBorel : StandardBorelSpace (V × ℝ) := inferInstance
local instance clockCoreOffsetConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance clockCoreOffsetConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance clockCoreOffsetConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance clockCoreOffsetPlanPolish : PolishSpace (LocalFiniteMeasure Edge) :=
  LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene (V × ℝ) (V × ℝ)
local notation "MacroScene" => V × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The same original probability experiment supplies the exact shrinking
source-offset carrier for BOTH of its actual retained plans. -/
theorem ae_physicalSceneRootedMaskedMacroscopicSceneLaw_clockCoreOffset {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → V) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {scale : ℝ} (hscale : scale ≠ 0)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set V) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    {T : Set (ℝ × ℝ)} (hT : MeasurableSet T) {K : Set V} (hK : MeasurableSet K)
    (hcarriedp : ∀ w, ∀ᵐ e ∂((Γp w).restrict E).restrict (H ×ˢ univ), (u e.1, u e.2) ∈ T → coord e.1 ∈ K)
    (hcarriedm : ∀ w, ∀ᵐ e ∂((Γm w).restrict E).restrict (H ×ˢ univ), (u e.1, u e.2) ∈ T → coord e.1 ∈ K) :
    ∀ᵐ s ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
      (fun x ↦ scale • coord x) (hcoord.const_smul scale) u hu scale Y hY D hD : Measure JointScene),
      (∀ᵐ e ∂(s.2.1.1 : Measure Edge), (e.1.2, e.2.2) ∈ T → s.1.1 + scale⁻¹ • e.1.1 ∈ K) ∧
      (∀ᵐ e ∂(s.2.1.2 : Measure Edge), (e.1.2, e.2.2) ∈ T → s.1.1 + scale⁻¹ • e.1.1 ∈ K) := by
  have hset : MeasurableSet {s : JointScene |
      (∀ᵐ e ∂(s.2.1.1 : Measure Edge), (e.1.2, e.2.2) ∈ T → s.1.1 + scale⁻¹ • e.1.1 ∈ K) ∧
      (∀ᵐ e ∂(s.2.1.2 : Measure Edge), (e.1.2, e.2.2) ∈ T → s.1.1 + scale⁻¹ • e.1.1 ∈ K)} :=
    (measurableSet_physicalSceneClockCoreOffsetCarrier (fun s : JointScene ↦ s.1.1)
      measurable_fst.fst (fun s ↦ s.2.1.1) measurable_snd.fst.fst scale hT hK).inter
      (measurableSet_physicalSceneClockCoreOffsetCarrier (fun s : JointScene ↦ s.1.1)
        measurable_fst.fst (fun s ↦ s.2.1.2) measurable_snd.fst.snd scale hT hK)
  change ∀ᵐ s ∂((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E
      (fun x ↦ scale • coord x) u ((n : ℝ) + 1) scale Y)), _
  apply (ae_map_iff
    (measurable_physicalSceneRootedMaskedMacroscopicObservation base Γp Γm hp hm H hH E hE
      (fun x ↦ scale • coord x) (hcoord.const_smul scale) u hu ((n : ℝ) + 1) scale Y hY).aemeasurable
    hset).mpr
  exact ae_of_all _ fun v ↦
    ⟨ae_physicalSceneRootedPlan_originalCore_on_clockSet _ coord hcoord u hu hscale
        ((n : ℝ) + 1) v.2 hT hK (hcarriedp v.1),
      ae_physicalSceneRootedPlan_originalCore_on_clockSet _ coord hcoord u hu hscale
        ((n : ℝ) + 1) v.2 hT hK (hcarriedm v.1)⟩

end OTSelector.Reconstruction
