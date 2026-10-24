import OTSelector.Transport.CyclicMonotonicity.StrictCyclePairMeasure
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitProjectedCycleAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedAccuracy
import OTSelector.MeasureTheory.MeasureProductDefect

/-! Original retained/lost extensions remove actual full-plan cycle mass on their fixed projection. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local instance cyclePairAccuracyStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance cyclePairAccuracyConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance cyclePairAccuracyConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance cyclePairAccuracyConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance cyclePairAccuracyPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Auxiliary original cores remove strict-cycle pair mass on one SAME full
scene law. Compact finiteness supplies every local mass cutoff internally;
only actual discarded source mass is charged and its accuracy is taken last. -/
theorem ae_full_cyclePairMass_zero_of_actual_projected_core_accuracy
    (Rfull : ProbabilityMeasure MacroScene) (Raux : ℕ → ProbabilityMeasure JointScene)
    (hprojection : ∀ m, (Raux m).map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (bad : Set (MacroScene × (Edge × Edge))) (hbad : MeasurableSet bad)
    (K : Set Edge) (hK : IsCompact K)
    (hbadK : ∀ s : MacroScene, Prod.mk s ⁻¹' bad ⊆ K ×ˢ K)
    (U : Set (ι → ℝ)) (hKU : K ⊆ {e | e.1.1 ∈ U})
    (hdecomposition : ∀ m, ∀ᵐ s ∂(Raux m : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hretained : ∀ m, ∀ᵐ s ∂(Raux m : Measure JointScene),
      physicalSceneCyclePairMass
        (fun s : JointScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
        ((fun z : JointScene × (Edge × Edge) ↦ (z.1.1, z.2)) ⁻¹' bad) s = 0)
    (accuracy : ℕ → ℝ≥0∞) (haccuracy : Tendsto accuracy atTop (𝓝 0))
    (hlost : ∀ (m : ℕ) (level : ℝ≥0∞), 0 < level → level ≠ ⊤ →
      (Raux m : Measure JointScene)
        {s | level < physicalSceneMaskedLostSourceMass base U s} ≤ accuracy m / level) :
    ∀ᵐ s ∂(Rfull : Measure MacroScene),
      physicalSceneCyclePairMass
        (fun s : MacroScene ↦ LocalFiniteMeasure.cavityAverage s.2.1) bad s = 0 := by
  let fullPlan : MacroScene → LocalFiniteMeasure Edge :=
    fun s ↦ LocalFiniteMeasure.cavityAverage s.2.1
  let retainedPlan : JointScene → LocalFiniteMeasure Edge :=
    fun s ↦ LocalFiniteMeasure.cavityAverage s.2.1
  let retainedBad : Set (JointScene × (Edge × Edge)) :=
    (fun z : JointScene × (Edge × Edge) ↦ (z.1.1, z.2)) ⁻¹' bad
  have hfull : Measurable fullPlan :=
    LocalFiniteMeasure.continuous_cavityAverage.measurable.comp measurable_snd.fst
  have hW := measurable_physicalSceneCyclePairMass fullPlan hfull hbad
  have hmass : Measurable (fun s : MacroScene ↦ (fullPlan s : Measure Edge) K) :=
    (Measure.measurable_coe hK.measurableSet).comp (measurable_localFiniteMeasure_coe.comp hfull)
  apply ae_eq_zero_of_projected_cycle_retained_zero_and_lost_accuracy
    Rfull Raux Prod.fst measurable_fst hprojection
    (physicalSceneCyclePairMass fullPlan bad)
    (fun s ↦ (fullPlan s : Measure Edge) K) hW hmass
    (ae_of_all _ fun s ↦ hK.measure_ne_top)
    (fun _ s ↦ physicalSceneCyclePairMass retainedPlan retainedBad s)
    (fun _ ↦ physicalSceneMaskedLostSourceMass base U) ?_ hretained accuracy haccuracy hlost
  intro m
  filter_upwards [hdecomposition m] with s hs
  have hsplit : (fullPlan s.1 : Measure Edge) =
      (retainedPlan s : Measure Edge) + (LocalFiniteMeasure.cavityAverage s.2.2 : Measure Edge) := by
    change (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge) = _
    rw [show s.1.2.1 = physicalScenePairSum s.2 from hs, physicalScene_cavityAverage_pairSum]
  have hb := measure_prod_self_witness_le_of_add
    (fullPlan s.1 : Measure Edge) (retainedPlan s : Measure Edge)
    (LocalFiniteMeasure.cavityAverage s.2.2 : Measure Edge) hsplit (hbadK s.1)
  change (fullPlan s.1 : Measure Edge).prod (fullPlan s.1) (Prod.mk s.1 ⁻¹' bad) ≤
    (retainedPlan s : Measure Edge).prod (retainedPlan s) (Prod.mk s.1 ⁻¹' bad) +
      2 * (fullPlan s.1 : Measure Edge) K *
        (LocalFiniteMeasure.cavityAverage s.2.2 : Measure Edge) {e | e.1.1 ∈ U}
  apply hb.trans
  gcongr
end OTSelector.Reconstruction
