import OTSelector.MeasureTheory.ProjectedSourceAbsoluteContinuity
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedProjectedCyclePairAccuracy

/-!
# Full source absolute continuity from actual masked projected scenes

The closed actual retained/lost decomposition gives the setwise source split
internally. Retained references and actual lost-source tails then imply source
absolute continuity on the same fixed full projected scene law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local instance maskedProjectedSourceACStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance maskedProjectedSourceACConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology _
local instance maskedProjectedSourceACConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance maskedProjectedSourceACConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance maskedProjectedSourceACPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local notation "Endpoint" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Endpoint × Endpoint)
local notation "PairScene" => CavityLocalScene Endpoint Endpoint
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Exact closed decomposition bounds every full source set in the spatial
window by its actual retained source mass and one actual lost source-window
mass, including nonmeasurable source subsets. -/
theorem physicalSceneMaskedDecomposition_source_inter_le_retained_add_lost
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (s : JointScene) (hs : s ∈ physicalSceneMaskedDecompositionCarrier base)
    (B : Set Endpoint) :
    (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge).fst
        (B ∩ (U ×ˢ (univ : Set ℝ))) ≤
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).fst
        (B ∩ (U ×ˢ (univ : Set ℝ))) +
      physicalSceneMaskedLostSourceMass base U s := by
  have hsplit : (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge) =
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) +
        (LocalFiniteMeasure.cavityAverage s.2.2 : Measure Edge) := by
    rw [show s.1.2.1 = physicalScenePairSum s.2 from hs,
      physicalScene_cavityAverage_pairSum]
  rw [hsplit, Measure.fst_add, Measure.add_apply]
  apply add_le_add le_rfl
  calc
    (LocalFiniteMeasure.cavityAverage s.2.2 : Measure Edge).fst
        (B ∩ (U ×ˢ (univ : Set ℝ))) ≤
      (LocalFiniteMeasure.cavityAverage s.2.2 : Measure Edge).fst
        (U ×ˢ (univ : Set ℝ)) := measure_mono inter_subset_right
    _ = physicalSceneMaskedLostSourceMass base U s := by
      rw [Measure.fst_apply (hU.prod MeasurableSet.univ)]
      unfold physicalSceneMaskedLostSourceMass
      congr 1
      ext e
      simp

/-- Actual closed retained/lost decompositions on arbitrary accuracy
extensions, all projecting to the SAME original full scene law, remove the
setwise-split premise from projected source absolute continuity. -/
theorem ae_full_source_restrict_absolutelyContinuous_of_actual_projected_masked_accuracy
    (Rfull : ProbabilityMeasure MacroScene) (Raux : ℕ → ProbabilityMeasure JointScene)
    (hprojection : ∀ n,
      (Raux n).map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (U : Set (ι → ℝ)) (hU : IsOpen U) (reference : Measure Endpoint)
    (approximant : ℕ → Measure Endpoint) [∀ n, (approximant n).OuterRegular]
    (hac : ∀ n, approximant n ≪ reference)
    (error loss : ℕ → ℝ≥0∞)
    (herror : Tendsto error atTop (𝓝 0)) (hloss : Tendsto loss atTop (𝓝 0))
    (hdecomposition : ∀ n, ∀ᵐ s ∂(Raux n : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hretained : ∀ n, ∀ᵐ s ∂(Raux n : Measure JointScene),
      sourceOpenDominationDefectOn (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge)
        (U ×ˢ (univ : Set ℝ)) (approximant n) (error n))
    (hlost : ∀ n (threshold : ℝ≥0∞), 0 < threshold → threshold ≠ ⊤ →
      (Raux n : Measure JointScene)
        {s | threshold < physicalSceneMaskedLostSourceMass base U s} ≤ loss n / threshold) :
    ∀ᵐ s ∂(Rfull : Measure MacroScene),
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).fst.restrict
        (U ×ˢ (univ : Set ℝ)) ≪ reference := by
  let fullPlan : MacroScene → LocalFiniteMeasure Edge :=
    fun s ↦ LocalFiniteMeasure.cavityAverage s.2.1
  have hfull : Continuous fullPlan :=
    LocalFiniteMeasure.continuous_cavityAverage.comp continuous_snd.fst
  have hmap (n : ℕ) :
      (Raux n : Measure JointScene).map (Prod.fst : JointScene → MacroScene) =
        (Rfull : Measure MacroScene) :=
    congrArg (fun Q : ProbabilityMeasure MacroScene ↦ (Q : Measure MacroScene)) (hprojection n)
  apply ae_absolutelyContinuous_source_restrict_of_projected_retained_discard
    (Rfull : Measure MacroScene) (fun n ↦ (Raux n : Measure JointScene))
    (fun _ ↦ Prod.fst) (fun _ ↦ measurable_fst) hmap fullPlan hfull
    (fun _ s ↦ (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge))
    (U ×ˢ (univ : Set ℝ)) (hU.prod isOpen_univ) reference approximant hac
    (fun _ ↦ physicalSceneMaskedLostSourceMass base U) error loss herror hloss
    ?_ hretained hlost
  intro n
  filter_upwards [hdecomposition n] with s hs B
  exact physicalSceneMaskedDecomposition_source_inter_le_retained_add_lost base U
    hU.measurableSet s hs B

end OTSelector.Reconstruction
