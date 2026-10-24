import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedRetainedPacking
import OTSelector.MeasureTheory.ProjectedRetainedAccuracy

/-!
# Original full rectangle readouts from retained and lost joint extensions

The closed exact decomposition makes every fixed full rectangle witness no
larger than its retained witness plus one lost source-window mass. Each core
accuracy may use its own actual joint extension over the SAME original law.
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
local instance maskedAccuracyStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedAccuracyConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance maskedAccuracyConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedAccuracyConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedAccuracyPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Averaging the exact retained/lost pair split gives the sum of its actual averages. -/
theorem physicalScene_cavityAverage_pairSum (p : PairScene × PairScene) :
    (LocalFiniteMeasure.cavityAverage (physicalScenePairSum p) :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) =
      (LocalFiniteMeasure.cavityAverage p.1 : Measure _) +
        (LocalFiniteMeasure.cavityAverage p.2 : Measure _) := by
  simp only [LocalFiniteMeasure.coe_cavityAverage, physicalScenePairSum,
    coe_physicalSceneLocalFiniteSum, smul_add]
  ac_rfl

/-- Every realization of the closed exact decomposition controls the complete
original rectangle witness by its retained witness and one discarded source mass. -/
theorem physicalScene_full_witness_le_retained_add_lost
    (Emacro : Set (ι → ℝ))
    (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) (U : Set (ι → ℝ))
    (hT₀ : T₀ ⊆ {e | e.1.1 ∈ U}) (hT₁ : T₁ ⊆ {e | e.1.1 ∈ U})
    (s : JointScene) (hs : s ∈ physicalSceneMaskedDecompositionCarrier base) :
    physicalSceneMacroscopicAverageWitness base Emacro T₀ T₁ s.1 ≤
      physicalSceneMaskedRetainedAverageWitness base Emacro T₀ T₁ s +
        physicalSceneMaskedLostSourceMass base U s := by
  have havg : (LocalFiniteMeasure.cavityAverage s.1.2.1 :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) =
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure _) +
        (LocalFiniteMeasure.cavityAverage s.2.2 : Measure _) := by
    rw [show s.1.2.1 = physicalScenePairSum s.2 from hs]
    exact physicalScene_cavityAverage_pairSum s.2
  by_cases hm : s.1.1 ∈ Emacro
  · have hm' : s.1 ∈ Prod.fst ⁻¹' Emacro := hm
    simp only [physicalSceneMacroscopicAverageWitness, physicalSceneMaskedRetainedAverageWitness,
      Set.indicator_of_mem hm', Set.indicator_of_mem hm, physicalSceneMaskedLostSourceMass]
    apply physicalScene_capped_min_le_of_common_loss
    · rw [havg, Measure.add_apply]
      exact add_le_add le_rfl (measure_mono hT₀)
    · rw [havg, Measure.add_apply]
      exact add_le_add le_rfl (measure_mono hT₁)
  · have hm' : s.1 ∉ Prod.fst ⁻¹' Emacro := hm
    simp only [physicalSceneMacroscopicAverageWitness, physicalSceneMaskedRetainedAverageWitness,
      Set.indicator_of_notMem hm', Set.indicator_of_notMem hm, zero_add, zero_le]

/-- Actual auxiliary cores are exhausted only after the original full scene
law is fixed. Their retained Taylor witnesses vanish on their own joint limits,
and their original lost-mass bounds then recover the SAME complete readout. -/
theorem ae_full_macroscopic_witness_zero_of_actual_projected_core_accuracy
    (Rfull : ProbabilityMeasure MacroScene) (Raux : ℕ → ProbabilityMeasure JointScene)
    (hprojection : ∀ m, (Raux m).map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (Emacro : Set (ι → ℝ)) (hEmacro : IsOpen Emacro)
    (T₀ T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (hT₀ : IsOpen T₀) (hT₁ : IsOpen T₁)
    (U : Set (ι → ℝ))
    (hT₀U : T₀ ⊆ {e | e.1.1 ∈ U}) (hT₁U : T₁ ⊆ {e | e.1.1 ∈ U})
    (hdecomposition : ∀ m, ∀ᵐ s ∂(Raux m : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hretained : ∀ m, ∀ᵐ s ∂(Raux m : Measure JointScene),
      physicalSceneMaskedRetainedAverageWitness base Emacro T₀ T₁ s = 0)
    (accuracy : ℕ → ℝ≥0∞) (haccuracy : Tendsto accuracy atTop (𝓝 0))
    (hlost : ∀ (m : ℕ) (level : ℝ≥0∞), 0 < level → level ≠ ⊤ →
      (Raux m : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base U s} ≤
        accuracy m / level) :
    ∀ᵐ s ∂(Rfull : Measure MacroScene),
      physicalSceneMacroscopicAverageWitness base Emacro T₀ T₁ s = 0 := by
  exact ae_eq_zero_of_projected_retained_zero_and_lost_accuracy Rfull Raux
    Prod.fst measurable_fst hprojection
    (physicalSceneMacroscopicAverageWitness base Emacro T₀ T₁)
    (lowerSemicontinuous_physicalSceneMacroscopicAverageWitness base hEmacro hT₀ hT₁).measurable
    (fun _ ↦ physicalSceneMaskedRetainedAverageWitness base Emacro T₀ T₁)
    (fun _ ↦ physicalSceneMaskedLostSourceMass base U)
    (fun m ↦ (hdecomposition m).mono fun s hs ↦
      physicalScene_full_witness_le_retained_add_lost base Emacro T₀ T₁ U hT₀U hT₁U s hs)
    hretained accuracy haccuracy hlost

end OTSelector.Reconstruction
