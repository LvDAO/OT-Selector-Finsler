import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedStrictClockExhaustion

/-! The same exact decomposition transfers original full clock nullness and gap to retained plans. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local instance retainedStrictClockStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance retainedStrictClockConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance retainedStrictClockConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance retainedStrictClockConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance retainedStrictClockPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Exact full = retained + lost makes the actual retained average a submeasure
of the SAME full average. -/
theorem physicalScene_retainedAverage_le_full_of_decomposition
    (s : JointScene) (hs : s ∈ physicalSceneMaskedDecompositionCarrier base) :
    (LocalFiniteMeasure.cavityAverage s.2.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) ≤
      (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure _) := by
  rw [show s.1.2.1 = physicalScenePairSum s.2 from hs,
    physicalScene_cavityAverage_pairSum]
  exact le_add_of_nonneg_right bot_le

/-- Rational endpoint nullness and the original positive full-plan clock gap
put the actual retained average strictly inside its selected original window.
The rational screen only needs to be chosen below that already produced gap. -/
theorem physicalScene_retained_strictClock_of_full_null_and_gap
    (s : JointScene) (hs : s ∈ physicalSceneMaskedDecompositionCarrier base)
    (q : RationalScalarPairWindow) (gap : ℝ) (hscreen : (q.val.2.2 : ℝ) < gap)
    (hnull : ∀ q : ℚ, (LocalFiniteMeasure.cavityAverage s.1.2.1 :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      {e | e.1.2 = (q : ℝ) ∨ e.2.2 = (q : ℝ)} = 0)
    (hgap : ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.1.2.1 :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), gap ≤ e.2.2 - e.1.2)
    (hclosed : ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), (e.1.2, e.2.2) ∈ q.region) :
    ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e ∈ physicalSceneStrictClockRegion q := by
  have hac := Measure.absolutelyContinuous_of_le
    (physicalScene_retainedAverage_le_full_of_decomposition base s hs)
  have hnot (r : ℚ) : ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 :
      Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
      e.1.2 ≠ (r : ℝ) ∧ e.2.2 ≠ (r : ℝ) := by
    have hz := hac (hnull r)
    exact (measure_eq_zero_iff_ae_notMem.mp hz).mono fun _ he ↦ not_or.mp he
  filter_upwards [hclosed, hnot q.val.1, hnot q.val.2.1, hac.ae_le hgap]
    with e he hlo hhi hgap
  refine ⟨⟨lt_of_le_of_ne he.1.1.1 (Ne.symm hlo.1),
    lt_of_le_of_ne he.1.1.2 hhi.1⟩,
    ⟨lt_of_le_of_ne he.1.2.1 (Ne.symm hlo.2),
      lt_of_le_of_ne he.1.2.2 hhi.2⟩, hscreen.trans_le hgap⟩
end OTSelector.Reconstruction
