import OTSelector.Transport.CyclicMonotonicity.StrictCyclePairMeasure
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedStrictClock

/-! The actual retained clock and support certificates kill fixed original-cost cycle witnesses. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local instance retainedCyclePairStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance retainedCyclePairConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance retainedCyclePairConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance retainedCyclePairConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance retainedCyclePairPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- A legal gap test retaining all actual spatial positions and clocks. -/
def physicalSceneClockGapRegion (gap : ℝ) : Set Edge :=
  {e | gap < e.2.2 - e.1.2}

theorem isOpen_physicalSceneClockGapRegion (gap : ℝ) :
    IsOpen (physicalSceneClockGapRegion (ι := ι) gap) :=
  isOpen_lt continuous_const (continuous_snd.snd.sub continuous_fst.snd)

/-- The endpoints of two carried strict-window edges remain in the original
scalar interval. A crossed positive gap above the core screen is therefore legal. -/
theorem physicalSceneStrictClock_cross_of_gap
    (q : RationalScalarPairWindow) (g : ℝ) (hscreen : (q.val.2.2 : ℝ) ≤ g)
    (e e' : Edge) (he : e ∈ physicalSceneStrictClockRegion q)
    (he' : e' ∈ physicalSceneStrictClockRegion q)
    (hc : (e.1, e'.2) ∈ physicalSceneClockGapRegion g)
    (hc' : (e'.1, e.2) ∈ physicalSceneClockGapRegion g) :
    (e.1, e'.2) ∈ physicalSceneStrictClockRegion q ∧
      (e'.1, e.2) ∈ physicalSceneStrictClockRegion q :=
  ⟨⟨he.1, he'.2.1, hscreen.trans_lt hc⟩,
    ⟨he'.1, he.2.1, hscreen.trans_lt hc'⟩⟩

/-- Original full clock nullness, original full legality, literal retained
window concentration and the produced retained support certificate imply zero
strict-cycle product mass. The event tests the same actual varying cost. -/
theorem physicalScene_retainedCyclePairMass_zero_of_original_certificates
    (c : JointScene → Point → Point → ℝ)
    (hc : Measurable (fun p : JointScene × Edge ↦ c p.1 p.2.1 p.2.2))
    (K : Set Edge) (hK : MeasurableSet K)
    (s : JointScene) (hs : s ∈ physicalSceneMaskedDecompositionCarrier base)
    (q : RationalScalarPairWindow) (gap g margin : ℝ)
    (hscreenGap : (q.val.2.2 : ℝ) < gap) (hscreenCycle : (q.val.2.2 : ℝ) ≤ g)
    (hmargin : 0 ≤ margin)
    (hnull : ∀ r : ℚ,
      (s.1.2.1.1 : Measure Edge) {e | e.1.2 = (r : ℝ) ∨ e.2.2 = (r : ℝ)} = 0 ∧
      (s.1.2.1.2 : Measure Edge) {e | e.1.2 = (r : ℝ) ∨ e.2.2 = (r : ℝ)} = 0)
    (hgap : ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge),
      gap ≤ e.2.2 - e.1.2)
    (hclosed :
      (s.2.1.1 : Measure Edge) {e | (e.1.2, e.2.2) ∉ q.region} = 0 ∧
      (s.2.1.2 : Measure Edge) {e | (e.1.2, e.2.2) ∉ q.region} = 0)
    (hmono : IsTwoCycleMonotoneOn (c s) (physicalSceneStrictClockRegion q)
      ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).support ∩
        physicalSceneStrictClockRegion q)) :
    physicalSceneCyclePairMass
      (fun s : JointScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
      (physicalSceneStrictCyclePairEvent c (physicalSceneClockGapRegion g) K margin) s = 0 := by
  have hnullAvg (r : ℚ) : (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge)
      {e | e.1.2 = (r : ℝ) ∨ e.2.2 = (r : ℝ)} = 0 := by
    rw [LocalFiniteMeasure.coe_cavityAverage, Measure.smul_apply, Measure.add_apply,
      (hnull r).1, (hnull r).2]
    simp
  have hclosedAvg : ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
      (e.1.2, e.2.2) ∈ q.region := by
    apply ae_iff.mpr
    rw [LocalFiniteMeasure.coe_cavityAverage, Measure.smul_apply, Measure.add_apply,
      hclosed.1, hclosed.2]
    simp
  have hstrict := physicalScene_retained_strictClock_of_full_null_and_gap base
    s hs q gap hscreenGap hnullAvg hgap hclosedAvg
  exact physicalSceneStrictCyclePairMass_zero_of_carried_twoCycle _ c hc
    (isOpen_physicalSceneClockGapRegion g).measurableSet hK hmargin s
    (physicalSceneStrictClockRegion q) hstrict hmono
    (physicalSceneStrictClock_cross_of_gap q g hscreenCycle)
end OTSelector.Reconstruction
