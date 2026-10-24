import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The original unit-source-window Palm readout on the original scene

A canonical S-finite scene kernel retains both clocks and the full actual
edge displacement in the source unit cube. Its mean is the actual true Palm,
so every integrable Palm observable has an integrable original scene readout.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalScenePalmReadoutInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalScenePalmReadoutPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual original full-displacement pair Palm kernel in one physical
source cube; no scene event or input coordinate is forgotten. -/
def legalMarkedSceneUnitPalmKernel (q : ℕ) :
    Kernel (LegalMarkedOptimalInputScene q) (PhysicalPairPalmMark (Fin q)) :=
  ((physicalScenePairKernel.comap Prod.fst measurable_fst).restrict
    ((measurableSet_palmUnitCube (Fin q)).prod MeasurableSet.univ)).map Prod.snd

instance legalMarkedSceneUnitPalmKernel_isSFinite (q : ℕ) :
    IsSFiniteKernel (legalMarkedSceneUnitPalmKernel q) := by
  unfold legalMarkedSceneUnitPalmKernel
  infer_instance

@[simp]
theorem legalMarkedSceneUnitPalmKernel_apply (q : ℕ) (s : LegalMarkedOptimalInputScene q) :
    legalMarkedSceneUnitPalmKernel q s =
      cubePalm (Fin q) (physicalScenePairKernel s.1) := by
  rw [legalMarkedSceneUnitPalmKernel, Kernel.map_apply _ measurable_snd,
    Kernel.restrict_apply]
  rfl

/-- The mean of the actual scene unit kernel is precisely its own true Palm. -/
theorem legalMarkedJointPalm_eq_unitPalmKernel_comp
    {q : ℕ} (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    legalMarkedJointPalm q Q =
      legalMarkedSceneUnitPalmKernel q ∘ₘ (Q : Measure (LegalMarkedOptimalInputScene q)) := by
  ext B hB
  rw [Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
    legalMarkedJointPalm, cubePalm_apply (Fin q) _ hB, physicalScenePairCampbell,
    Measure.bind_apply ((measurableSet_palmUnitCube (Fin q)).prod hB)
      (Kernel.measurable _).aemeasurable]
  change (∫⁻ scene, physicalScenePairKernel scene (palmUnitCube (Fin q) ×ˢ B)
    ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst) = _
  rw [lintegral_map (Kernel.measurable_coe _ ((measurableSet_palmUnitCube (Fin q)).prod hB))
    measurable_fst]
  apply lintegral_congr
  intro s
  rw [legalMarkedSceneUnitPalmKernel_apply, cubePalm_apply (Fin q) _ hB]

/-- An actual unit-window scene observable of a full-displacement Palm test. -/
def legalMarkedScenePalmReadout {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q : ℕ) (f : PhysicalPairPalmMark (Fin q) → V) (s : LegalMarkedOptimalInputScene q) : V :=
  ∫ m, f m ∂legalMarkedSceneUnitPalmKernel q s

/-- Actual integrable Palm observables give integrable original scene readouts. -/
theorem integrable_legalMarkedScenePalmReadout
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {q : ℕ} (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    {f : PhysicalPairPalmMark (Fin q) → V} (hf : Integrable f (legalMarkedJointPalm q Q)) :
    Integrable (legalMarkedScenePalmReadout q f)
      (Q : Measure (LegalMarkedOptimalInputScene q)) := by
  change Integrable (fun s ↦ ∫ m, f m ∂legalMarkedSceneUnitPalmKernel q s) _
  rw [legalMarkedJointPalm_eq_unitPalmKernel_comp, Measure.comp_eq_comp_const_apply] at hf
  simpa only [Kernel.const_apply] using hf.integral_comp

/-- The actual original scene readout integrates to its own true Palm test. -/
theorem integral_legalMarkedScenePalmReadout
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {q : ℕ} (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    {f : PhysicalPairPalmMark (Fin q) → V} (hf : Integrable f (legalMarkedJointPalm q Q)) :
    (∫ s, legalMarkedScenePalmReadout q f s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ m, f m ∂legalMarkedJointPalm q Q := by
  rw [legalMarkedJointPalm_eq_unitPalmKernel_comp, Measure.comp_eq_comp_const_apply] at hf ⊢
  simpa only [Kernel.const_apply, legalMarkedScenePalmReadout] using (Kernel.integral_comp hf).symm

/-- The genuine weighted value is the expectation of one literal original
scene observable, suitable for conditioning on invariant scene events. -/
theorem LegalWeightedStationaryPoissonMatching.value_eq_integral_scenePalmReadout
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) :
    M.value t = ∫ s, legalMarkedScenePalmReadout q
      (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) s
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hI : Integrable (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
      (legalMarkedJointPalm q M.law) :=
    M.kinetic_integrable.add (M.probe_integrable.const_mul t)
  rw [integral_legalMarkedScenePalmReadout M.law hI,
    integral_add M.kinetic_integrable (M.probe_integrable.const_mul t), integral_const_mul]
  rfl

end OTSelector.Reconstruction
