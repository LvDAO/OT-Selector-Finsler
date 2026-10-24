import OTSelector.Reconstruction.MarkedStationaryValueLegalRandomGridSecondMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-!
# Original stationary finite-second-moment scenes lose vanishing grid energy

The original scene's mean edge measure is restricted only at its source unit
window. Its exact paired-mark pushforward is the same full-displacement Palm,
so the original Palm second moment supplies all required integrability. The
random-grid conclusion is then written as an expectation of the original
scene law, preserving every original target and its dependence.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryGridEnergyInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryGridEnergyPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The same original expected edge plan, restricted at its actual source
unit window while leaving its target completely unrestricted. -/
def legalMarkedSourceUnitMeanPlan (q : ℕ) (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    Measure (LegalMarkedPhysicalEdge q) :=
  (physicalSceneMeanPlan (legalMarkedInputPairLaw q Q :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))).restrict
      {e | e.1.1 ∈ palmUnitCube (Fin q)}

/-- The actual source-unit mean plan has precisely its own true paired-mark
Palm law, with every original scalar mark and full displacement retained. -/
theorem map_legalMarkedSourceUnitMeanPlan_pairMark (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    (legalMarkedSourceUnitMeanPlan q Q).map (fun e ↦ (physicalPairAnchor e).2) =
      legalMarkedJointPalm q Q := by
  refine Measure.ext_of_lintegral _ (fun f hf ↦ ?_)
  rw [lintegral_map hf measurable_physicalPairAnchor.snd]
  change (∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ palmUnitCube (Fin q)},
    f (physicalPairAnchor e).2 ∂physicalSceneMeanPlan (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) = _
  have h := setLIntegral_physicalSceneMeanPlan
    (legalMarkedInputPairLaw q Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q)
      (LegalMarkedPhysicalPoint q))) (hf.comp measurable_physicalPairAnchor.snd)
      (measurableSet_palmUnitCube (Fin q))
  simp only [Function.comp_def] at h
  exact h.trans (lintegral_cubePalm_physicalScenePairCampbell _ hf).symm

instance legalWeightedStationaryPoissonMatchingSourceUnitMeanPlanProbability
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    IsProbabilityMeasure (legalMarkedSourceUnitMeanPlan q M.law) := by
  have : IsProbabilityMeasure ((legalMarkedSourceUnitMeanPlan q M.law).map
      (fun e ↦ (physicalPairAnchor e).2)) := by
    rw [map_legalMarkedSourceUnitMeanPlan_pairMark]
    exact M.palm_probability
  exact Measure.isProbabilityMeasure_of_map (fun e ↦ (physicalPairAnchor e).2)

/-- The original Palm second moment gives the moment of the exact original
source-unit mean plan, without any properness assumption on the target map. -/
theorem integrable_sourceUnitMeanPlan_displacement_sq
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hM : Integrable (fun m ↦ ‖m.2‖ ^ 2) (legalMarkedJointPalm q M.law)) :
    Integrable (fun e : LegalMarkedPhysicalEdge q ↦ ‖e.2.1 - e.1.1‖ ^ 2)
      (legalMarkedSourceUnitMeanPlan q M.law) := by
  have h : Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ ‖m.2‖ ^ 2)
      ((legalMarkedSourceUnitMeanPlan q M.law).map (fun e ↦ (physicalPairAnchor e).2)) := by
    rw [map_legalMarkedSourceUnitMeanPlan_pairMark]
    exact hM
  exact h.comp_measurable measurable_physicalPairAnchor.snd

/-- An original stationary finite-second-moment matching loses vanishing
quadratic energy when the independent translated grid spacing grows. This is
an actual scene expectation, not an iid description of its selected ports. -/
theorem tendsto_original_stationary_shiftedGrid_crossing_energy_zero
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hM : Integrable (fun m ↦ ‖m.2‖ ^ 2) (legalMarkedJointPalm q M.law))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ u, ∫⁻ scene,
        ∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ palmUnitCube (Fin q)},
          (if shiftedGridCells (R n) u e.1.1 ≠ shiftedGridCells (R n) u e.2.1
            then ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2) else 0)
          ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q))
        ∂(legalMarkedInputPairLaw q M.law : Measure
          (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  have hlim := tendsto_lintegral_shiftedGrid_crossing_squared_energy_zero q
    (legalMarkedSourceUnitMeanPlan q M.law) (integrable_sourceUnitMeanPlan_displacement_sq M hM)
    R hRpos hR
  refine hlim.congr' (Filter.Eventually.of_forall (fun n ↦ ?_))
  apply lintegral_congr_ae
  filter_upwards with u
  have hs : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ shiftedGridCells (R n) u e.1.1) :=
    (measurable_joint_shiftedGridCells (R n)).comp (measurable_const.prodMk measurable_fst.fst)
  have ht : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ shiftedGridCells (R n) u e.2.1) :=
    (measurable_joint_shiftedGridCells (R n)).comp (measurable_const.prodMk measurable_snd.fst)
  have hw : Measurable (fun e : LegalMarkedPhysicalEdge q ↦
      if shiftedGridCells (R n) u e.1.1 ≠ shiftedGridCells (R n) u e.2.1
        then ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2) else 0) :=
    (((measurable_snd.fst.sub measurable_fst.fst).norm.pow_const 2).ennreal_ofReal).ite
      (measurableSet_eq_fun hs ht).compl measurable_const
  exact setLIntegral_physicalSceneMeanPlan _ hw (measurableSet_palmUnitCube (Fin q))

end OTSelector.Reconstruction
