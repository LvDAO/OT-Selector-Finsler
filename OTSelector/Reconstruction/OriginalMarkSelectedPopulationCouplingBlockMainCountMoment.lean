import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockMainCountMomentLaw
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocksSets
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts
import OTSelector.Probability.PoissonCountDiscrepancy

/-! Actual original main-input block discrepancies have square-root volume
expectation, directly on the same Q scene law. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- Equal genuine block masses give the sharp square-root-volume discrepancy
bound for the unchanged main scene, including zero-volume or null blocks. -/
theorem LegalWeightedStationaryPoissonMatching.originalMainPhysicalBlockCount_abs_sub_integrable_and_integral_le
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hbal : α S = β T) :
    Integrable (fun scene ↦ |(originalMainPhysicalBlockCount K S 0 scene : ℝ) -
      (originalMainPhysicalBlockCount K T 1 scene : ℝ)|) (Q.law : Measure _) ∧
    (∫ scene, |(originalMainPhysicalBlockCount K S 0 scene : ℝ) -
      (originalMainPhysicalBlockCount K T 1 scene : ℝ)| ∂(Q.law : Measure _)) ≤
        Real.sqrt (2 * volume.real K * α.real S) := by
  let a := (volume K).toNNReal * (α S).toNNReal
  have hlaw := Q.hasLaw_originalMainPhysicalBlockCount_pair hK hS hT
  rw [← hbal] at hlaw
  have hm : MeasurePreserving (fun scene ↦
      (originalMainPhysicalBlockCount K S 0 scene, originalMainPhysicalBlockCount K T 1 scene))
      (Q.law : Measure _) ((poissonMeasure a).prod (poissonMeasure a)) :=
    ⟨(measurable_originalMainPhysicalBlockCount hK.measurableSet hS 0).prodMk
      (measurable_originalMainPhysicalBlockCount hK.measurableSet hT 1), hlaw.map_eq⟩
  have hI : Integrable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|)
      ((poissonMeasure a).prod (poissonMeasure a)) :=
    (((integrable_id_poissonMeasure a).comp_fst _).sub
      ((integrable_id_poissonMeasure a).comp_snd _)).abs
  have hf : Measurable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ) - (z.2 : ℝ)|) := by fun_prop
  refine ⟨hm.integrable_comp_of_integrable hI, ?_⟩
  have heq := hlaw.integral_comp hf.aestronglyMeasurable
  change (∫ scene, |(originalMainPhysicalBlockCount K S 0 scene : ℝ) -
    (originalMainPhysicalBlockCount K T 1 scene : ℝ)| ∂(Q.law : Measure _)) = _ at heq
  rw [heq]
  convert integral_abs_sub_poissonPair_le a using 1
  simp only [a, NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, measureReal_def]
  congr 1
  ring

/-- On the actual same-frame physical cube and every actual Hall block, balance
comes from the block construction itself. No count, variance or rate law is an input. -/
theorem LegalWeightedStationaryPoissonMatching.originalMainOrientedClockSlabBlock_count_discrepancy
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (G : OriginalStageClockGrid) (b : G.ClockSlabBlock α β) :
    let K := originalCenteredPhysicalCubeRegion frame (2 * R)
    Integrable (fun scene ↦
      |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β b) 0 scene : ℝ) -
        (originalMainPhysicalBlockCount K (G.targetBlockCell α β b) 1 scene : ℝ)|)
      (Q.law : Measure _) ∧
    (∫ scene, |(originalMainPhysicalBlockCount K (G.sourceBlockCell α β b) 0 scene : ℝ) -
      (originalMainPhysicalBlockCount K (G.targetBlockCell α β b) 1 scene : ℝ)|
      ∂(Q.law : Measure _)) ≤
        Real.sqrt (2 * volume.real K * α.real (G.sourceBlockCell α β b)) := by
  exact Q.originalMainPhysicalBlockCount_abs_sub_integrable_and_integral_le
    (isCompact_originalStagePhysicalCube frame (2 * R))
    (G.blockCells_measurable b).1 (G.blockCells_measurable b).2
    ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top α _) (measure_ne_top β _)).mp
      (G.block_mass_balance b))

end OTSelector.Reconstruction
