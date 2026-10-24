import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockCountMoment
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocksSets

/-! Reserve fluctuation on the actual source-Ico / target-Ioc Hall blocks.
The equal count intensity is derived from the real block construction. -/

open Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Every actual clock block, including a zero block, has the genuine reserve
count discrepancy rate. Original observed indices and original clocks are used. -/
theorem OriginalStageClockGrid.originalReserveObservedBlockCount_abs_sub_integrable_and_integral_le
    {q : ℕ} (G : OriginalStageClockGrid) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (rate : ℝ≥0)
    (b : G.ClockSlabBlock μ ν) :
    Integrable (fun z ↦
      |(originalReserveObservedBlockCount (q := q) (G.sourceBlockCell μ ν b) z.1 : ℝ) -
        (originalReserveObservedBlockCount (G.targetBlockCell μ ν b) z.2 : ℝ)|)
      (twoMarkedCloudLaw q ℝ ℝ μ ν rate) ∧
    (∫ z, |(originalReserveObservedBlockCount (q := q) (G.sourceBlockCell μ ν b) z.1 : ℝ) -
      (originalReserveObservedBlockCount (G.targetBlockCell μ ν b) z.2 : ℝ)|
      ∂twoMarkedCloudLaw q ℝ ℝ μ ν rate) ≤
        Real.sqrt (2 * (rate : ℝ) * μ.real (G.sourceBlockCell μ ν b)) := by
  exact OTSelector.Probability.originalReserveObservedBlockCount_abs_sub_integrable_and_integral_le
    μ ν rate (G.blockCells_measurable b).1 (G.blockCells_measurable b).2
    ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp
      (G.block_mass_balance b))

end OTSelector.Reconstruction
