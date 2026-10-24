import OTSelector.Reconstruction.FinslerOriginalEqualMassPartitionFromModel

/-!
# Physical chart coordinates: the typed input for the equal-mass partitions

## (1) The residual of FinslerOriginalEqualMassPartitionFromModel

|equalMassPartition_of_coordinateLawMap| consumes a measurable coordinate map
|psi : M -> Fin q -> R| whose pushforward of the physical probability is the cube
law |cubeMeasure (Fin q) 1|, together with a measurable cube cell map and its cell
masses.  The physical probabilities are
|physicalSourceProbability omegaM rho_0| and |physicalTargetProbability omegaM rho_1|
(OTSelector/Limit/PhysicalSelectorWrapper.lean:18,25).  Their pushforward laws are
supplied inside the seed model only through the seed recovery theorems
(|physical_cell_laws|: a physical map applied to an intensity-times-clock-kernel
measure recovers |eta_0.restrict (a ⁻¹' L)|; |iid_coordinate_laws|: the iid product
version).  Those are inverse-recovery statements (measure equals a pushforward),
not a global cube-coordinate statement: no repo module exhibits a measurable
|psi : M -> Fin q -> R| with |(physicalSourceProbability omegaM rho_0).map psi =
cubeMeasure (Fin q) 1|.  Hence (1) the map and its pushforward proof cannot be
produced from the modules read; they are isolated below as
|PhysicalChartCoordinates| (fields |psiS pushS psiT pushT| plus the cube cell map
and cell masses).

## (2) The construction delivered

|equalMassPartitions_of_chartCoordinates|: given |PhysicalChartCoordinates|, produces
both |EqualMassPartition|s (source and target) by applying
|equalMassPartition_of_coordinateLawMap| twice.  Feeding them to
|cellMassPartition_of_equalMass| needs |hw : w c = ((blockW ...) : R)|, and
|geometricCore_of_seedParts| additionally needs |CellCoordinateIsomorphisms| (the
per-block cube laws), which remain the residual:
no module states the per-block normalized coordinate law.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The chart-coordinate input**: measurable coordinates for both physical laws
whose pushforwards are the cube law, plus the measurable cell map and its masses. -/
structure PhysicalChartCoordinates [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (w : (Fin q → Fin (2 ^ k + 1)) → ℝ) where
  ψS : M → Fin q → ℝ
  hψS : Measurable ψS
  pushS : (physicalSourceProbability ωM ρ₀ : Measure M).map ψS = cubeMeasure (Fin q) 1
  ψT : M → Fin q → ℝ
  hψT : Measurable ψT
  pushT : (physicalTargetProbability ωM ρ₁ : Measure M).map ψT = cubeMeasure (Fin q) 1
  cellOfCoord : (Fin q → ℝ) → (Fin q → Fin (2 ^ k + 1))
  hcellOfCoord : Measurable cellOfCoord
  cellmass : ∀ c, cubeMeasure (Fin q) 1 (cellOfCoord ⁻¹' {c}) = ENNReal.ofReal (w c)

/-- **Both equal-mass partitions from the chart coordinates.** -/
def equalMassPartitions_of_chartCoordinates [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (w : (Fin q → Fin (2 ^ k + 1)) → ℝ)
    (P : PhysicalChartCoordinates q k ωM ρ₀ ρ₁ w) :
    EqualMassPartition (physicalSourceProbability ωM ρ₀ : Measure M)
        (Fin q → Fin (2 ^ k + 1)) w ×
    EqualMassPartition (physicalTargetProbability ωM ρ₁ : Measure M)
        (Fin q → Fin (2 ^ k + 1)) w :=
  ⟨equalMassPartition_of_coordinateLawMap q k _
      w P.ψS P.hψS P.cellOfCoord P.hcellOfCoord P.pushS P.cellmass,
    equalMassPartition_of_coordinateLawMap q k _
      w P.ψT P.hψT P.cellOfCoord P.hcellOfCoord P.pushT P.cellmass⟩

end OTSelector.Reconstruction
