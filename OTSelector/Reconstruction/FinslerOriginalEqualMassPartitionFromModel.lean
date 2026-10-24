import OTSelector.Reconstruction.FinslerOriginalPopDataIntrinsicFromSeedModel
import OTSelector.Reconstruction.FinslerOriginalMeasurablePartitionProducer

/-!
# Equal-mass partitions for the physical laws by pullback of dyadic cells

## (1) The chain used

If the physical probability |mu| is the pushforward of the cube law along a
measurable chart map |Phi : M -> DyadicUnitCube q|,
|mu.map Phi = cubeMeasure (Fin q) 1| (the chart-coordinate form of the physical
model: the physical measure transported to the unit cube), then pulling back the
dyadic cells |dyadicCubeCell k : DyadicUnitCube q -> Fin q -> Fin (2^k+1)| gives a
fibre partition whose masses are the cube masses of the dyadic cells.  The remaining
input is the dyadic cell cube mass
|cubeMeasure (Fin q) 1 (dyadicCubeCell k ⁻¹' {c}) = ofReal (w c)|, which is the
equal-mass property of the dyadic partition.

## (2) Delivered

|equalMassPartition_of_coordinateLawMap|: constructs |EqualMassPartition mu (Fin q -> Fin (2^k+1)) w|
from a measurable coordinate map |psi : M -> Fin q -> R| with |mu.map psi = cubeMeasure (Fin q) 1|,
proving the fibre laws by |Measure.map_apply|.

## (3) Residual

* the pushforward law |mu.map psi = cubeMeasure (Fin q) 1| for
  |mu = physicalSourceProbability ωM rho_0| and |physicalTargetProbability ωM rho_1|
  -- the chart/coordinate transport of the physical model, not stated in the repo
  modules read;
* a measurable cell map on the cube together with its dyadic cell cube masses;
* the per-block cube laws |C : CellCoordinateIsomorphisms| needed by
  |geometricCore_of_seedParts| (FinslerOriginalPopDataIntrinsicFromSeedModel), which
  is not yet invoked.  No 'sorry', 'admit' or added axiom occurs.
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

/-- **Equal-mass partition by pullback of a cell map along a coordinate law map**:
if the physical law's pushforward along a measurable coordinate map |psi| is the
cube law, then pulling back any measurable cell map on the cube gives a fibre
partition with the cube fibre masses. -/
def equalMassPartition_of_coordinateLawMap [MeasurableSpace M] (q k : ℕ) (μ : Measure M)
    (w : (Fin q → Fin (2 ^ k + 1)) → ℝ)
    (ψ : M → Fin q → ℝ) (hψ : Measurable ψ)
    (cellOfCoord : (Fin q → ℝ) → (Fin q → Fin (2 ^ k + 1)))
    (hcellOfCoord : Measurable cellOfCoord)
    (hpush : μ.map ψ = cubeMeasure (Fin q) 1)
    (hcellmass : ∀ c, cubeMeasure (Fin q) 1 (cellOfCoord ⁻¹' {c}) = ENNReal.ofReal (w c)) :
    EqualMassPartition μ (Fin q → Fin (2 ^ k + 1)) w where
  cell := fun x => cellOfCoord (ψ x)
  hcell := hcellOfCoord.comp hψ
  hmass := fun c => by
    have hpre : (fun x => cellOfCoord (ψ x)) ⁻¹' {c}
        = ψ ⁻¹' (cellOfCoord ⁻¹' {c}) := rfl
    rw [hpre, (Measure.map_apply hψ (hcellOfCoord (measurableSet_singleton c))).symm, hpush, hcellmass c]

end OTSelector.Reconstruction
