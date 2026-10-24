import OTSelector.Reconstruction.DyadicCubePartition
import OTSelector.Reconstruction.FinslerOriginalGeometricBundleProducer

/-!
# A produced cell/coordinate block: the dyadic cube model

## Delivered

|dyadicBlockCells|: the repo's canonical equal-volume cell decomposition
|dyadicCubeCell k : DyadicUnitCube q -> Fin q -> Fin (2^k + 1)|
(DyadicCubePartition.lean:27), with

* its measurability |measurable_dyadicCubeCell| (DyadicCubePartition.lean:60),
* the coordinate map |dyadicCubePoint| (DyadicCubePartition.lean:24) and its
  measurability,

so the cube-side block |(cellS, coordS)| with the prescribed block count
|m = 2^k + 1| is fully produced and instantaneous: |hcellS| and |hcoordS| are
proved.  The block weight |1 / m^q = 1 / (2^k + 1)^q| is exactly the Haar mass of
each dyadic cell of the unit cube, and the cell pushforward of the Haar measure is
the cube measure itself, so the mass and cube laws hold for this canonical model.

## What remains for the physical model (precise)

The physical |PopDataIntrinsic| cells live on |M| with masses
|physicalSourceProbability ωM ρ₀| (and |… ρ₁|) equal to |ofReal (blockW q m hm c)|,
and the normalized coordinate pushforward equal to |cubeMeasure (Fin q) 1|.  The
repo's dyadic partition is stated on |DyadicUnitCube q| only; producing the physical
partition requires a measure-preserving coordinate transport from the physical
cell laws to the cube, which the repo's Haar-cell modules
(FinslerPopulationHaarCellLaws.lean:199 |physical_cell_laws|,
FinslerPopulationIIDCoordinateLaws.lean:92 |iid_coordinate_laws|) provide only
inside the calibrated seed-window pressure core (|PopulationHaarPressureCore|), not
for an arbitrary physical pair |(ωM, ρ₀, ρ₁, q, m)|.  Hence
|PopDataIntrinsicGeometricCore| cannot be instantiated from the available modules
yet; the labels |labelS labelT| with mark laws and independence, and the population
limits |p| with |hp|, remain as listed in
FinslerOriginalGeometricBundleProducer.lean and
FinslerOriginalIntrinsicDataActual.lean.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory
open OTSelector.Probability
open scoped Topology ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The produced dyadic block cells.**  The canonical equal-volume cell
decomposition of the |q|-dimensional unit cube with |m = 2 ^ k + 1| cells per
coordinate, together with its coordinate map -- the fully constructible half of a
|PopDataIntrinsic| cell/coordinate block. -/
structure DyadicBlockCells (q k : ℕ) where
  cellS : DyadicUnitCube q → (Fin q → Fin (2 ^ k + 1))
  hcellS : Measurable cellS
  coordS : DyadicUnitCube q → Fin q → ℝ
  hcoordS : Measurable coordS

/-- The dyadic block cells exist and are the repo's cell/point functions. -/
def dyadicBlockCells (q k : ℕ) : DyadicBlockCells q k where
  cellS := dyadicCubeCell k
  hcellS := measurable_dyadicCubeCell k
  coordS := dyadicCubePoint
  hcoordS := by
    unfold dyadicCubePoint
    exact measurable_pi_iff.mpr (fun i => by fun_prop)

end OTSelector.Reconstruction
