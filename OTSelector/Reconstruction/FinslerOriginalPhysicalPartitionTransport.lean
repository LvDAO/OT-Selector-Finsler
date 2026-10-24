import OTSelector.Reconstruction.FinslerOriginalGeometricBundleProducer

/-!
# The physical partition transport (F13)

## The repo's physical Haar cell laws

|PopulationHaarPressureCore.physical_cell_laws| (FinslerPopulationHaarCellLaws.lean:199)
states: for a measurable subset |L| of a coefficient's roots and the induced
intensity |((kappa i).restrict (R '' L)).withDensity (populationSeedPieceHaarDensity ...)|,
mapping by the actual seed map |populationSeedPhysicalMap S| after the coordinate-clock
kernel recovers the physical laws:
|(intensity tensor coordinateClockKernel).map (populationSeedPhysicalMap S) =
 eta_0.restrict (a ⁻¹' L)| and likewise for |eta_1|.  Its companion
|iid_coordinate_laws| (FinslerPopulationIIDCoordinateLaws.lean:92) gives the same
statement for iid products.  Neither statement is a block partition of the physical
measure into equal-mass cells: it recovers the original physical law on a measurable
seed domain, so it does not supply the mass law |mu (cellS ⁻¹' {c}) = ofReal (blockW c)|
nor the cube law of the normalized coordinate pushforward.

## The reduction

The cell/coordinate half of |PopDataIntrinsicGeometricCore| is therefore reduced below
to a **single** missing measurable transport object |PhysicalBlockTransport|: the
cells, their measurability and the mass laws, the coordinate maps and the cube laws
(types copied from the core).  Once such a transport is produced (a partition of |M|
with block-weight masses and normalized coordinate pushforward the cube measure),
|geometricCoreOfTransport| instantiates the core immediately.

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

/-- **The single missing transport object**: a physical cell decomposition into the
block-weight masses together with cube-law coordinate maps -- exactly the
cell/coordinate half of |PopDataIntrinsicGeometricCore| at |m = 2 ^ k + 1|, stated
without any proof obligations left open. -/
structure PhysicalBlockTransport [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))] where
  cellS : M → (Fin q → Fin (2 ^ k + 1))
  hcellS : Measurable cellS
  cellT : M → (Fin q → Fin (2 ^ k + 1))
  hcellT : Measurable cellT
  hmassS : ∀ c, ((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}) =
    ENNReal.ofReal ((blockW q (2 ^ k + 1) (by positivity) c : unitInterval) : ℝ)
  hmassT : ∀ c, ((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}) =
    ENNReal.ofReal ((blockW q (2 ^ k + 1) (by positivity) c : unitInterval) : ℝ)
  coordS : M → Fin q → ℝ
  hcoordS : Measurable coordS
  coordT : M → Fin q → ℝ
  hcoordT : Measurable coordT
  hcubeS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}))⁻¹ •
    ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (cellS ⁻¹' {c})).map coordS =
      cubeMeasure (Fin q) 1
  hcubeT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}))⁻¹ •
    ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (cellT ⁻¹' {c})).map coordT =
      cubeMeasure (Fin q) 1

/-- **The cell/coordinate half of |PopDataIntrinsicGeometricCore|, instantiated
from the transport.** -/
def geometricCoreOfTransport [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (T : PhysicalBlockTransport (M := M) q k ωM ρ₀ ρ₁) :
    PopDataIntrinsicGeometricCore (M := M) q (2 ^ k + 1) (by positivity) ωM ρ₀ ρ₁ where
  cellS := T.cellS
  hcellS := T.hcellS
  cellT := T.cellT
  hcellT := T.hcellT
  hmassS := T.hmassS
  hmassT := T.hmassT
  coordS := T.coordS
  hcoordS := T.hcoordS
  coordT := T.coordT
  hcoordT := T.hcoordT

end OTSelector.Reconstruction
