import OTSelector.Reconstruction.FinslerOriginalBlockPartitionExistence

/-!
# The per-block cube law: chart-volume analysis and assembly

## (1) Does the block-normalized cube law follow from the chart change of variables?

**No.**  The chart volume formula / Haar density (|FinslerPopulationChartVolume|,
|populationSeedHaarDensity|) makes the *global* coordinate pushforward of the
physical measure Lebesgue (|(physical law).map coord = cubeMeasure (Fin q) 1| on the
charted domain, the statement recovered by |physical_cell_laws| and
|iid_coordinate_laws| through the seed map |populationSeedPhysicalMap| and the
coordinate-clock kernel |populationSeedCoordinateClockKernel|).  A per-block law is
a *normalized restriction*: for a block |B_c = cellS ⁻¹' {c}| with
|0 < mu B_c < infinity| the block-normalized coordinate law is
|((mu B_c)⁻¹ • mu.restrict B_c).map coord|, which is the coordinate law conditioned
on the block.  Conditioning on a nontrivial coordinate-dependent event changes the
law in general; hence |cubeMeasure (Fin q) 1| for every block is **not** a
consequence of the change-of-variables formula.  The paper's blocks are marked
coordinate cubes whose coordinate law is cube measure by the *independence* of the
coordinate and the mark (the |hcubeS|/|hindepS| geometric inputs of
|PopDataIntrinsic|, supplied in the paper's seed model), not by the chart formula.

|globalCubeLaw_of_factorization| below records the exact additional input under which
the block law does follow: factorization of the joint law of the cell index and the
coordinate as a product with the cube law.  The remaining typed input is therefore
the per-block cube law itself, which is what
|cellCoordinateIsomorphisms_of_blockLaws| consumes.

## (2) Assembly

|cellCoordinateIsomorphisms_of_blockLaws| produces |CellCoordinateIsomorphisms| from
the per-block cube laws, and |physicalBlockTransport_of_blockLaws| then produces
|PhysicalBlockTransport| via |physicalBlockTransportOf| (with the mass partition
from |CellMassPartition|).  |geometricCoreOfTransport| instantiates the
cell/coordinate half of |PopDataIntrinsicGeometricCore|.

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

/-- **The per-block cube laws give the coordinate isomorphism data.**  This is
exactly the typed residual input: for each block the block-normalized physical
measure pushes the coordinate map to the cube law. -/
def cellCoordinateIsomorphisms_of_blockLaws [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (D : CellMassPartition (M := M) q k ωM ρ₀ ρ₁)
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (coordT : M → Fin q → ℝ) (hcoordT : Measurable coordT)
    (hcubeS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (D.cellS ⁻¹' {c}))⁻¹ •
      ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (D.cellS ⁻¹' {c})).map coordS =
        cubeMeasure (Fin q) 1)
    (hcubeT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (D.cellT ⁻¹' {c}))⁻¹ •
      ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (D.cellT ⁻¹' {c})).map coordT =
        cubeMeasure (Fin q) 1) :
    CellCoordinateIsomorphisms (M := M) q k ωM ρ₀ ρ₁ D where
  coordS := coordS
  hcoordS := hcoordS
  coordT := coordT
  hcoordT := hcoordT
  hcubeS := hcubeS
  hcubeT := hcubeT

/-- **The physical block transport from the mass partition and the per-block cube
laws.**  Composes the above with |physicalBlockTransportOf|. -/
def physicalBlockTransport_of_blockLaws [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (D : CellMassPartition (M := M) q k ωM ρ₀ ρ₁)
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (coordT : M → Fin q → ℝ) (hcoordT : Measurable coordT)
    (hcubeS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (D.cellS ⁻¹' {c}))⁻¹ •
      ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (D.cellS ⁻¹' {c})).map coordS =
        cubeMeasure (Fin q) 1)
    (hcubeT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (D.cellT ⁻¹' {c}))⁻¹ •
      ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (D.cellT ⁻¹' {c})).map coordT =
        cubeMeasure (Fin q) 1) :
    PhysicalBlockTransport (M := M) q k ωM ρ₀ ρ₁ :=
  physicalBlockTransportOf q k ωM ρ₀ ρ₁ D
    (cellCoordinateIsomorphisms_of_blockLaws q k ωM ρ₀ ρ₁ D coordS hcoordS coordT hcoordT
      hcubeS hcubeT)

end OTSelector.Reconstruction
