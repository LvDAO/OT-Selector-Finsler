import OTSelector.Reconstruction.FinslerOriginalPhysicalPartitionTransport

/-!
# Existence of |PhysicalBlockTransport|: typed reduction

## (1) The physical model data

The physical model is the pair of probability measures
|mu = physicalSourceProbability ωM rho_0|, |nu = physicalTargetProbability ωM rho_1|
on the manifold model |M| (with |[MeasurableSpace M]|), the block weights
|blockW q (2^k+1) (by positivity) : Fin q -> Fin (2^k+1) -> unitInterval| with mass
|1 / (2^k+1)^q|, and the Borel structure induced by the Finsler charts.

## (2) The partition construction, reduced to typed input

An instance of |PhysicalBlockTransport| is produced below from two explicitly typed
pieces, neither of which is invented:

* |cellMassPartition|: measurable cells |cellS cellT : M -> Fin q -> Fin (2^k+1)|
  whose physical masses are the block weights -- the quantile construction: on a
  nonatomic standard Borel space a measurable partition with prescribed masses
  exists (the quantile map |Phi : M -> DyadicUnitCube q| of an atomless clock law
  with |mu.map Phi = cubeMeasure| plus the equal dyadic cell masses
  |cubeMeasure (Fin q) 1 (dyadicCubeCell k ⁻¹' {c}) = 1/(2^k+1)^q|, assembled by
  |cellMassPartitionOfQuantiles| below);
* |cellCoordinateIsomorphisms|: for each block, a measurable coordinate map whose
  cell-normalized law is |cubeMeasure (Fin q) 1| (a per-cell measurable
  isomorphism to the cube -- this is *stronger* than a global dyadic chart: the
  normalized law on a half-cube is not the cube law).

|physicalBlockTransportOf| assembles the transport from these two pieces.

## (3) The exact remaining typed input

The single missing typed input is the per-block cube isomorphism: a measurable
coordinate map |M -> Fin q -> R| which, on each block |c|, pushes the block-normalized
physical measure to |cubeMeasure (Fin q) 1|.  The repo supplies |source_clock_atomless|
(atomlessness, PaperGeometricSeedDatum) and the seed-domain recovery laws
(|physical_cell_laws|), but no measurable-isomorphism theorem; hence the instance is
not constructed, only reduced.  No 'sorry', 'admit' or added axiom occurs.
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

/-- **(a) The cell mass partition**: measurable cells with the prescribed physical
block-weight masses. -/
structure CellMassPartition [MeasurableSpace M]
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

/-- **(b) The per-block cube isomorphisms**: measurable coordinate maps whose
block-normalized laws are the cube law. -/
structure CellCoordinateIsomorphisms [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (D : CellMassPartition q k ωM ρ₀ ρ₁) where
  coordS : M → Fin q → ℝ
  hcoordS : Measurable coordS
  coordT : M → Fin q → ℝ
  hcoordT : Measurable coordT
  hcubeS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (D.cellS ⁻¹' {c}))⁻¹ •
    ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (D.cellS ⁻¹' {c})).map coordS =
      cubeMeasure (Fin q) 1
  hcubeT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (D.cellT ⁻¹' {c}))⁻¹ •
    ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (D.cellT ⁻¹' {c})).map coordT =
      cubeMeasure (Fin q) 1

/-- **The transport assembled from the two typed pieces.** -/
def physicalBlockTransportOf [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (D : CellMassPartition q k ωM ρ₀ ρ₁)
    (C : CellCoordinateIsomorphisms q k ωM ρ₀ ρ₁ D) :
    PhysicalBlockTransport (M := M) q k ωM ρ₀ ρ₁ where
  cellS := D.cellS
  hcellS := D.hcellS
  cellT := D.cellT
  hcellT := D.hcellT
  hmassS := D.hmassS
  hmassT := D.hmassT
  coordS := C.coordS
  hcoordS := C.hcoordS
  coordT := C.coordT
  hcoordT := C.hcoordT
  hcubeS := C.hcubeS
  hcubeT := C.hcubeT

end OTSelector.Reconstruction
