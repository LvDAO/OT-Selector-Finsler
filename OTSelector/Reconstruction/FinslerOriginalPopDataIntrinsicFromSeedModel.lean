import OTSelector.Reconstruction.FinslerOriginalEqualMassPartition

/-!
# The geometric core of |PopDataIntrinsic| from the paper seed-model parts

## (1) What the repo seed model supplies

The paper seed model (main.tex:355 atlas, :1147-1185 seed) is formalized by the
calibrated seed windows and their recovery/law statements:
|PopulationHaarPressureCore.physical_cell_laws| (FinslerPopulationHaarCellLaws.lean:199)
and |iid_coordinate_laws| (FinslerPopulationIIDCoordinateLaws.lean:92) give the
seed-domain physical recovery laws; |source_clock_atomless| / |target_clock_atomless|
(of the paper geometric hypotheses) supply atomlessness of the clock laws.  None of
these fields is itself a block partition of the physical measure into blocks of mass
|ofReal (blockW q (2^k+1) c)| nor a per-block cube law: as established in
FinslerOriginalPerBlockCubeLaw, the chart change-of-variables gives only the GLOBAL
coordinate law, and the per-block cube law is the (paper's) independence input.

## (2) The composition

|geometricCore_of_seedParts| assembles |PopDataIntrinsicGeometricCore| from exactly
two typed parts:

* |Dμ Dν : EqualMassPartition (physicalSourceProbability ωM ρ₀ / physicalTargetProbability ωM ρ₁)
  (Fin q → Fin (2^k+1)) w| with |hw : w c = ((blockW q (2^k+1) (by positivity) c : unitInterval) : ℝ)|
  (FinslerOriginalEqualMassPartition: the mass half |CellMassPartition|);
* |C : CellCoordinateIsomorphisms q k ωM ρ₀ ρ₁| over that mass partition
  (FinslerOriginalBlockPartitionExistence / FinslerOriginalPerBlockCubeLaw: the
  per-block cube laws);

via |physicalBlockTransportOf| (FinslerOriginalBlockPartitionExistence) and
|geometricCoreOfTransport| (FinslerOriginalPhysicalPartitionTransport).

## (3) Exact residual

(a) |EqualMassPartition| for the atomless physical laws: a measurable
|M -> (Fin q -> Fin (2^k+1))| with fibre masses |1 / (2^k+1)^q| (the
quantile/standard-Borel-isomorphism step; absent from mathlib);
(b) the per-block cube laws of |CellCoordinateIsomorphisms|.  With (a) and (b) the
core is inhabited and, combined with |hCbnd_intrinsic_lane| and the analytic fields,
so is |PopDataIntrinsic|.  No 'sorry', 'admit' or added axiom occurs.
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

/-- **The geometric core from the seed-model parts**: the equal-mass mass partition
plus the per-block cube laws. -/
def geometricCore_of_seedParts [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (w : (Fin q → Fin (2 ^ k + 1)) → ℝ)
    (hw : ∀ c, w c = ((blockW q (2 ^ k + 1) (by positivity) c : unitInterval) : ℝ))
    (Dμ : EqualMassPartition (physicalSourceProbability ωM ρ₀ : Measure M)
      (Fin q → Fin (2 ^ k + 1)) w)
    (Dν : EqualMassPartition (physicalTargetProbability ωM ρ₁ : Measure M)
      (Fin q → Fin (2 ^ k + 1)) w)
    (C : CellCoordinateIsomorphisms (M := M) q k ωM ρ₀ ρ₁
      (cellMassPartition_of_equalMass q k ωM ρ₀ ρ₁ w hw Dμ Dν)) :
    PopDataIntrinsicGeometricCore (M := M) q (2 ^ k + 1) (by positivity) ωM ρ₀ ρ₁ :=
  geometricCoreOfTransport q k ωM ρ₀ ρ₁
    (physicalBlockTransportOf q k ωM ρ₀ ρ₁
      (cellMassPartition_of_equalMass q k ωM ρ₀ ρ₁ w hw Dμ Dν) C)

end OTSelector.Reconstruction
