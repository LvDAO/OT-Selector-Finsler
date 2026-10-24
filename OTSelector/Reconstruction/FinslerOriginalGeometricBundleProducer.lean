import OTSelector.Reconstruction.FinslerOriginalIntrinsicDataActual

/-!
# The geometric data bundle of |PopDataIntrinsic| (producer boundary)

## Delivered

|PopDataIntrinsicGeometricCore|: the measure/geometry interface of |PopDataIntrinsic|
that the repo's cell machinery addresses, stated verbatim: the two measurable cell
decompositions |cellS cellT : M -> Fin q -> Fin m| with their mass laws (block
weights |1 / m^q|), and the two coordinate maps |coordS coordT : M -> Fin q -> R|
with measurability.  The remaining geometric fields of |PopDataIntrinsic| are the
law fields

  |hcubeS hcubeT hmarkLawS hmarkLawT hindepS hindepT|

(the pushforwards of the cell-normalized measures to |cubeMeasure (Fin q) 1| and the
mark labels |labelS labelT| with mark laws |alpha beta| and independence).

## Obstruction (why |dataIntr_of_geometricLane| is not yet inhabited)

The mass laws |hmassS hmassT| demand, for the prescribed block-weight law
|c |-> 1 / m^q|, a measurable partition of |M| with exactly those
|physicalSourceProbability| masses.  No module in the repository constructs such a
measure-dependent partition: the TaylorTiles/cell-model machinery (e.g.
FinslerCellModelData.lean, FinslerConcreteUpperModel.lean,
FinslerPopulationPressureTiles.lean) supplies finite-tile cost/model data, not a
partition of |M| with prescribed image laws, and the cube/mark/independence laws
|hcubeS hcubeT hmarkLawS hmarkLawT hindepS hindepT| are additional geometric inputs
that no available producer supplies.

With the partition in hand, the analytic fields are transcriptions:
|kin g Cb G hCb0 hG0 hkin hkin_bound hg hgb alpha beta hαprob hβprob p hp
 epsilon Berr Gb Bnd hε0 hB0 hGb0 hBnd0 hGbnd0 hGbnd hF0 hrel_guarded hprobe hG
 hmodel_bound hdelta hqdim|, and |hCbnd_intrinsic| is produced by
|hCbnd_intrinsic_lane| (FinslerOriginalIntrinsicDataActual.lean).

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

/-- **The measure/geometry core of |PopDataIntrinsic|**: measurable cell
decompositions with the block-weight mass laws, and measurable coordinate maps.
The cube laws, label maps with mark laws, and independence are the remaining
geometric fields (see the module documentation). -/
structure PopDataIntrinsicGeometricCore
    [MeasurableSpace M]
    (q m : ℕ) (hm : 0 < m) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))] where
  cellS : M → (Fin q → Fin m)
  hcellS : Measurable cellS
  cellT : M → (Fin q → Fin m)
  hcellT : Measurable cellT
  hmassS : ∀ c, ((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}) =
    ENNReal.ofReal ((blockW q m hm c : unitInterval) : ℝ)
  hmassT : ∀ c, ((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}) =
    ENNReal.ofReal ((blockW q m hm c : unitInterval) : ℝ)
  coordS : M → Fin q → ℝ
  hcoordS : Measurable coordS
  coordT : M → Fin q → ℝ
  hcoordT : Measurable coordT

end OTSelector.Reconstruction
