import OTSelector.Reconstruction.FinslerOriginalPhysicalChartCoordinates

/-!
# Minimal inputs of the F13 chart-coordinate residual

## (1) |equalMassPartition_of_globalCubeLaw|

Every hypothesis of the equal-mass partition is a separate explicit binder: the
coordinate map |psi|, its measurability, the cube-law pushforward, the cell map
|cellOfCoord| with its measurability, and the equal-mass cube masses
|hcellmass|.  The proof is a direct application of
|equalMassPartition_of_coordinateLawMap|.

## (2) |physicalChartCoordinates_of_globalCubeLaw|

|PhysicalChartCoordinates| adds nothing beyond this named data: it is assembled
from |psiS hpsiS pushS psiT hpsiT pushT cellOfCoord hcellOfCoord cellmass| by
the structure literal.  Hence the residual for |dataIntr| is exactly: the two
global cube-law coordinates and the equal-mass cell map.

## (3) Minimal residual for |dataIntr| (|PopDataIntrinsic|)

(a) |psiS : M -> Fin q -> R| measurable with
    |(physicalSourceProbability omegaM rho_0).map psiS = cubeMeasure (Fin q) 1|;
(b) |psiT| with the target analogue;
(c) |cellOfCoord| measurable with |cellmass|;
(d) the per-block cube laws |C : CellCoordinateIsomorphisms|;
(e) the four seed inputs of |PaperSeedPatchBundle| (patch, tube openness, two
    clock atomlessness fields);
(f) the analytic fields of |PopDataIntrinsic| (kin/kin_bound, g, Cb, G, p/hp,
    error sequences, hrel_guarded, hqdim, ...), typechecked in
    FinslerOriginalPopDataIntrinsicBound.

The volume binder only yields the LOCAL chart equality
|chart_pushforward_restrict_of_unit_density| (FinslerOriginalChartCoordinatesFromVolume);
it does not yield (a)-(d): the chart is local and pushes to |m.restrict chi.target|,
not to the cube law.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory
open OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.Probability
open scoped Topology ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-- **(1) Equal-mass partition from the explicit global cube-law inputs.** -/
def equalMassPartition_of_globalCubeLaw [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    (w : (Fin q → Fin (2 ^ k + 1)) → ℝ)
    (ψ : M → Fin q → ℝ) (hψ : Measurable ψ)
    (cellOfCoord : (Fin q → ℝ) → (Fin q → Fin (2 ^ k + 1)))
    (hcellOfCoord : Measurable cellOfCoord)
    (hpush : (physicalSourceProbability ωM ρ₀ : Measure M).map ψ = cubeMeasure (Fin q) 1)
    (hcellmass : ∀ c, cubeMeasure (Fin q) 1 (cellOfCoord ⁻¹' {c}) = ENNReal.ofReal (w c)) :
    EqualMassPartition (physicalSourceProbability ωM ρ₀ : Measure M)
      (Fin q → Fin (2 ^ k + 1)) w :=
  equalMassPartition_of_coordinateLawMap q k (physicalSourceProbability ωM ρ₀ : Measure M)
    w ψ hψ cellOfCoord hcellOfCoord hpush hcellmass

/-- **(2) |PhysicalChartCoordinates| from the explicit minimal inputs.** -/
def physicalChartCoordinates_of_globalCubeLaw [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (w : (Fin q → Fin (2 ^ k + 1)) → ℝ)
    (ψS : M → Fin q → ℝ) (hψS : Measurable ψS)
    (pushS : (physicalSourceProbability ωM ρ₀ : Measure M).map ψS = cubeMeasure (Fin q) 1)
    (ψT : M → Fin q → ℝ) (hψT : Measurable ψT)
    (pushT : (physicalTargetProbability ωM ρ₁ : Measure M).map ψT = cubeMeasure (Fin q) 1)
    (cellOfCoord : (Fin q → ℝ) → (Fin q → Fin (2 ^ k + 1)))
    (hcellOfCoord : Measurable cellOfCoord)
    (cellmass : ∀ c, cubeMeasure (Fin q) 1 (cellOfCoord ⁻¹' {c}) = ENNReal.ofReal (w c)) :
    PhysicalChartCoordinates q k ωM ρ₀ ρ₁ w where
  ψS := ψS
  hψS := hψS
  pushS := pushS
  ψT := ψT
  hψT := hψT
  pushT := pushT
  cellOfCoord := cellOfCoord
  hcellOfCoord := hcellOfCoord
  cellmass := cellmass

end OTSelector.Reconstruction
