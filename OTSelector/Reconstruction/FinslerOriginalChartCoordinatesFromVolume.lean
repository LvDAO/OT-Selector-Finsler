import OTSelector.Reconstruction.FinslerOriginalPhysicalChartCoordinates

/-!
# Local chart pushforward from the volume-density binder

The paper endgame carries the volume binder

`(omegaM.restrict chi.source).map chi = (m.restrict chi.target).withDensity
  (fun y => ENNReal.ofReal (v old y))`

for every chart centre `old`.  This module records the exact content that IS derivable
from it: when the calibrated density is a.e. one on the target, the chart pushforward
of the restricted source measure is the restricted Haar measure on the target.  This is
the local, per-chart part of the F13 coordinate law.

## What is NOT derivable from the volume binder

The binder is local: it is indexed by the chart centre `old` and only relates the
restriction to `chi.source` with a density on `chi.target`.  In particular it gives

* no chain from `m.restrict chi.target` (an `E`-dimensional Haar restriction) to the cube
  law `cubeMeasure (Fin q) 1` for the (unrestricted) block index `q`;
* no single global measurable map `psi : M -> Fin q -> R` whose pushforward of the
  physical probability is the cube law, since the chart is local;
* no cube cell map `cellOfCoord` with its equal-mass cell masses;
* no per-block cube laws `C : CellCoordinateIsomorphisms`.

So `PhysicalChartCoordinates` (`FinslerOriginalPhysicalChartCoordinates`) keeps all of
its fields: only the local pushforward equality below is discharged here.
-/

open MeasureTheory

namespace OTSelector.Reconstruction

/-- **Local chart pushforward at a.e. unit calibrated density.**

If the chart pushforward of the restricted source measure is the restricted Haar measure
weighted by the calibrated density `fun y => ENNReal.ofReal (v y)`, and that density is
a.e. one, then the pushforward is the restricted Haar measure itself. -/
theorem chart_pushforward_restrict_of_unit_density {M E : Type*}
    [MeasurableSpace M] [MeasurableSpace E]
    {χ : M → E} {s : Set M} {t : Set E} {m : Measure E} {v : E → ℝ} {ωM : Measure M}
    (hvol : (ωM.restrict s).map χ =
      (m.restrict t).withDensity (fun y => ENNReal.ofReal (v y)))
    (hv1 : ∀ᵐ y ∂(m.restrict t), v y = 1) :
    (ωM.restrict s).map χ = m.restrict t := by
  rw [hvol]
  have h : (fun y => ENNReal.ofReal (v y)) =ᵐ[(m.restrict t)] (fun _ => 1) :=
    hv1.mono fun y hy => by simp [hy]
  rw [withDensity_congr_ae h]
  exact withDensity_one

end OTSelector.Reconstruction
