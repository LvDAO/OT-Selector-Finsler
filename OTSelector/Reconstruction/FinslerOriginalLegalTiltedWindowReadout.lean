import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalPathWindowReadout
import OTSelector.Reconstruction.FinslerOriginalMarkedPressureRepresentation

/-!
# Readout identification of the finite-volume tilted value

This module isolates the last sub-gap of
FinslerOriginalMarkedPressureRepresentation: the readout identification of the
finite-volume tilted value.

The scene-level windowed readout formula is available for a genuine weighted
stationary matching: the expected finite-volume window readout of a local Palm
observable is the window mass times the Palm integral
(LegalWeightedStationaryPoissonMatching.pathWindowReadout_integrable_and_
integral).  We specialize it to constant displacement, then instantiate the
marked pressure representation and combine with the local legal pressure.

1. **Scene window readout identity** (scene_windowReadout_integral): for a
   finite-volume measurable window W and a local readout J, the expected
   scene-level windowed readout is volume(W) times the Palm integral of J.

2. **Palm representation of the normalized readout limit**
   (markedPressureRepresentation_of_sceneReadout): if the finite-volume pressure
   readouts are scene windowed readouts of a fixed local J and their
   volume-normalized limit is p, then p = int m, J m d(Palm M).

3. **Local legal pressure comparison** (palmIdentification_of_sceneReadout): if
   J is pointwise dominated by the local legal pressure readout I, then
   p <= int m, I m d(Palm M).  This is the Palm identification inequality used
   in the retained-core lane, now derived from the readout representation.

## Remaining sub-gap

The last identification is the local additivity of the finite legal maximum:
that the actual finite-volume optimal tilted value legalMarkedTilted is, after
volume normalization, the scene windowed readout of the local candidate-value
readout J.  The maximum over legal matchings is nonlinear, so this is not a
measure-theoretic consequence of the Campbell machinery; it is the local
optimality/readout formula of the paper (the finite legal optimum is realized by
the local candidate matching at almost every anchor).  Everything else - the
window readout expectation, the normalization, the limit and the comparison with
the local legal pressure - is proved here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Scene window readout identity.**  For a finite-volume measurable window W
and a local Palm readout J, the expected scene-level windowed readout of a
genuine weighted stationary matching is the window mass times the Palm integral
of J. -/
theorem scene_windowReadout_integral
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {W : Set (Fin q → ℝ)} (hW : MeasurableSet W) (hWfin : volume W ≠ ⊤)
    (J : PhysicalPairPalmMark (Fin q) → ℝ)
    (hJ : Integrable J (legalMarkedJointPalm q M.law)) :
    (∫ s, legalMarkedPathWindowReadout q (fun _ _ => 0)
        (W.indicator (fun _ => (1 : ℝ))) J s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      volume.real W * (∫ m, J m ∂legalMarkedJointPalm q M.law) := by
  have hh : Integrable (W.indicator (fun _ => (1 : ℝ))) (volume : Measure (Fin q → ℝ)) :=
    IntegrableOn.integrable_indicator (integrableOn_const hWfin) hW
  obtain ⟨hi, he⟩ := M.pathWindowReadout_integrable_and_integral
    (d := fun _ _ => (0 : ℝ)) (h := W.indicator (fun _ => (1 : ℝ)))
    (f := J) measurable_const hh hJ
  rw [he, smul_eq_mul]
  congr 1
  rw [integral_indicator hW, setIntegral_const, smul_eq_mul, mul_one]

/-- **Palm representation of the normalized readout limit.**  If the finite-volume
pressure readouts are the scene windowed readouts of a fixed local readout J and
their volume-normalized limit is p, then p is the Palm integral of J. -/
theorem markedPressureRepresentation_of_sceneReadout
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (J : PhysicalPairPalmMark (Fin q) → ℝ)
    (hJ : Integrable J (legalMarkedJointPalm q M.law))
    (U : ℕ → Set (Fin q → ℝ)) (hU : ∀ n, MeasurableSet (U n))
    (hUfin : ∀ n, volume (U n) ≠ ⊤)
    (hVol : ∀ n, volume.real (U n) ≠ 0)
    (readout : ℕ → ℝ)
    (hread : ∀ n, readout n =
      ∫ s, legalMarkedPathWindowReadout q (fun _ _ => 0)
        ((U n).indicator (fun _ => (1 : ℝ))) J s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q)))
    {p : ℝ}
    (hp : Tendsto (fun n => readout n / volume.real (U n)) atTop (𝓝 p)) :
    p = ∫ m, J m ∂legalMarkedJointPalm q M.law := by
  have hconst : ∀ n, readout n / volume.real (U n) =
      ∫ m, J m ∂legalMarkedJointPalm q M.law := by
    intro n
    rw [hread n, scene_windowReadout_integral M (hU n) (hUfin n) J hJ]
    exact mul_div_cancel_left₀ _ (hVol n)
  have hfun : (fun n => readout n / volume.real (U n)) =
      fun _ => ∫ m, J m ∂legalMarkedJointPalm q M.law := funext hconst
  rw [hfun] at hp
  exact tendsto_nhds_unique hp tendsto_const_nhds

/-- **Local legal pressure comparison.**  If the local readout J is pointwise
dominated by the local legal pressure readout I, then the represented marked
pressure limit is at most the Palm integral of I. -/
theorem palmIdentification_of_sceneReadout
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (J I : PhysicalPairPalmMark (Fin q) → ℝ)
    (hJ : Integrable J (legalMarkedJointPalm q M.law))
    (hI : Integrable I (legalMarkedJointPalm q M.law))
    (hpt : ∀ᵐ m ∂(legalMarkedJointPalm q M.law), J m ≤ I m)
    {p : ℝ}
    (hp : p = ∫ m, J m ∂legalMarkedJointPalm q M.law) :
    p ≤ ∫ m, I m ∂legalMarkedJointPalm q M.law := by
  rw [hp]
  exact integral_mono_ae hJ hI hpt

end OTSelector.Reconstruction
