import OTSelector.Reconstruction.FinslerOriginalLegalTiltedWindowReadout
import OTSelector.Reconstruction.FinslerOriginalRootedCampbellFrozenCore
import OTSelector.Reconstruction.FinslerFrozenCoreDomination

/-!
# Local additivity of the finite legal maximum

This module isolates the final sub-gap of
FinslerOriginalLegalTiltedWindowReadout: the local optimality/readout formula
for the finite legal maximum.  The finite legal optimum is realized by the
local candidate matching at almost every anchor, so that after volume
normalization the finite tilted value equals the scene windowed readout of the
local candidate-value readout J, up to a vanishing defect.

The two finite inputs of the paper are isolated explicitly as the *lower
readout inequality* (the local candidate matching is legal, hence a feasible
value for the finite maximum) and the *frozen-core finite-domination upper
inequality* (the finite legal optimum is bounded by the local candidate readout
plus a defect that vanishes after volume normalization).

1. **normalized_tendsto_of_localReadout**: a squeeze lemma: if the finite value
   T n is sandwiched between vol n * J and vol n * J + defect n, and the
   normalized defect tends to zero, then T n / vol n tends to J.

2. **markedPressureReadout_of_localOptimality**: instantiation with
   vol n = volume.real (U n), T n the finite tilted readout, and
   J = int m, Jfun m d(Palm M): the normalized marked pressure limit is the Palm
   integral of the local candidate-value readout.

3. **palmIdentification_of_localOptimality**: if the local readout Jfun is
   pointwise dominated by the local legal pressure readout I, then the marked
   pressure limit is at most int m, I m d(Palm M).  This is the (Palm)
   identification inequality of the retained-core lane, now obtained from the
   local optimality squeeze.

## Exact remaining sub-gap

The two finite inequalities are the paper's finite-domination/local-optimality
statements: (a) the actual candidate matching restricted to the window is a
legal finite matching, so its value is a lower bound for the finite legal
maximum (this is the constructive direction; it needs the legality of the
candidate matching's window restriction), and (b) the frozen-core finite
domination upper bound with defect o(volume).  The squeeze, the normalization,
the Palm readout and the final comparison with the local legal pressure are
proved here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability
open scoped ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Local-optimality squeeze.**  If the finite value T is sandwiched between
vol * J and vol * J + defect, with positive growing volume and vanishing
normalized defect, then the normalized finite value tends to J. -/
theorem normalized_tendsto_of_localReadout
    (T vol defect : ℕ → ℝ) (J : ℝ)
    (hvol : ∀ n, 0 < vol n)
    (hlower : ∀ n, vol n * J ≤ T n)
    (hupper : ∀ n, T n ≤ vol n * J + defect n)
    (hdef : Tendsto (fun n => defect n / vol n) atTop (𝓝 0)) :
    Tendsto (fun n => T n / vol n) atTop (𝓝 J) := by
  have hnonneg : ∀ n, 0 ≤ T n / vol n - J := by
    intro n
    have h := hlower n
    rw [sub_nonneg]
    rw [le_div_iff₀ (hvol n)]
    linarith [h]
  have hle : ∀ n, T n / vol n - J ≤ defect n / vol n := by
    intro n
    have h := hupper n
    rw [sub_le_iff_le_add, div_le_iff₀ (hvol n)]
    have hd : (defect n / vol n + J) * vol n = defect n + J * vol n := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (hvol n))]
    rw [hd]
    nlinarith [h]
  have hzero : Tendsto (fun n => T n / vol n - J) atTop (𝓝 0) :=
    squeeze_zero hnonneg hle hdef
  have hstep : Tendsto (fun n => (T n / vol n - J) + J) atTop (𝓝 (0 + J)) :=
    hzero.add (tendsto_const_nhds (x := J))
  have heq : (fun n => (T n / vol n - J) + J) = fun n => T n / vol n := by
    funext n
    ring
  rw [heq] at hstep
  simpa using hstep

/-- **Marked pressure readout from local optimality.**  If the finite tilted
readouts are sandwiched between the window mass times the Palm readout of the
local candidate value and that same quantity plus a defect vanishing after
normalization, then their volume-normalized limit is exactly the Palm integral
of the local candidate-value readout. -/
theorem markedPressureReadout_of_localOptimality
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (Jfun : PhysicalPairPalmMark (Fin q) → ℝ)
    (U : ℕ → Set (Fin q → ℝ)) (hU : ∀ n, MeasurableSet (U n))
    (hUfin : ∀ n, volume (U n) ≠ ⊤)
    (hVol : ∀ n, 0 < volume.real (U n))
    (readout defect : ℕ → ℝ)
    (hlower : ∀ n, volume.real (U n) *
        (∫ m, Jfun m ∂legalMarkedJointPalm q M.law) ≤ readout n)
    (hupper : ∀ n, readout n ≤ volume.real (U n) *
        (∫ m, Jfun m ∂legalMarkedJointPalm q M.law) + defect n)
    (hdef : Tendsto (fun n => defect n / volume.real (U n)) atTop (𝓝 0)) :
    Tendsto (fun n => readout n / volume.real (U n)) atTop
      (𝓝 (∫ m, Jfun m ∂legalMarkedJointPalm q M.law)) :=
  normalized_tendsto_of_localReadout readout (fun n => volume.real (U n)) defect
    (∫ m, Jfun m ∂legalMarkedJointPalm q M.law) hVol hlower hupper hdef

/-- **Palm identification from local optimality.**  If the local candidate-value
readout is pointwise dominated by the local legal pressure readout I, then the
marked pressure limit is at most the Palm integral of I. -/
theorem palmIdentification_of_localOptimality
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (Jfun I : PhysicalPairPalmMark (Fin q) → ℝ)
    (hJ : Integrable Jfun (legalMarkedJointPalm q M.law))
    (hI : Integrable I (legalMarkedJointPalm q M.law))
    (hpt : ∀ᵐ m ∂(legalMarkedJointPalm q M.law), Jfun m ≤ I m) :
    (∫ m, Jfun m ∂legalMarkedJointPalm q M.law) ≤
      ∫ m, I m ∂legalMarkedJointPalm q M.law :=
  integral_mono_ae hJ hI hpt

end OTSelector.Reconstruction
