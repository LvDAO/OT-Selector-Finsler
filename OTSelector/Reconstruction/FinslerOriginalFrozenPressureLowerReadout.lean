import OTSelector.Reconstruction.FinslerOriginalScenePressureWiring
import OTSelector.Reconstruction.FinslerOriginalPressureLowerAssembly

/-!
# The hread producer: frozen pressure lower = frozen Campbell readout

This module produces the hread input of the actual lower bundle
(EndgameLowerFields/FinalProbLowerData lane): the identification
frozenPressureLower = Psi of the lower pressure readout.

## Findings

frozenPressureLower is DEFINED as the frozen Campbell readout

  frozenPressureLower Seed a kappa lambda g q = fun f t =>
    campbellAveragedFrozenCost Seed a kappa lambda (g f t) q,

and the probe-shifted readout frozenProbePressureLower is DEFINED as

  frozenProbePressureLower = fun f t => frozenPressureLower f t - |t| * ||f||.

Hence:

1. frozenPressureLower_apply / frozenProbePressureLower_apply: both readouts are
   definitional unfolding lemmas (rfl).
2. frozenPressureLower_eq_frozenProbe_add_shift: the unshifted readout is the
   probe-shifted readout PLUS the probe constant |t| * ||f||.  This is the exact
   bookkeeping needed: the hprob lane works at the SHIFTED readout (Psi - shift,
   the probeShiftedReadout of FinslerOriginalEndgameLowerField), while hread is
   stated at the UNSHIFTED frozenPressureLower.  The probe shift is paid twice:
   once by the hprob readout (as -shift) and once by hread (as +shift).
3. frozenPressureLower_eq_of_apply: hread follows from a pointwise
   identification of Psi with the frozen Campbell readout.
4. frozenPressureLower_eq_of_probeReadout: hread in the SHIFTED form: if
   frozenProbePressureLower = Psi then the unshifted readout equals
   Psi + probeShift, i.e. hread at Psi + probeShift.
5. endgameLowerHread_of_campbellApply / endgameLowerHread_of_probeReadout: the
   two producers in the exact shape consumed by
   FinslerOriginalEndgameLowerLaneInputsActual / FinslerOriginalEndgameLowerFieldActual
   (hread : frozenPressureLower P a kappa lambda g q = Psi).

## Composition with the shifted-readout bridge

FinslerOriginalShiftedReadoutBridge works with probeShiftedReadout Psi =
(fun f t => Psi f t - |t| * ||f||) and asserts the hprob field there.  If the
probabilistic lane delivers the identification frozenProbePressureLower = Psi,
then hread is at Psi + probeShift, and composing with the bridge's shifted field
at (probeShiftedReadout (Psi + probeShift)) lands the lower bundle at the shifted
readout of the unshifted hread value.  No identification between the shifted and
unshifted readouts holds by construction; the shift is explicit and must be
tracked, which is exactly what this module fixes.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}

/-- **Unfolding of the frozen lower pressure readout.** -/
theorem frozenPressureLower_apply
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    frozenPressureLower Seed a κ lambda g q f t =
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q :=
  rfl

/-- **Unfolding of the probe-shifted frozen lower pressure readout.** -/
theorem frozenProbePressureLower_apply
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    frozenProbePressureLower Seed a κ lambda g q f t =
      frozenPressureLower Seed a κ lambda g q f t - |t| * (‖f‖₊ : ℝ) :=
  rfl

/-- **The unshifted readout is the shifted readout plus the probe constant.** -/
theorem frozenPressureLower_eq_frozenProbe_add_shift
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    frozenPressureLower Seed a κ lambda g q f t =
      frozenProbePressureLower Seed a κ lambda g q f t + |t| * (‖f‖₊ : ℝ) := by
  rw [frozenProbePressureLower_apply]
  ring

/-- **hread from a pointwise Campbell identification.**  If the readout Psi
agrees pointwise with the frozen Campbell cost, the frozen lower pressure readout
is Psi. -/
theorem frozenPressureLower_eq_of_apply
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (h : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Ψ f t = campbellAveragedFrozenCost Seed a κ lambda (g f t) q) :
    frozenPressureLower Seed a κ lambda g q = Ψ := by
  funext f t
  rw [frozenPressureLower_apply]
  exact (h f t).symm

/-- **hread in shifted form.**  If the probe-shifted frozen readout is Psi, then
the unshifted frozen lower pressure readout equals Psi plus the probe constant. -/
theorem frozenPressureLower_eq_addProbeShift_of_probeReadout
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (h : frozenProbePressureLower Seed a κ lambda g q = Ψ) :
    frozenPressureLower Seed a κ lambda g q =
      fun f t ↦ Ψ f t + |t| * (‖f‖₊ : ℝ) := by
  funext f t
  rw [frozenPressureLower_eq_frozenProbe_add_shift, h]

/-- **The hread producer consumed by the actual lower lane**
(FinslerOriginalEndgameLowerLaneInputsActual / FinslerOriginalEndgameLowerFieldActual):
the frozen pressure readout equals Psi once Psi is pointwise the frozen Campbell
cost.  This is exactly the shape
hread : frozenPressureLower P a κ lambda g q = Ψ. -/
theorem endgameLowerHread_of_campbellApply
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (h : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Ψ f t = campbellAveragedFrozenCost P a κ lambda (g f t) q) :
    frozenPressureLower P a κ lambda g q = Ψ :=
  frozenPressureLower_eq_of_apply P a κ lambda g q Ψ h

/-- **The shifted hread producer consumed by the actual lower lane.**  If the
probe-shifted lane supplies frozenProbePressureLower = Psi, this module supplies
the unshifted hread at Psi + probe constant, which is what the bundle's hread
slot consumes after the hprob readout has paid the shift. -/
theorem endgameLowerHread_of_probeReadout
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (h : frozenProbePressureLower P a κ lambda g q = Ψ) :
    frozenPressureLower P a κ lambda g q =
      fun f t ↦ Ψ f t + |t| * (‖f‖₊ : ℝ) :=
  frozenPressureLower_eq_addProbeShift_of_probeReadout P a κ lambda g q Ψ h

end OTSelector.Reconstruction
