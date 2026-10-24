import OTSelector.Reconstruction.FinslerOriginalUnshiftedReadoutDerivative
import OTSelector.Reconstruction.FinslerOriginalReadoutGlue

/-!
# The lane datum identification hIw

The last residual of `FinslerOriginalUnshiftedReadoutDerivative` is the lane datum
identification

    hIw : forall f, (datum f).Iw = frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f.

It is **definitional from the frozen Campbell readout** of the paper endgame data
assembly: `FrozenCampbellReadout g q datum` says, pointwise in probe and tilt,

    campbellAveragedFrozenCost (g f t) q = (datum f).Iw t,

while `frozenPressureLower ... g q f t` *is* `campbellAveragedFrozenCost (g f t) q` by
definition (rfl).  So hIw follows by `funext t` and symmetry of the readout equation,
with no extra hypothesis.

Consequently the V4 endgame `pressureLower` field (set to `frozenPressureLower ...` in
`paperEndgameData_of_upperBundle`) carries the readout tilt derivative from the single
near-minimizer squeeze `hsqueeze`, and the residual list of the derivative shortens to
`hsqueeze` ONLY.  No `sorry`, `admit` or added axiom.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace Asymptotics
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable {A B : Set M}

/-- **The lane datum identification hIw.**  The frozen Campbell readout of the endgame
assembly is exactly the pointwise identification of the lane datum readout with the lane's
unshifted frozen pressure field. -/
theorem frozenCampbellReadout_Iw_eq_frozenPressureLower
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum) :
    ∀ f : FinalProbeSpace A B,
      (datum f).Iw = frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f := by
  intro f
  funext t
  show (datum f).Iw t = campbellAveragedFrozenCost Seed a κ lambda (g f t) q
  exact (hC f t).symm

/-- **hderiv at the V4 endgame pressureLower field, from the squeeze only.**  The lane
datum identification is closed definitionally, so the unshifted readout derivative needs
only `hsqueeze` (the paper's zero-tilt near-minimizer readout identification) beyond the
endgame assembly's frozen Campbell readout. -/
theorem finslerReadoutTiltDerivative_frozenLowerField_of_squeeze
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum)
    (p : FinalProbeSpace A B → ℝ)
    (hsqueeze : ActualLaneReadoutSqueeze datum
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) p) :
    FinslerReadoutTiltDerivative
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) :=
  finslerReadoutTiltDerivative_unshiftedFrozenReadout Seed a κ lambda g q datum p
    (frozenCampbellReadout_Iw_eq_frozenPressureLower Seed a κ lambda g q datum hC)
    hsqueeze

end OTSelector.Reconstruction
