import OTSelector.Reconstruction.FinslerOriginalActualLaneSqueeze

/-!
# hderiv at the unshifted frozen readout

Discharges the last derivative input `hderiv : FinslerReadoutTiltDerivative D.pressureLower`
of `FinslerOriginalPaperTheoremFinalV4` from the actual-lane kinetic squeeze.

The V4 endgame datum sets its readout field to the frozen pressure field

    D.pressureLower = frozenPressureLower (K := A ∪ B) Seed a κ lambda g q

(at the same `frozenCost := hprobFrozenCostFamily` family used throughout the lane), so
the derivative is exactly the one produced by the actual-lane squeeze:

* `finslerReadoutTiltDerivative_of_unshiftedReadoutSqueeze`: for ANY pressure field, a
  lane datum family whose weighted pressure is that field (`hIw`) plus the
  `ActualLaneReadoutSqueeze` (the paper's zero-tilt near-minimizer readout
  identification) yields `FinslerReadoutTiltDerivative` at the field;
* `finslerReadoutTiltDerivative_unshiftedFrozenReadout`: the same at the concrete
  unshifted frozen readout family (arbitrary probe family `g`; the lane's
  `hprobFrozenCostFamily` enters only through `g` and the datum identification);
* `finslerReadoutTiltDerivative_of_field_eq`: field transport, so the V4 `hderiv`
  follows by `rfl` (`paperEndgameData_actual_final_v4 ... .pressureLower` unfolds to the
  frozen readout) applied to the theorem above.

Residual input: only the near-minimizer squeeze `hsqueeze` and the lane datum
identification `hIw` (both paper-level inputs of V4's residual table).  No `sorry`,
`admit` or added axiom.
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

/-- **hderiv from the actual-lane squeeze.**  For any limiting pressure field: a lane
datum family identified with the field, together with the near-minimizer readout squeeze,
gives the readout tilt derivative at zero. -/
theorem finslerReadoutTiltDerivative_of_unshiftedReadoutSqueeze
    {W : Type*} {G Cb : ℝ}
    (pressureLower : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ)
    (hIw : ∀ f : FinalProbeSpace A B, (datum f).Iw = pressureLower f)
    (hsqueeze : ActualLaneReadoutSqueeze datum pressureLower p) :
    FinslerReadoutTiltDerivative pressureLower := by
  have hsqueeze' : ∀ (f : FinalProbeSpace A B) (δ : ℝ), 0 < δ → ∀ c ∈ (datum f).Cw,
      (datum f).K c ≤ (datum f).Iw 0 + δ → |(datum f).P c - p f| ≤ δ := by
    intro f δ hδ c hc hK
    have hK' : (datum f).K c ≤ pressureLower f 0 + δ := by
      rwa [hIw f] at hK
    exact hsqueeze f δ hδ c hc hK'
  have h := finslerReadoutTiltDerivative_stationaryReadout_of_kinetic_squeeze
    datum p hsqueeze'
  have hfield : (fun f t => (datum f).Iw t) = fun f t => pressureLower f t := by
    funext f t
    exact congrFun (hIw f) t
  rwa [hfield] at h

/-- **hderiv at the unshifted frozen readout.**  Instantiation at the lane's frozen
pressure field `frozenPressureLower (K := A ∪ B) Seed a κ lambda g q` (the same frozen
family `hprobFrozenCostFamily` used by the V4 endgame datum). -/
theorem finslerReadoutTiltDerivative_unshiftedFrozenReadout
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ)
    (hIw : ∀ f : FinalProbeSpace A B,
      (datum f).Iw = frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f)
    (hsqueeze : ActualLaneReadoutSqueeze datum
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) p) :
    FinslerReadoutTiltDerivative
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) :=
  finslerReadoutTiltDerivative_of_unshiftedReadoutSqueeze
    (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) datum p hIw hsqueeze

/-- **Field transport**: the derivative transports along an equality of pressure fields;
applied with the definitional equality `D.pressureLower = frozenPressureLower ...` this
is exactly V4's `hderiv`. -/
theorem finslerReadoutTiltDerivative_of_field_eq
    {pressureLower : FinalPressureField A B} {field : FinalPressureField A B}
    (h : pressureLower = field) (hd : FinslerReadoutTiltDerivative pressureLower) :
    FinslerReadoutTiltDerivative field :=
  h ▸ hd

end OTSelector.Reconstruction
