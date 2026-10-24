import OTSelector.Reconstruction.FinslerOriginalEndgameValueFieldActual
import OTSelector.Reconstruction.FinslerOriginalEndgameUpperFieldActual

/-!
# Shift convention for the actual upper pressure field (audit flag F18)

The shifted upper readout bridge ProbeShiftedUpperReadout is phrased for a lane
upper pressure that already carries the probe-shift convention: it asks

  pressureUpper f t = (datum f).I2 t - probeShift f t,

i.e. the lane field equals the second-moment stationary pressure I2 of the datum
MINUS the probe constant probeShift f t = |t| * (norm f).  The actual upper
bundle endgameUpperFields_actual_lane (FinslerOriginalEndgameUpperFieldActual)
instead has

  pressureUpper = endgameUpperPressure_actual q m pc
    = fun f t => sum over c : Fin q -> Fin m of (1 / m^q) * pc f t c,

the UNshifted block weighted pool of the local upper pressure limits.  So the
shifted bridge as literally stated does not apply to the bundle field (F18).

## Resolution proved here

1. Which sign the upper bridge needs.  The probe constant is SUBTRACTED from the
   upper field, exactly as for the lower lane; equivalently it is ADDED back on
   the readout side: pressureUpper + probeShift = I2.  The sign/add-form
   characterisations are probeShiftedUpperReadout_iff_add_probeShift and
   probeShiftedUpperReadout_iff_sub_probeShift.

2. The convention bridge for the actual upper field.  Shifting the actual upper
   pool by -probeShift turns the shifted bridge into the UNshifted weighted-pool
   identification

     ActualUpperReadout q m pc datum
       := UpperStationaryReadout (endgameUpperPressure_actual q m pc) datum
       := forall f t, endgameUpperPressure_actual q m pc f t = (datum f).I2 t,

   proved as probeShiftedUpperReadout_actualUpper_iff.  Under this bridge the
   shifted actual upper field is literally the canonical shifted datum field
   (actualUpper_shifted_eq_probeShiftedUpperField), which is why the shifted
   convention is the correct one to pair with the shifted frozen lower lane.

3. The exact identification isolated.  Since the actual upper pressure is the
   block weighted pool of the local limits (not a Campbell average), the missing
   identity is ActualUpperReadout q m pc datum: the weighted pool reads off the
   datum second-moment stationary pressure I2.  This is the upper-sign analogue
   of FrozenCampbellReadout (which identifies the frozen Campbell average with
   Iw); its precise type is the def below.  The obstruction is recorded by
   finalValueIdentification_probeShift_zero_of_unshiftedUpper: an unshifted upper
   field paired with the shifted lower field satisfies the value identification
   only when the probe constant vanishes identically.

4. Composition.  endgameValueFields_actual_lane_actualUpper is the
   canonical-upper variant of the actual-lane value field for the ACTUAL upper
   bundle: its upper pressure is the actual block weighted pool shifted by
   -probeShift, its lower pressure is the lane probe-shifted frozen Campbell
   readout, and hvalue follows from FrozenCampbellReadout, ActualUpperReadout and
   the screening data.  The projection lemmas identify both pressure fields.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability Module
open scoped ContDiff Topology ENNReal NNReal BigOperators CompactlySupported BoundedContinuousFunction

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
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## 1. Which probe-shift sign the upper bridge uses -/

section SignConvention

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- Definitional form of the upper shifted bridge.  The shifted upper bridge is
exactly the statement that the lane upper pressure equals I2 of the datum minus
the probe constant. -/
theorem probeShiftedUpperReadout_iff_sub_probeShift
    (pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedUpperReadout pressureUpper datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        pressureUpper f t = (datum f).I2 t - probeShift f t :=
  Iff.rfl

/-- Sign form of the upper shifted bridge.  The probe constant is subtracted from
the upper lane field; equivalently it is added back on the datum side,
pressureUpper + probeShift = I2.  This is the same sign as for the lower lane. -/
theorem probeShiftedUpperReadout_iff_add_probeShift
    (pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedUpperReadout pressureUpper datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        pressureUpper f t + probeShift f t = (datum f).I2 t := by
  constructor
  · intro h f t
    have hh := h f t
    linarith
  · intro h f t
    have hh := h f t
    linarith

/-- An unshifted-to-I2 readout upper field satisfies the shifted bridge after it
is itself shifted by -probeShift. -/
theorem probeShiftedUpperReadout_of_upperStationaryReadout
    (pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h : UpperStationaryReadout pressureUpper datum) :
    ProbeShiftedUpperReadout
      (fun f t => pressureUpper f t - probeShift f t) datum :=
  (probeShiftedUpperReadout_shift_iff pressureUpper datum).mpr
    (fun f t => h f t)

end SignConvention

/-! ## 2. The actual upper pool and its convention bridge -/

section ActualUpper

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The isolated upper readout identification for the actual lane.  The actual
upper bundle has pressureUpper = endgameUpperPressure_actual q m pc, the block
weighted sum of the local upper pressure limits.  The identity needed to pair it
with a stationary datum is that this unshifted weighted pool reads off the datum
second-moment stationary pressure I2 at every probe and tilt.  This is the
upper-sign analogue of FrozenCampbellReadout; the pool is the finite block
average over the marked index set with weight 1 / m^q, not a Campbell average
over the seed law. -/
def ActualUpperReadout (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  UpperStationaryReadout (endgameUpperPressure_actual q m pc) datum

/-- Unfolding of the isolated upper identification. -/
theorem actualUpperReadout_iff (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ActualUpperReadout q m pc datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        endgameUpperPressure_actual q m pc f t = (datum f).I2 t :=
  Iff.rfl

/-- The convention bridge for the actual upper field.  Shifting the actual block
weighted upper pool by -probeShift (the same sign as the lower lane), the shifted
upper bridge for it is equivalent to the unshifted weighted-pool readout
ActualUpperReadout.  Hence the bridge that the actual upper bundle supports is
the unshifted one, and the shifted readout field is obtained by explicitly
subtracting the probe constant. -/
theorem probeShiftedUpperReadout_actualUpper_iff (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedUpperReadout
      (fun f t => endgameUpperPressure_actual q m pc f t - probeShift f t) datum ↔
        ActualUpperReadout q m pc datum :=
  probeShiftedUpperReadout_shift_iff (endgameUpperPressure_actual q m pc) datum

/-- The unshifted actual upper field does not satisfy the shifted bridge unless it
agrees with I2 - probeShift; in sign form, unless the probe constant has to be
added back to reach I2. -/
theorem probeShiftedUpperReadout_actualUpper_unshifted_iff (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedUpperReadout (endgameUpperPressure_actual q m pc) datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        endgameUpperPressure_actual q m pc f t + probeShift f t = (datum f).I2 t :=
  probeShiftedUpperReadout_iff_add_probeShift _ _

/-- Under the isolated upper identification the shifted actual upper pool is the
canonical shifted datum field probeShiftedUpperField datum = I2 - probeShift.  This
is why the canonical-upper value field for the actual bundle uses the
probe-shifted actual pool. -/
theorem actualUpper_shifted_eq_probeShiftedUpperField (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hupper : ActualUpperReadout q m pc datum) :
    (fun f t => endgameUpperPressure_actual q m pc f t - probeShift f t) =
      probeShiftedUpperField datum := by
  funext f t
  show endgameUpperPressure_actual q m pc f t - probeShift f t =
    (datum f).I2 t - probeShift f t
  rw [hupper f t]

end ActualUpper

/-! ## 3. Shifting both lanes cancels, and the unshifted-upper obstruction -/

section Cancellation

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- Shifting both lanes cancels out of the value identification.  If the unshifted
lane fields read off Iw and I2 of a screened datum, then their probe-shifted
fields identify. -/
theorem finalValueIdentification_of_unshiftedReadouts_shifted
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification
      (fun f t => pressureLower f t - probeShift f t)
      (fun f t => pressureUpper f t - probeShift f t) := by
  intro f t
  show pressureLower f t - probeShift f t = pressureUpper f t - probeShift f t
  rw [hL f t, hU f t]
  exact congrArg (fun x => x - probeShift f t)
    (finalValueIdentification_stationaryFields datum hscreen f t)

/-- The unshifted-upper obstruction.  Pairing the probe-shifted lower field with an
UNshifted upper readout closes the value identification only if the probe constant
is already present in the Iw-versus-I2 gap. -/
theorem finalValueIdentification_unshiftedLower_shiftedUpper_iff
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum) :
    FinalValueIdentification
        (fun f t => pressureLower f t - probeShift f t) pressureUpper ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        (datum f).Iw t - probeShift f t = (datum f).I2 t := by
  constructor
  · intro h f t
    have hh : pressureLower f t - probeShift f t = pressureUpper f t := h f t
    rw [hL f t, hU f t] at hh
    exact hh
  · intro h f t
    show pressureLower f t - probeShift f t = pressureUpper f t
    rw [hL f t, hU f t]
    exact h f t

/-- Exact reason F18 matters: with the screening data Iw = I2 in force, an
unshifted upper field paired with the probe-shifted lower field closes the value
identification if and only if the probe constant vanishes at every probe and
tilt.  Since probeShift is nonnegative this only happens in the degenerate
zero-shift case, so the upper field must be shifted into the same convention. -/
theorem finalValueIdentification_probeShift_zero_of_unshiftedUpper
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification
        (fun f t => pressureLower f t - probeShift f t) pressureUpper ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ), probeShift f t = 0 := by
  rw [finalValueIdentification_unshiftedLower_shiftedUpper_iff
    pressureLower pressureUpper datum hL hU]
  constructor
  · intro h f t
    have hI : (datum f).Iw t = (datum f).I2 t :=
      finalValueIdentification_stationaryFields datum hscreen f t
    have hh := h f t
    linarith
  · intro hzero f t
    rw [hzero f t, sub_zero]
    exact finalValueIdentification_stationaryFields datum hscreen f t

end Cancellation

/-! ## 4. The canonical-upper value field for the actual upper bundle -/

section Composition

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The actual-lane value field with the actual upper pressure bundle.

This is the canonical-upper variant of the actual-lane value field for the ACTUAL
upper bundle (endgameUpperFields_actual_lane, whose pressureUpper is
endgameUpperPressure_actual qU mU pc):

* the lower pressure is the actual lane probe-shifted frozen Campbell readout
  (campbellAveragedFrozenCost - probeShift, the same field as
  frozenProbePressureLowerField);
* the upper pressure is the actual block weighted upper pool shifted by
  -probeShift into the shifted readout convention;
* hvalue follows from FrozenCampbellReadout (lower lane), ActualUpperReadout (the
  isolated upper identification) and the screening data, with the probe constant
  cancelling on both sides.

The only named bridge beyond the existing actual-lane value field is
ActualUpperReadout: the actual upper pool is not a datum field, so its readout
identification is a genuine hypothesis rather than a definitional fact. -/
noncomputable def endgameValueFields_actual_lane_actualUpper
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (qU mU : ℕ) (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    (hupper : ActualUpperReadout qU mU pc datum)
    (hscreen : StationaryScreening datum) : EndgameValueFields A B :=
  endgameValueFields_actual_lane_from_frozenCampbell datum Seed a κ lambda gf q hC
    (fun f t => endgameUpperPressure_actual qU mU pc f t - probeShift f t)
    ((probeShiftedUpperReadout_actualUpper_iff qU mU pc datum).mpr hupper)
    hscreen

/-- The lower pressure of the actual-upper value field is the lane probe-shifted
frozen Campbell readout. -/
theorem endgameValueFields_actual_lane_actualUpper_pressureLower
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (qU mU : ℕ) (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    (hupper : ActualUpperReadout qU mU pc datum)
    (hscreen : StationaryScreening datum) (f : FinalProbeSpace A B) (t : ℝ) :
    (endgameValueFields_actual_lane_actualUpper datum Seed a κ lambda gf q hC
      qU mU pc hupper hscreen).pressureLower f t =
      campbellAveragedFrozenCost Seed a κ lambda (gf f t) q - probeShift f t :=
  rfl

/-- The upper pressure of the actual-upper value field is the actual block weighted
upper pool shifted by -probeShift into the readout convention.  In particular this
is the actual upper bundle field endgameUpperPressure_actual qU mU pc minus the
probe constant, not the unshifted bundle field itself. -/
theorem endgameValueFields_actual_lane_actualUpper_pressureUpper
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (qU mU : ℕ) (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    (hupper : ActualUpperReadout qU mU pc datum)
    (hscreen : StationaryScreening datum) (f : FinalProbeSpace A B) (t : ℝ) :
    (endgameValueFields_actual_lane_actualUpper datum Seed a κ lambda gf q hC
      qU mU pc hupper hscreen).pressureUpper f t =
      endgameUpperPressure_actual qU mU pc f t - probeShift f t :=
  rfl

/-- The value identification of the actual-upper value field, read off pointwise. -/
theorem endgameValueFields_actual_lane_actualUpper_hvalue
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (qU mU : ℕ) (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    (hupper : ActualUpperReadout qU mU pc datum)
    (hscreen : StationaryScreening datum) (f : FinalProbeSpace A B) (t : ℝ) :
    (endgameValueFields_actual_lane_actualUpper datum Seed a κ lambda gf q hC
      qU mU pc hupper hscreen).pressureLower f t =
      (endgameValueFields_actual_lane_actualUpper datum Seed a κ lambda gf q hC
        qU mU pc hupper hscreen).pressureUpper f t :=
  (endgameValueFields_actual_lane_actualUpper datum Seed a κ lambda gf q hC
    qU mU pc hupper hscreen).hvalue f t

end Composition

end OTSelector.Reconstruction
