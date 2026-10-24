import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit
import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality
import OTSelector.Reconstruction.FinslerOriginalScenePressureWiring

/-!
# Readout glue: the pressure fields as stationary-pressure readouts

The consumer conjunct hvalue of FinslerSelectorFinalInputs is the pointwise
equality pressureLower f t = pressureUpper f t of the two pressure fields of the
final assembly.  FinslerOriginalValueInputAssembly.lean reduced it to the
screening approximation of the stationary pressures Iw (weighted class, finite
weighted kinetic mean) and I2 (second-moment class) of a probe-indexed
StationaryPressureDatum, with two named readout hypotheses hL, hU.

This module closes hL and hU as far as the readout conventions allow:

1. **The canonical stationary readout fields.**
   stationaryLowerField datum := fun f t => (datum f).Iw t and
   stationaryUpperField datum := fun f t => (datum f).I2 t.  These are the
   pressure fields under the frozen stationary readout convention.  The
   unconditional order stationaryLowerField <= stationaryUpperField is the legal
   lane order Iw <= I2.

2. **The readout bridge predicates.**  LowerStationaryReadout pressureLower
   datum := forall f t, pressureLower f t = (datum f).Iw t, and the upper
   analogue.  For the canonical fields the bridges hold by rfl, so hL and hU are
   discharged under the convention.

3. **The frozen pressure-lower lane.**  frozenPressureLower of
   FinslerOriginalScenePressureWiring.lean is the Campbell-averaged frozen cost
   readout.  Its readout bridge is the precise named hypothesis
   FrozenCampbellReadout: the frozen Campbell population readout at (f, t)
   equals the weighted stationary pressure Iw of the datum.  This is the exact
   remaining content of hL for the actual lower lane function.

4. **The final identification and the assembled inputs.**  Given both readout
   bridges and the screening data (reserve-zero / Palm screening), the value
   identification holds for the actual pressure pair, and together with radius,
   hradius, hprob, hupper it produces a full FinslerSelectorFinalInputs.  With
   the canonical stationary fields as the pressure pair, hL and hU are
   discharged by rfl and only the screening data remains.

## Exact remaining gap

* For the canonical stationary fields: the screening approximation (equivalently
  the Palm reserve-zero data) remains; hL and hU are definitional.
* For the actual frozen lower lane function: the named hypothesis
  FrozenCampbellReadout (frozen Campbell readout = weighted stationary pressure
  Iw of the datum at every probe and tilt).
* For the actual upper lane function: the upper readout bridge (upper pressure
  = second-moment stationary pressure I2 of the same datum); the upper lane
  supplies its empirical identification PhysicalKernelUpperBridge separately.
* radius, hradius, hprob, hupper remain the pre-existing open inputs.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M}

/-! ## 1. The canonical stationary readout fields -/

section StationaryFields

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The lower (weighted) pressure field of the frozen stationary readout
convention: the weighted stationary pressure Iw of the probe-indexed datum. -/
noncomputable def stationaryLowerField
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    FinalPressureField A B :=
  fun f t => (datum f).Iw t

/-- The upper (second-moment) pressure field of the frozen stationary readout
convention: the second-moment stationary pressure I2 of the datum. -/
noncomputable def stationaryUpperField
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    FinalPressureField A B :=
  fun f t => (datum f).I2 t

@[simp] theorem stationaryLowerField_apply
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (f : FinalProbeSpace A B) (t : ℝ) :
    stationaryLowerField datum f t = (datum f).Iw t := rfl

@[simp] theorem stationaryUpperField_apply
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (f : FinalProbeSpace A B) (t : ℝ) :
    stationaryUpperField datum f t = (datum f).I2 t := rfl

/-- The unconditional order of the two stationary readout fields: the weighted
pressure is at most the second-moment pressure (the legal lane order Iw <= I2). -/
theorem stationaryLowerField_le_upperField
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (f : FinalProbeSpace A B) (t : ℝ) :
    stationaryLowerField datum f t <= stationaryUpperField datum f t :=
  (datum f).Iw_le_I2 t

end StationaryFields

/-! ## 2. The readout bridge predicates (the named hypotheses hL, hU) -/

section ReadoutBridges

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The lower readout glue (hL): the assembly pressureLower is the frozen
readout of the weighted stationary pressure Iw of the probe-indexed datum. -/
def LowerStationaryReadout
    (pressureLower : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  forall (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t

/-- The upper readout glue (hU): the assembly pressureUpper is the frozen
readout of the second-moment stationary pressure I2 of the same datum. -/
def UpperStationaryReadout
    (pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  forall (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t

/-- Under the frozen stationary readout convention hL holds definitionally. -/
theorem lowerStationaryReadout_canonical
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    LowerStationaryReadout (stationaryLowerField datum) datum :=
  fun _ _ => rfl

/-- Under the frozen stationary readout convention hU holds definitionally. -/
theorem upperStationaryReadout_canonical
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    UpperStationaryReadout (stationaryUpperField datum) datum :=
  fun _ _ => rfl

/-- The screening approximation of the datum: every weighted matching is
approached in signed value from above by a second-moment matching.  This is the
reserve-zero / Palm screening data (the RHS of
StationaryPressureDatum.Iw_eq_I2_iff_screening). -/
def StationaryScreening
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  forall (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw ->
    forall ε : ℝ, 0 < ε ->
      exists Q' : W, Q' ∈ (datum f).C2 ∧
        (datum f).K Q' + v * (datum f).P Q' <
          (datum f).K Q + v * (datum f).P Q + ε

/-- Screening gives the value identification of the canonical stationary
readout fields. -/
theorem finalValueIdentification_stationaryFields
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification (stationaryLowerField datum) (stationaryUpperField datum) := by
  intro f t
  show (datum f).Iw t = (datum f).I2 t
  exact (StationaryPressureDatum.Iw_eq_I2_iff_screening (datum f) t).mpr
    (fun Q hQ ε hε => hscreen f t Q hQ ε hε)

/-- The value identification for the actual pressure pair from the two readout
bridges and the screening data.  This closes hvalue with hL and hU kept as the
precise named hypotheses. -/
theorem finalValueIdentification_of_readoutBridges
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification pressureLower pressureUpper := by
  intro f t
  rw [hL f t, hU f t]
  exact (StationaryPressureDatum.Iw_eq_I2_iff_screening (datum f) t).mpr
    (fun Q hQ ε hε => hscreen f t Q hQ ε hε)

end ReadoutBridges

/-! ## 3. The frozen pressure-lower lane -/

section FrozenLowerLane

variable {A B : Set M} {W : Type*} {G Cb : ℝ}
  {u : M → ℝ} {Seed : ℕ → F.CalibratedSeedWindow u}
  {a : M → Z} {κ : forall j, Measure (Seed j).seed.covector.ker}
  {lambda : Measure Z}

/-- The frozen lower pressure of FinslerOriginalScenePressureWiring.lean as a
pressure field on the probe space of the carrier A union B. -/
noncomputable def frozenLowerField
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ) :
    FinalPressureField A B :=
  frozenPressureLower (K := A ∪ B) Seed a κ lambda g q

/-- The frozen lower field is the Campbell-averaged frozen cost readout. -/
theorem frozenLowerField_apply
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (f : FinalProbeSpace A B) (t : ℝ) :
    frozenLowerField (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) g q f t =
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q := rfl

/-- The precise remaining content of hL for the actual frozen lower lane: the
frozen Campbell population readout equals the weighted stationary pressure Iw of
the probe-indexed datum at every probe and tilt. -/
def FrozenCampbellReadout
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  forall (f : FinalProbeSpace A B) (t : ℝ),
    campbellAveragedFrozenCost Seed a κ lambda (g f t) q = (datum f).Iw t

/-- The readout bridge of the frozen lower field is exactly the Campbell
readout identification. -/
theorem lowerStationaryReadout_frozenLowerField_iff
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    LowerStationaryReadout (frozenLowerField (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q) datum ↔ FrozenCampbellReadout (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) g q datum := by
  constructor
  · intro h f t
    rw [← frozenLowerField_apply (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q f t]
    exact h f t
  · intro h f t
    rw [frozenLowerField_apply (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q f t]
    exact h f t

end FrozenLowerLane

/-! ## 4. Assembling the final inputs with the readout glue -/

section Assembly

variable {A B : Set M} {W : Type*} {G Cb : ℝ} {μ ν : ProbabilityMeasure M}
  {hA : IsCompact A} {hB : IsCompact B}
  {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}
  {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}

/-- The fully assembled final inputs under the frozen stationary readout
convention: hL and hU hold definitionally for the canonical stationary fields,
and the screening data supply hvalue. -/
def finalInputs_of_stationaryConvention
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hscreen : StationaryScreening datum)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u
      (stationaryLowerField datum) radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u
      (stationaryUpperField datum) radius) :
    FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := stationaryLowerField datum
    pressureUpper := stationaryUpperField datum
    radius := radius
    hradius := hradius
    hvalue := finalValueIdentification_stationaryFields datum hscreen
    hprob := hprob
    hupper := hupper }

/-- The fully assembled final inputs for an arbitrary pressure pair once the two
readout bridges and the screening data are supplied. -/
def finalInputs_of_readoutBridges
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum)
    (hscreen : StationaryScreening datum)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius) :
    FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := pressureLower
    pressureUpper := pressureUpper
    radius := radius
    hradius := hradius
    hvalue := finalValueIdentification_of_readoutBridges pressureLower pressureUpper
      datum hL hU hscreen
    hprob := hprob
    hupper := hupper }

end Assembly

end OTSelector.Reconstruction