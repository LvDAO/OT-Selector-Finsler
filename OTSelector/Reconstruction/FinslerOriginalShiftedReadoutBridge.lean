import OTSelector.Reconstruction.FinslerOriginalPressureLowerAssembly
import OTSelector.Reconstruction.FinslerOriginalEndgameValueField

/-!
# The probe-shifted lower readout bridge

The lower lane's pressureLower is the probe-shifted readout
frozenProbePressureLower f t = frozenPressureLower f t - |t| * ‖f‖₊, while the
frozen/value lane's stationary datum readout Iw is unshifted.  This module
settles that bookkeeping.

## What is proved

1. **Shifted readout fields.**  probeShift f t = |t| * (‖f‖₊ : ℝ), the fields
   probeShiftedLowerField datum and probeShiftedUpperField datum
   (Iw t - probeShift, I2 t - probeShift), the shifted readout-bridge
   predicates ProbeShiftedLowerReadout / ProbeShiftedUpperReadout, and the
   identification
   finalValueIdentification_probeShiftedFields: a screened datum identifies its
   shifted pair (the shift is subtracted from both sides).
   finalValueIdentification_of_probeShiftedReadoutBridges transfers this to a
   lane pair through the shifted bridges.

2. **The shift cancels out of the bridge.**  For any lane readout Psi,
   probeShiftedLowerReadout_shift_iff:
   ProbeShiftedLowerReadout (fun f t => Psi f t - probeShift f t) datum is
   equivalent to the unshifted readout identification
   (forall f t, Psi f t = (datum f).Iw t).  Hence a bridge for the unshifted
   frozen Campbell readout automatically yields the shifted hL for the actual
   frozenProbePressureLower.

3. **The shift is absorbed into an actual datum.**  shiftProbeDatum datum c
   shifts the probe by the nonnegative constant c and pays the probe bound with
   G + c; it keeps the same weighted and second-moment classes and competitors.
   Its value is shiftProbeDatum_Iw: Iw of the shifted datum is Iw of the
   original datum minus v * c.  The screening data and the value identification
   are invariant: stationaryScreening_shiftProbeDatum,
   finalValueIdentification_shiftProbeDatum.  Consequently the probe-shifted
   readout is the Iw readout of an actual (sign-of-tilt dependent) shifted
   datum: probeShiftedLowerField_eq_shiftProbeDatum.

4. **The concrete frozen lower lane.**  frozenProbePressureLowerField is the
   lane's actual shifted pressureLower as a pressure field;
   frozenProbePressureLowerField_apply: it equals the Campbell averaged frozen
   cost minus probeShift.  The shifted hL bridge for this field is equivalent to
   the named unshifted bridge
   FrozenCampbellReadout (probeShiftedLowerReadout_frozenProbePressureLower_iff),
   and finalValueIdentification_probeShifted_of_frozenCampbell produces the
   value identification of the lane pair from FrozenCampbellReadout, the shifted
   upper bridge and the screening data (bundled in
   endgameValueFields_probeShifted_of_frozenCampbell).

## Exact remaining named bridge

The single remaining bridge for the lane pair is FrozenCampbellReadout
(FinslerOriginalReadoutGlue.lean:217): for all probes f and tilts t,
campbellAveragedFrozenCost Seed a κ lambda (g f t) q = (datum f).Iw t, i.e. the
unshifted frozen Campbell population readout equals the weighted stationary
pressure of the datum.  The probe shift itself no longer needs to be bridged:
it is definitional in frozenProbePressureLower and cancels/can be absorbed.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability Module
open scoped ContDiff Topology ENNReal NNReal BigOperators CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## 1. The probe constant -/

section ProbeShift

variable {A B : Set M}

/-- The probe constant |t| ‖f‖₊ paid by the shifted lower pressure readout. -/
noncomputable def probeShift (f : FinalProbeSpace A B) (t : ℝ) : ℝ :=
  |t| * (‖f‖₊ : ℝ)

@[simp] theorem probeShift_apply (f : FinalProbeSpace A B) (t : ℝ) :
    probeShift f t = |t| * (‖f‖₊ : ℝ) := rfl

/-- The probe constant is nonnegative. -/
theorem probeShift_nonneg (f : FinalProbeSpace A B) (t : ℝ) : 0 ≤ probeShift f t :=
  mul_nonneg (abs_nonneg t) (by positivity)

/-- On nonnegative tilts the probe constant is t ‖f‖₊. -/
theorem probeShift_of_nonneg (f : FinalProbeSpace A B) {t : ℝ} (ht : 0 ≤ t) :
    probeShift f t = t * (‖f‖₊ : ℝ) := by
  rw [probeShift_apply, abs_of_nonneg ht]

/-- The probe norm is nonnegative in ℝ. -/
theorem nnreal_norm_nonneg (f : FinalProbeSpace A B) : (0 : ℝ) ≤ (‖f‖₊ : ℝ) := by
  have h : (0 : ℝ≥0) ≤ ‖f‖₊ := bot_le
  exact_mod_cast h

/-- On negative tilts the probe constant is -(t ‖f‖₊). -/
theorem probeShift_of_neg (f : FinalProbeSpace A B) {t : ℝ} (ht : t < 0) :
    probeShift f t = -(t * (‖f‖₊ : ℝ)) := by
  rw [probeShift_apply, abs_of_neg ht]
  ring

end ProbeShift

/-! ## 2. Shifted stationary readout fields and their bridges -/

section ShiftedFields

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The probe-shifted lower stationary readout field Iw - probeShift. -/
noncomputable def probeShiftedLowerField
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    FinalPressureField A B :=
  fun f t => (datum f).Iw t - probeShift f t

/-- The probe-shifted upper stationary readout field I2 - probeShift. -/
noncomputable def probeShiftedUpperField
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    FinalPressureField A B :=
  fun f t => (datum f).I2 t - probeShift f t

@[simp] theorem probeShiftedLowerField_apply
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (f : FinalProbeSpace A B) (t : ℝ) :
    probeShiftedLowerField datum f t = (datum f).Iw t - probeShift f t := rfl

@[simp] theorem probeShiftedUpperField_apply
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (f : FinalProbeSpace A B) (t : ℝ) :
    probeShiftedUpperField datum f t = (datum f).I2 t - probeShift f t := rfl

/-- The probe-shifted lower readout bridge of a lane pressureLower. -/
def ProbeShiftedLowerReadout (pressureLower : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  forall (f : FinalProbeSpace A B) (t : ℝ),
    pressureLower f t = (datum f).Iw t - probeShift f t

/-- The probe-shifted upper readout bridge of a lane pressureUpper. -/
def ProbeShiftedUpperReadout (pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  forall (f : FinalProbeSpace A B) (t : ℝ),
    pressureUpper f t = (datum f).I2 t - probeShift f t

/-- The shifted canonical pair satisfies the shifted bridges definitionally. -/
theorem probeShiftedLowerReadout_canonical
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedLowerReadout (probeShiftedLowerField datum) datum :=
  fun _f _t => rfl

/-- The shifted canonical pair satisfies the shifted upper bridge
definitionally. -/
theorem probeShiftedUpperReadout_canonical
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedUpperReadout (probeShiftedUpperField datum) datum :=
  fun _f _t => rfl

/-- **A screened datum identifies its probe-shifted readout pair.**  The probe
shift is subtracted from both sides, so the value identification is unchanged. -/
theorem finalValueIdentification_probeShiftedFields
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification (probeShiftedLowerField datum) (probeShiftedUpperField datum) := by
  intro f t
  show (datum f).Iw t - probeShift f t = (datum f).I2 t - probeShift f t
  have h : (datum f).Iw t = (datum f).I2 t :=
    finalValueIdentification_stationaryFields datum hscreen f t
  linarith

/-- **Value identification of a lane pair from the shifted readout
bridges.** -/
theorem finalValueIdentification_of_probeShiftedReadoutBridges
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ProbeShiftedLowerReadout pressureLower datum)
    (hU : ProbeShiftedUpperReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification pressureLower pressureUpper := by
  intro f t
  rw [hL f t, hU f t]
  exact finalValueIdentification_probeShiftedFields datum hscreen f t

/-- The endgame value field of a lane pair from the shifted readout bridges. -/
noncomputable def endgameValueFields_of_probeShiftedReadoutBridges
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ProbeShiftedLowerReadout pressureLower datum)
    (hU : ProbeShiftedUpperReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) : EndgameValueFields A B where
  pressureLower := pressureLower
  pressureUpper := pressureUpper
  hvalue := finalValueIdentification_of_probeShiftedReadoutBridges
    pressureLower pressureUpper datum hL hU hscreen

end ShiftedFields

/-! ## 3. The shift cancels out of the bridge -/

section Cancellation

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- **The probe shift cancels out of the lower readout bridge**: the shifted
bridge for the shifted field of a lane readout Psi is equivalent to the
unshifted readout identification of Psi. -/
theorem probeShiftedLowerReadout_shift_iff
    (Psi : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedLowerReadout (fun f t => Psi f t - probeShift f t) datum ↔
      (forall (f : FinalProbeSpace A B) (t : ℝ), Psi f t = (datum f).Iw t) := by
  constructor
  · intro h f t
    have hh : Psi f t - probeShift f t = (datum f).Iw t - probeShift f t := h f t
    linarith
  · intro h f t
    show Psi f t - probeShift f t = (datum f).Iw t - probeShift f t
    rw [h f t]

/-- **The probe shift cancels out of the upper readout bridge.** -/
theorem probeShiftedUpperReadout_shift_iff
    (Psi : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedUpperReadout (fun f t => Psi f t - probeShift f t) datum ↔
      (forall (f : FinalProbeSpace A B) (t : ℝ), Psi f t = (datum f).I2 t) := by
  constructor
  · intro h f t
    have hh : Psi f t - probeShift f t = (datum f).I2 t - probeShift f t := h f t
    linarith
  · intro h f t
    show Psi f t - probeShift f t = (datum f).I2 t - probeShift f t
    rw [h f t]

end Cancellation

/-! ## 4. Absorbing the probe shift into an actual datum -/

section ShiftDatum

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The shift of the stationary value set is the shift of the value. -/
private theorem sInf_image_sub_const (Shift : W → ℝ) (C : Set W) (hne : C.Nonempty)
    (hbdd : BddBelow (Shift '' C)) (d : ℝ) :
    sInf ((fun Q => Shift Q - d) '' C) = sInf (Shift '' C) - d := by
  have himg : (fun Q => Shift Q - d) '' C = (fun x => x - d) '' (Shift '' C) := by
    ext y
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Shift Q, ⟨Q, hQ, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨Q, hQ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, rfl⟩
  have hneS : (Shift '' C).Nonempty := hne.image Shift
  have hneT : ((fun x => x - d) '' (Shift '' C)).Nonempty := hneS.image _
  have hbddT : BddBelow ((fun x => x - d) '' (Shift '' C)) := by
    obtain ⟨b, hb⟩ := hbdd
    refine ⟨b - d, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    linarith [hb hx]
  rw [himg]
  apply le_antisymm
  · have hlow : sInf ((fun x => x - d) '' (Shift '' C)) + d ≤ sInf (Shift '' C) := by
      apply le_csInf hneS
      intro x hx
      have hx' : x - d ∈ (fun x => x - d) '' (Shift '' C) := ⟨x, hx, rfl⟩
      linarith [csInf_le hbddT hx']
    linarith
  · apply le_csInf hneT
    rintro y ⟨x, hx, rfl⟩
    linarith [csInf_le hbdd hx]

/-- The stationary datum whose probe is shifted by a nonnegative constant; the
probe bound is paid by G + c, all other data are unchanged. -/
noncomputable def shiftProbeDatum (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) : StationaryPressureDatum W (G + c) Cb where
  K := datum.K
  P := fun Q => datum.P Q - c
  Cw := datum.Cw
  C2 := datum.C2
  C2_subset_Cw := datum.C2_subset_Cw
  kinetic_nonneg := fun Q hQ => datum.kinetic_nonneg Q hQ
  probe_bound := fun Q hQ => by
    have h1 : |datum.P Q - c| ≤ |datum.P Q| + c := by
      rw [abs_le]
      constructor <;>
        nlinarith [neg_abs_le (datum.P Q), le_abs_self (datum.P Q)]
    have h2 := datum.probe_bound Q hQ
    linarith
  competitor := datum.competitor
  competitor_mem := datum.competitor_mem
  kinetic_competitor_le := datum.kinetic_competitor_le
  competitor2 := datum.competitor2
  competitor2_mem := datum.competitor2_mem
  kinetic_competitor2_le := datum.kinetic_competitor2_le

@[simp] theorem shiftProbeDatum_K (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) (Q : W) : (shiftProbeDatum datum c hc).K Q = datum.K Q := rfl

@[simp] theorem shiftProbeDatum_P (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) (Q : W) : (shiftProbeDatum datum c hc).P Q = datum.P Q - c := rfl

@[simp] theorem shiftProbeDatum_Cw (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) : (shiftProbeDatum datum c hc).Cw = datum.Cw := rfl

@[simp] theorem shiftProbeDatum_C2 (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) : (shiftProbeDatum datum c hc).C2 = datum.C2 := rfl

/-- The stationary datum whose probe is shifted up by a nonnegative constant;
the probe bound is again paid by G + c. -/
noncomputable def shiftProbeDatumUp (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) : StationaryPressureDatum W (G + c) Cb where
  K := datum.K
  P := fun Q => datum.P Q + c
  Cw := datum.Cw
  C2 := datum.C2
  C2_subset_Cw := datum.C2_subset_Cw
  kinetic_nonneg := fun Q hQ => datum.kinetic_nonneg Q hQ
  probe_bound := fun Q hQ => by
    have h1 : |datum.P Q + c| ≤ |datum.P Q| + c := by
      rw [abs_le]
      constructor <;>
        nlinarith [neg_abs_le (datum.P Q), le_abs_self (datum.P Q)]
    have h2 := datum.probe_bound Q hQ
    linarith
  competitor := datum.competitor
  competitor_mem := datum.competitor_mem
  kinetic_competitor_le := datum.kinetic_competitor_le
  competitor2 := datum.competitor2
  competitor2_mem := datum.competitor2_mem
  kinetic_competitor2_le := datum.kinetic_competitor2_le

@[simp] theorem shiftProbeDatumUp_K (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) (Q : W) : (shiftProbeDatumUp datum c hc).K Q = datum.K Q := rfl

@[simp] theorem shiftProbeDatumUp_P (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) (Q : W) : (shiftProbeDatumUp datum c hc).P Q = datum.P Q + c := rfl

@[simp] theorem shiftProbeDatumUp_C2 (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) : (shiftProbeDatumUp datum c hc).C2 = datum.C2 := rfl

/-- **The probe shift is absorbed into the value**: the shifted datum has value
Iw - v * c. -/
theorem shiftProbeDatum_Iw (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) (v : ℝ) :
    (shiftProbeDatum datum c hc).Iw v = datum.Iw v - v * c := by
  have hLHS : (shiftProbeDatum datum c hc).Iw v =
      sInf ((fun Q => datum.K Q + v * (datum.P Q - c)) '' datum.Cw) := rfl
  rw [hLHS]
  have hfun : (fun Q => datum.K Q + v * (datum.P Q - c)) =
      (fun Q => (datum.K Q + v * datum.P Q) - v * c) := by
    funext Q
    ring
  rw [hfun]
  have hRHS : datum.Iw v = sInf ((fun Q => datum.K Q + v * datum.P Q) '' datum.Cw) := rfl
  rw [hRHS]
  exact sInf_image_sub_const (fun Q => datum.K Q + v * datum.P Q) datum.Cw
    (StationaryPressureDatum.nonempty_Cw datum) (StationaryPressureDatum.bddBelow_Cw datum v) (v * c)

/-- **The screening data is invariant under the probe shift.** -/
theorem stationaryScreening_shiftProbeDatum
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) (c : ℝ) (hc : 0 ≤ c)
    (hscreen : StationaryScreening datum) :
    StationaryScreening (fun f => shiftProbeDatum (datum f) c hc) := by
  intro f v Q hQ ε hε
  obtain ⟨Q', hQ', hlt⟩ := hscreen f v Q hQ ε hε
  refine ⟨Q', ?_, ?_⟩
  · rw [shiftProbeDatum_C2]
    exact hQ'
  · simp only [shiftProbeDatum_K, shiftProbeDatum_P]
    linarith

/-- **The upward probe shift is absorbed into the value**: the upward shifted
datum has value Iw + v * c. -/
theorem shiftProbeDatumUp_Iw (datum : StationaryPressureDatum W G Cb) (c : ℝ)
    (hc : 0 ≤ c) (v : ℝ) :
    (shiftProbeDatumUp datum c hc).Iw v = datum.Iw v + v * c := by
  have hLHS : (shiftProbeDatumUp datum c hc).Iw v =
      sInf ((fun Q => datum.K Q + v * (datum.P Q + c)) '' datum.Cw) := rfl
  rw [hLHS]
  have hfun : (fun Q => datum.K Q + v * (datum.P Q + c)) =
      (fun Q => (datum.K Q + v * datum.P Q) + v * c) := by
    funext Q
    ring
  rw [hfun]
  have hRHS : datum.Iw v = sInf ((fun Q => datum.K Q + v * datum.P Q) '' datum.Cw) := rfl
  rw [hRHS]
  have h := sInf_image_sub_const (fun Q => datum.K Q + v * datum.P Q) datum.Cw
    (StationaryPressureDatum.nonempty_Cw datum) (StationaryPressureDatum.bddBelow_Cw datum v)
    (-(v * c))
  simpa [sub_neg_eq_add] using h

/-- **The screening data is invariant under the upward probe shift.** -/
theorem stationaryScreening_shiftProbeDatumUp
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) (c : ℝ) (hc : 0 ≤ c)
    (hscreen : StationaryScreening datum) :
    StationaryScreening (fun f => shiftProbeDatumUp (datum f) c hc) := by
  intro f v Q hQ ε hε
  obtain ⟨Q', hQ', hlt⟩ := hscreen f v Q hQ ε hε
  refine ⟨Q', ?_, ?_⟩
  · rw [shiftProbeDatumUp_C2]
    exact hQ'
  · simp only [shiftProbeDatumUp_K, shiftProbeDatumUp_P]
    linarith

end ShiftDatum

/-! ## 5. The probe-shifted readout as the value of an actual datum -/

section Absorbed

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- **The probe-shifted readout is the Iw readout of an actual (sign-of-tilt
dependent) shifted datum**: the probe constant is absorbed into the probe of the
stationary datum. -/
theorem probeShiftedLowerField_eq_shiftProbeDatum
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (f : FinalProbeSpace A B) (t : ℝ) :
    probeShiftedLowerField datum f t =
      if 0 ≤ t then
        (shiftProbeDatum (datum f) (‖f‖₊ : ℝ) (nnreal_norm_nonneg f)).Iw t
      else
        (shiftProbeDatumUp (datum f) (‖f‖₊ : ℝ) (nnreal_norm_nonneg f)).Iw t := by
  have h1 : (shiftProbeDatum (datum f) (‖f‖₊ : ℝ) (nnreal_norm_nonneg f)).Iw t =
      (datum f).Iw t - t * (‖f‖₊ : ℝ) :=
    shiftProbeDatum_Iw (datum f) _ (nnreal_norm_nonneg f) t
  have h2 : (shiftProbeDatumUp (datum f) (‖f‖₊ : ℝ) (nnreal_norm_nonneg f)).Iw t =
      (datum f).Iw t + t * (‖f‖₊ : ℝ) :=
    shiftProbeDatumUp_Iw (datum f) _ (nnreal_norm_nonneg f) t
  split_ifs with ht
  · rw [h1, probeShiftedLowerField_apply, probeShift_of_nonneg f ht]
  · rw [h2, probeShiftedLowerField_apply, probeShift_of_neg f (lt_of_not_ge ht)]
    ring

/-- **The value identification of the shifted canonical pair is the value
identification of an actual shifted datum family** (at each tilt). -/
theorem finalValueIdentification_shiftProbeDatum
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) (c : ℝ) (hc : 0 ≤ c)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification
      (stationaryLowerField (fun f => shiftProbeDatum (datum f) c hc))
      (stationaryUpperField (fun f => shiftProbeDatum (datum f) c hc)) :=
  finalValueIdentification_stationaryFields _
    (stationaryScreening_shiftProbeDatum datum c hc hscreen)

end Absorbed

/-! ## 6. The concrete frozen lower lane -/

section FrozenLane

variable {A B : Set M} {W : Type*} {G Cb : ℝ}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : forall j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}

/-- The actual probe-shifted frozen lower pressure of the lane, as a pressure
field on the probe space of the carrier A union B. -/
noncomputable def frozenProbePressureLowerField
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ) : FinalPressureField A B :=
  frozenProbePressureLower (K := A ∪ B) Seed a κ lambda g q

/-- The lane field is the Campbell averaged frozen cost minus the probe
constant. -/
theorem frozenProbePressureLowerField_apply
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (f : FinalProbeSpace A B) (t : ℝ) :
    frozenProbePressureLowerField Seed a κ lambda g q f t =
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q - probeShift f t := rfl

/-- **The shifted hL bridge for the actual lane field is exactly the named
unshifted FrozenCampbellReadout.**  The probe shift cancels. -/
theorem probeShiftedLowerReadout_frozenProbePressureLower_iff
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ProbeShiftedLowerReadout
        (frozenProbePressureLowerField Seed a κ lambda g q) datum ↔
      FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        g q datum := by
  constructor
  · intro h f t
    have hh : campbellAveragedFrozenCost Seed a κ lambda (g f t) q - probeShift f t =
        (datum f).Iw t - probeShift f t := by
      simpa only [frozenProbePressureLowerField_apply] using h f t
    linarith
  · intro h f t
    show frozenProbePressureLowerField Seed a κ lambda g q f t =
      (datum f).Iw t - probeShift f t
    rw [frozenProbePressureLowerField_apply, h f t]

/-- **Value identification of the actual lane pair from the named unshifted
FrozenCampbellReadout, the shifted upper bridge and the screening data.** -/
theorem finalValueIdentification_probeShifted_of_frozenCampbell
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hL : forall (f : FinalProbeSpace A B) (t : ℝ),
      pressureLower f t = frozenProbePressureLowerField Seed a κ lambda g q f t)
    (hU : ProbeShiftedUpperReadout pressureUpper datum)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      g q datum)
    (hscreen : StationaryScreening datum) :
    FinalValueIdentification pressureLower pressureUpper := by
  intro f t
  rw [hL f t, hU f t, frozenProbePressureLowerField_apply, hC f t]
  exact finalValueIdentification_probeShiftedFields datum hscreen f t

/-- The endgame value field of the actual lane pair from the named unshifted
FrozenCampbellReadout, the shifted upper bridge and the screening data. -/
noncomputable def endgameValueFields_probeShifted_of_frozenCampbell
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hL : forall (f : FinalProbeSpace A B) (t : ℝ),
      pressureLower f t = frozenProbePressureLowerField Seed a κ lambda g q f t)
    (hU : ProbeShiftedUpperReadout pressureUpper datum)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      g q datum)
    (hscreen : StationaryScreening datum) : EndgameValueFields A B where
  pressureLower := pressureLower
  pressureUpper := pressureUpper
  hvalue := finalValueIdentification_probeShifted_of_frozenCampbell
    pressureLower pressureUpper datum Seed a κ lambda g q hL hU hC hscreen

end FrozenLane

end OTSelector.Reconstruction