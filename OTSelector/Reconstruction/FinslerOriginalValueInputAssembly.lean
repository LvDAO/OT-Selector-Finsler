import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit
import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality

/-!
# Assembly of the hvalue input of the final selector from the legal-pressure value lane

The final paper theorem existsUnique_general_finsler_selector_final consumes a
FinslerSelectorFinalInputs structure whose hvalue field is the value
identification conjunct

  hvalue : forall (f : (A union B) x (A union B) ->b R) (t : R),
      pressureLower f t = pressureUpper f t

(FinalValueIdentification in FinslerSelectorFinalInputsWiringAudit.lean).

This module wires that conjunct to the legal-pressure value-equality lane
(FinslerOriginalLegalPressureValueEquality.lean):

* the abstract stationary pressure datum StationaryPressureDatum with its two
  classes Cw (finite weighted kinetic mean) and C2 (finite unweighted second
  moment) and pressures Iw, I2;
* the theorem StationaryPressureDatum.Iw_eq_I2_iff_screening: the value
  identification Iw = I2 is exactly the screening approximation of every
  weighted matching by second-moment matchings (the Palm reserve-screening /
  reserve-zero data of the paper);
* the concrete original Poisson framework theorem
  originalWeightedStationaryInf_eq_secondMomentInf_iff_screening, whose RHS is
  the same screening statement for the literal original focal kinetic cost, and
  the quantitative form originalSecondMomentStationaryInf_le_weighted_add
  (repair budget) whose zero budget special case also gives the identification.

## Contents

1. Abstract wiring.  For an arbitrary probe family F, if the two pressure
   fields are the readouts of the two stationary pressures of a stationary datum
   (hL, hU), then the value identification holds as soon as the datum satisfies
   the screening approximation (valueIdentification_of_stationaryScreening), in
   particular when the two classes coincide (..._of_stationaryClassesEq) and
   when the screening budget is zero (..._of_zeroScreeningBudget).

2. The exact consumer equivalence: finalValueIdentification_iff_stationaryScreening.
   Under the readout identification, the consumer conjunct hvalue is equivalent
   to the screening approximation at every probe and tilt.  No analytic content
   is lost or hidden: hvalue is exactly the Palm reserve-screening statement.

3. The assembled structure.  finalInputs_of_stationaryScreening produces a
   FinslerSelectorFinalInputs from the remaining explicit fields (radius,
   hradius, hprob, hupper) once the pressure fields are readouts of a screening
   stationary datum; finalInputs_of_zeroScreeningBudget is the reserve-zero form.

## Exact remaining gap

The named hypotheses that remain are:

* hL, hU: the readout identification -- the assembly pressureLower and
  pressureUpper are the frozen readouts of the weighted and second-moment
  stationary pressures of the probe-indexed stationary datum.  This is the
  frozen readout convention of the pressure-lower lane and the upper energy
  lane, not an analytic gap in the value identification itself;
* hscreen: the screening approximation (equivalently the Palm reserve-zero /
  zero repair budget data).  In the concrete original lane this is the RHS of
  originalWeightedStationaryInf_eq_secondMomentInf_iff_screening, or the
  budget-zero case of originalSecondMomentStationaryInf_le_weighted_add (whose
  positive budget is the Neumann residual-repair estimate).  Under uniform
  ellipticity of the kinetic coefficient the identification is unconditional;
* the remaining explicit inputs radius, hradius, hprob, hupper are the
  already-named open inputs of the assembly and are unchanged here.

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

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-! ## 1. Abstract wiring: stationary pressure data and screening -/

section AbstractWiring

variable {𝓕 W : Type*} {G Cb : ℝ}

/-- Screening gives the value identification.  If the two pressure fields are
the readouts of the weighted and second-moment stationary pressures of a
stationary datum, then the value identification holds whenever the weighted
class is screened by the second-moment class. -/
theorem valueIdentification_of_stationaryScreening
    {pressureLower pressureUpper : 𝓕 → ℝ → ℝ}
    (datum : 𝓕 → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : 𝓕) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : 𝓕) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    (hscreen : ∀ (f : 𝓕) (v : ℝ) (Q : W), Q ∈ (datum f).Cw → ∀ ε : ℝ, 0 < ε →
      ∃ Q' ∈ (datum f).C2,
        (datum f).K Q' + v * (datum f).P Q' <
          (datum f).K Q + v * (datum f).P Q + ε) :
    ∀ (f : 𝓕) (t : ℝ), pressureLower f t = pressureUpper f t := by
  intro f t
  rw [hL f t, hU f t]
  exact (StationaryPressureDatum.Iw_eq_I2_iff_screening (datum f) t).mpr
    (fun Q hQ ε hε => hscreen f t Q hQ ε hε)

/-- Value identification from equal classes.  This is the unconditionally
identified (uniformly elliptic) regime: all weighted matchings are second-moment
matchings. -/
theorem valueIdentification_of_stationaryClassesEq
    {pressureLower pressureUpper : 𝓕 → ℝ → ℝ}
    (datum : 𝓕 → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : 𝓕) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : 𝓕) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    (hclass : ∀ f : 𝓕, (datum f).Cw = (datum f).C2) :
    ∀ (f : 𝓕) (t : ℝ), pressureLower f t = pressureUpper f t := by
  intro f t
  rw [hL f t, hU f t]
  exact StationaryPressureDatum.Iw_eq_I2_of_classes_eq (datum f) t (hclass f)

/-- Value identification from a zero screening budget.  A screening budget
B <= 0 (the reserve-zero case of the Palm repair estimate) identifies the two
pressure readouts. -/
theorem valueIdentification_of_zeroScreeningBudget
    {pressureLower pressureUpper : 𝓕 → ℝ → ℝ}
    (datum : 𝓕 → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : 𝓕) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : 𝓕) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    {Bres : ℝ} (hBzero : Bres ≤ 0)
    (hscreen : ∀ (f : 𝓕) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∃ Q' ∈ (datum f).C2,
        (datum f).K Q' + v * (datum f).P Q' ≤
          (datum f).K Q + v * (datum f).P Q + Bres) :
    ∀ (f : 𝓕) (t : ℝ), pressureLower f t = pressureUpper f t := by
  intro f t
  rw [hL f t, hU f t]
  refine (StationaryPressureDatum.Iw_eq_I2_iff_screening (datum f) t).mpr ?_
  intro Q hQ ε hε
  obtain ⟨Q', hQ', hle⟩ := hscreen f t Q hQ
  exact ⟨Q', hQ', by linarith⟩

end AbstractWiring

/-! ## 2. The consumer interface of the hvalue field -/

section ConsumerWiring

variable {A B : Set M}

/-- The consumer shape of the hvalue field of FinslerSelectorFinalInputs (the
field itself, definitionally). -/
theorem finalInputs_hvalue_is_valueIdentification
    {μ ν : ProbabilityMeasure M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalValueIdentification inputs.pressureLower inputs.pressureUpper :=
  inputs.hvalue

/-- The hvalue conjunct is exactly the stationary screening statement.  Under
the readout identification of the two pressure fields with the weighted and
second-moment stationary pressures of a probe-indexed stationary datum, the
consumer conjunct is equivalent to the screening approximation at every probe
and tilt.  This is the precise content of the open value input. -/
theorem finalValueIdentification_iff_stationaryScreening
    {W : Type*} {G Cb : ℝ}
    {pressureLower pressureUpper : FinalPressureField A B}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t) :
    FinalValueIdentification pressureLower pressureUpper ↔
      ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
        ∀ ε : ℝ, 0 < ε →
          ∃ Q' ∈ (datum f).C2,
            (datum f).K Q' + v * (datum f).P Q' <
              (datum f).K Q + v * (datum f).P Q + ε := by
  constructor
  · intro hvalue f v Q hQ ε hε
    have hI := (StationaryPressureDatum.Iw_eq_I2_iff_screening (datum f) v).mp
      (by rw [← hL f v, ← hU f v]; exact hvalue f v)
    exact hI Q hQ ε hε
  · intro hscreen
    exact valueIdentification_of_stationaryScreening datum hL hU hscreen

/-- Consumer form: the value identification from the screening approximation. -/
theorem finalValueIdentification_of_stationaryScreening
    {W : Type*} {G Cb : ℝ}
    {pressureLower pressureUpper : FinalPressureField A B}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    (hscreen : ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∀ ε : ℝ, 0 < ε →
        ∃ Q' ∈ (datum f).C2,
          (datum f).K Q' + v * (datum f).P Q' <
            (datum f).K Q + v * (datum f).P Q + ε) :
    FinalValueIdentification pressureLower pressureUpper :=
  valueIdentification_of_stationaryScreening datum hL hU hscreen

/-- Consumer form: the value identification from equal stationary classes (the
unconditional uniformly elliptic regime). -/
theorem finalValueIdentification_of_stationaryClassesEq
    {W : Type*} {G Cb : ℝ}
    {pressureLower pressureUpper : FinalPressureField A B}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    (hclass : ∀ f : FinalProbeSpace A B, (datum f).Cw = (datum f).C2) :
    FinalValueIdentification pressureLower pressureUpper :=
  valueIdentification_of_stationaryClassesEq datum hL hU hclass

/-- Consumer form: the value identification from a zero screening budget. -/
theorem finalValueIdentification_of_zeroScreeningBudget
    {W : Type*} {G Cb : ℝ}
    {pressureLower pressureUpper : FinalPressureField A B}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    {Bres : ℝ} (hBzero : Bres ≤ 0)
    (hscreen : ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∃ Q' ∈ (datum f).C2,
        (datum f).K Q' + v * (datum f).P Q' ≤
          (datum f).K Q + v * (datum f).P Q + Bres) :
    FinalValueIdentification pressureLower pressureUpper :=
  valueIdentification_of_zeroScreeningBudget datum hL hU hBzero hscreen

end ConsumerWiring

/-! ## 3. Assembling the final input structure -/

section Assembly

variable {A B : Set M} {μ ν : ProbabilityMeasure M}
  {hA : IsCompact A} {hB : IsCompact B}
  {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}
  {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}

/-- The hvalue input is discharged by the screening identification.  All other
fields of FinslerSelectorFinalInputs being supplied, the legal-pressure
screening data produce the full input structure for the final theorem. -/
def finalInputs_of_stationaryScreening
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    (hscreen : ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∀ ε : ℝ, 0 < ε →
        ∃ Q' ∈ (datum f).C2,
          (datum f).K Q' + v * (datum f).P Q' <
            (datum f).K Q + v * (datum f).P Q + ε)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius) :
    FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := pressureLower
    pressureUpper := pressureUpper
    radius := radius
    hradius := hradius
    hvalue := finalValueIdentification_of_stationaryScreening datum hL hU hscreen
    hprob := hprob
    hupper := hupper }

/-- The hvalue input is discharged by the unconditional class identification
(the uniformly elliptic regime, e.g. the identity coefficient). -/
def finalInputs_of_stationaryClassesEq
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    (hclass : ∀ f : FinalProbeSpace A B, (datum f).Cw = (datum f).C2)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius) :
    FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := pressureLower
    pressureUpper := pressureUpper
    radius := radius
    hradius := hradius
    hvalue := finalValueIdentification_of_stationaryClassesEq datum hL hU hclass
    hprob := hprob
    hupper := hupper }

/-- The hvalue input is discharged by the zero Palm reserve budget (the
reserve-zero case of the Neumann residual-repair estimate). -/
def finalInputs_of_zeroScreeningBudget
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = (datum f).Iw t)
    (hU : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureUpper f t = (datum f).I2 t)
    {Bres : ℝ} (hBzero : Bres ≤ 0)
    (hscreen : ∀ (f : FinalProbeSpace A B) (v : ℝ) (Q : W), Q ∈ (datum f).Cw →
      ∃ Q' ∈ (datum f).C2,
        (datum f).K Q' + v * (datum f).P Q' ≤
          (datum f).K Q + v * (datum f).P Q + Bres)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius) :
    FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := pressureLower
    pressureUpper := pressureUpper
    radius := radius
    hradius := hradius
    hvalue := finalValueIdentification_of_zeroScreeningBudget datum hL hU hBzero hscreen
    hprob := hprob
    hupper := hupper }

end Assembly

end OTSelector.Reconstruction