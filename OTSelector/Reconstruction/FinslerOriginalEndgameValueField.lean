import OTSelector.Reconstruction.FinslerOriginalStationaryDatumConstruction

/-!
# The endgame value field of the selector's final inputs

This module bundles the last value identification of the general Finsler
assembly as one structure, EndgameValueFields, and produces it from the
stationary screening data of the actual legal lane in the uniformly elliptic
regime.

The bundle is

  pressureLower : FinalPressureField A B,
  pressureUpper : FinalPressureField A B,
  hvalue : FinalValueIdentification pressureLower pressureUpper.

## Two lanes of the construction

1. **Canonical stationary readout pair.**  For a probe-indexed stationary
   pressure datum with screening data (FinslerOriginalReadoutGlue's
   StationaryScreening), the canonical fields stationaryLowerField datum and
   stationaryUpperField datum are value-identified
   (endgameValueFields_canonical, using finalValueIdentification_stationaryFields).

2. **The actual legal lane.**  The actual stationary pressure datum over the
   legal matching space (legalStationaryDatum, and originalLegalStationaryDatum
   for the original focal kinetic cost) satisfies the screening data in the
   uniformly elliptic regime, hence its canonical pair is value-identified
   (endgameValueFields_legalDatum_of_uniform_elliptic,
   endgameValueFields_originalLegalDatum_of_uniform_elliptic), and
   endgameValueFields_nonempty_* record the resulting nonemptiness.

## The exact readout bridge needed for an arbitrary lane pair

The lane's own pressure fields pressureLower, pressureUpper admit a value field
as soon as they agree with a screened canonical stationary pair through the
readout bridges of FinslerOriginalReadoutGlue:

  hL : LowerStationaryReadout pressureLower datum
       (forall f t, pressureLower f t = (datum f).Iw t),
  hU : UpperStationaryReadout pressureUpper datum
       (forall f t, pressureUpper f t = (datum f).I2 t).

That transfer is endgameValueFields_of_readoutBridges: it consumes exactly
those two named bridges plus the screening data, and produces the bundle for
the lane pair.  Equivalently, for a lane pair that is literally the canonical
stationary readout fields the bridges are definitional (rfl) and no extra data
is needed.

## Remaining named data

* the probe-indexed datum, its (kinetic/probe) competitor data, and the
  screening data in the non-elliptic regime;
* in the uniformly elliptic regime only: kinetic nonnegativity, the probe bound,
  the ellipticity c > 0 with c * sum v^2 <= kin (resp. originalFocalKinetic),
  and (only for the original lane competitor) the legal lane framework
  hypotheses.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability Module
open scoped ContDiff Topology ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The value-field bundle -/

section Bundle

variable {A B : Set M}

/-- **The endgame value field of the selector's final inputs.**

It bundles the two pressure fields together with their identification, which is
exactly the hvalue field of the final inputs structure. -/
structure EndgameValueFields (A B : Set M) where
  pressureLower : FinalPressureField A B
  pressureUpper : FinalPressureField A B
  hvalue : FinalValueIdentification pressureLower pressureUpper

/-- The bundled value identification, applied. -/
@[simp] theorem EndgameValueFields.hvalue_apply (fields : EndgameValueFields A B)
    (f : FinalProbeSpace A B) (t : ℝ) :
    fields.pressureLower f t = fields.pressureUpper f t :=
  fields.hvalue f t

variable {W : Type*} {G Cb : ℝ}

/-- **The canonical stationary readout pair is an endgame value field** as soon
as the datum has screening data. -/
noncomputable def endgameValueFields_canonical
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hscreen : StationaryScreening datum) : EndgameValueFields A B where
  pressureLower := stationaryLowerField datum
  pressureUpper := stationaryUpperField datum
  hvalue := finalValueIdentification_stationaryFields datum hscreen

/-- **The lane pair with readout bridges is an endgame value field.**

This is the exact transfer needed for the actual lane pressures: it consumes the
two named readout bridges hL, hU to a screened stationary datum and nothing
else. -/
noncomputable def endgameValueFields_of_readoutBridges
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) : EndgameValueFields A B where
  pressureLower := pressureLower
  pressureUpper := pressureUpper
  hvalue := finalValueIdentification_of_readoutBridges pressureLower pressureUpper datum
    hL hU hscreen

/-- Nonemptiness of the bundle from a screened datum (canonical pair). -/
theorem endgameValueFields_nonempty_canonical
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hscreen : StationaryScreening datum) : Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_canonical datum hscreen⟩

/-- Nonemptiness of the bundle from explicit readout bridges to a screened
datum. -/
theorem endgameValueFields_nonempty_of_readoutBridges
    (pressureLower pressureUpper : FinalPressureField A B)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hL : LowerStationaryReadout pressureLower datum)
    (hU : UpperStationaryReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) : Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_of_readoutBridges pressureLower pressureUpper datum hL hU hscreen⟩

end Bundle

/-! ## The actual legal lane -/

section LegalLane

variable {A B : Set M} {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {G Cb : ℝ}

/-- **The endgame value field of the actual legal datum**, in the uniformly
elliptic regime: the canonical stationary readout pair of legalStationaryDatum
is value-identified. -/
noncomputable def endgameValueFields_legalDatum_of_uniform_elliptic
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v) :
    EndgameValueFields A B :=
  endgameValueFields_canonical _
    (stationaryScreening_legalStationaryDatum_of_uniform_elliptic
      hkin_nonneg hgb Q0 hQ0 hCb hc hkin)

/-- Nonemptiness of the endgame value field of the actual legal datum. -/
theorem endgameValueFields_nonempty_legalDatum_of_uniform_elliptic
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v) :
    Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_legalDatum_of_uniform_elliptic hkin_nonneg hgb Q0 hQ0 hCb hc hkin⟩

end LegalLane

/-! ## The actual original legal lane -/

section OriginalLane

variable {A B : Set M} {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {μ ν : Measure ℝ}

/-- In the uniformly elliptic regime the second-moment class of the actual
original legal datum is everything. -/
theorem originalLegalStationaryDatum_C2_eq_univ_of_uniform_elliptic
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ D.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v) :
    (originalLegalStationaryDatum D hF hw hq hgap hbounds pi hpi horder hg hgb
      hkin_nonneg).C2 = Set.univ :=
  legalStationaryDatum_C2_eq_univ_of_uniform_elliptic (kin := D.originalFocalKinetic gap)
    hkin_nonneg hgb
    (Classical.choose (D.originalSecondMomentSubclass_nonempty
      hF hw hq hgap hbounds pi hpi horder hg hgb))
    (Classical.choose_spec (D.originalSecondMomentSubclass_nonempty
      hF hw hq hgap hbounds pi hpi horder hg hgb))
    le_rfl hc hkin

/-- **The screening data of the actual original legal datum**, in the uniformly
elliptic regime. -/
theorem stationaryScreening_originalLegalStationaryDatum_of_uniform_elliptic
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ D.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v) :
    StationaryScreening
      (fun _ : FinalProbeSpace A B =>
        originalLegalStationaryDatum D hF hw hq hgap hbounds pi hpi horder hg hgb
          hkin_nonneg) :=
  stationaryScreening_of_c2_univ _
    (fun _ => originalLegalStationaryDatum_C2_eq_univ_of_uniform_elliptic
      D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin)

/-- **The endgame value field of the actual original legal datum**, in the
uniformly elliptic regime. -/
noncomputable def endgameValueFields_originalLegalDatum_of_uniform_elliptic
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ D.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v) :
    EndgameValueFields A B :=
  endgameValueFields_canonical _
    (stationaryScreening_originalLegalStationaryDatum_of_uniform_elliptic
      D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin)

/-- Nonemptiness of the endgame value field of the actual original legal
datum. -/
theorem endgameValueFields_nonempty_originalLegalDatum_of_uniform_elliptic
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ D.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v) :
    Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_originalLegalDatum_of_uniform_elliptic
    D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin⟩

end OriginalLane

end OTSelector.Reconstruction
