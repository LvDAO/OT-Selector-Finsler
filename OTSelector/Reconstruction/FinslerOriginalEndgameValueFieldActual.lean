import OTSelector.Reconstruction.FinslerOriginalShiftedReadoutBridge

/-!
# The endgame value field for the actual lane

This module assembles the actual-lane value field end to end from three
ingredients: the frozen Campbell readout bridge, the upper-lane probe-shifted
pairing, and the stationary screening data.

## What is produced

1. **The actual-lane value field from the named bridge.**  For an arbitrary
   probe-indexed stationary datum,
   endgameValueFields_actual_lane_from_frozenCampbell produces
   EndgameValueFields with
   pressureLower f t = campbellAveragedFrozenCost Seed a κ lambda (g f t) q
     - probeShift f t,
   pressureUpper an arbitrary lane upper pressure supplied with its shifted
   readout bridge ProbeShiftedUpperReadout, and hvalue through
   endgameValueFields_probeShifted_of_frozenCampbell.

2. **The strongest producer.**  When the upper lane is itself the shifted
   stationary readout field probeShiftedUpperField datum (so its bridge holds
   definitionally), only FrozenCampbellReadout and StationaryScreening remain:
   endgameValueFields_actual_lane_canonicalUpper_from_frozenCampbell.

3. **The datum is not arbitrary.**  originalLaneDatumFamily instantiates the
   datum family from the actual legal original input lane construction
   (originalLegalStationaryDatum, FinslerOriginalStationaryDatumConstruction),
   whose competitor is produced by originalSecondMomentSubclass_nonempty from
   the legal lane framework hypotheses.  In the uniformly elliptic regime its
   screening data is
   stationaryScreening_originalLaneDatumFamily_of_uniform_elliptic, so the
   actual-lane value fields
   endgameValueFields_originalLane_from_frozenCampbell and
   endgameValueFields_originalLane_canonicalUpper_from_frozenCampbell need only

   * FrozenCampbellReadout (the single named bridge; exact type below),
   * the upper-lane shifted pairing (only in the non-canonical-upper version),
   * the legal lane framework hypotheses hF, hw, hq, hgap, hbounds, pi,
     [IsFiniteMeasure pi], hpi, horder, hg, hgb,
   * kinetic nonnegativity hkin_nonneg and uniform ellipticity c > 0 with
     c * sum v^2 <= D.originalFocalKinetic gap.

## Exact type of the single named bridge

  FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) g q
    datum : Prop
  := forall (f : FinalProbeSpace A B) (t : ℝ),
       campbellAveragedFrozenCost Seed a κ lambda (g f t) q = (datum f).Iw t,

i.e. the unshifted frozen Campbell population readout equals the weighted
stationary pressure Iw of the datum at every probe and tilt.  The probe shift
itself is already handled (FinslerOriginalShiftedReadoutBridge): it is
definitional in the lane's pressureLower, cancels out of the readout bridge and
is absorbable into a stationary datum.

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

/-! ## 1. The actual-lane value field from the named bridge -/

section ActualLane

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- **The actual-lane value field from the named frozen Campbell readout
bridge, the upper-lane shifted pairing and the screening data.**

The lower pressure is the lane's probe-shifted frozen readout
campbellAveragedFrozenCost - probeShift, the upper pressure is a supplied lane
upper pressure with its shifted readout bridge. -/
noncomputable def endgameValueFields_actual_lane_from_frozenCampbell
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (pressureUpper : FinalPressureField A B)
    (hU : ProbeShiftedUpperReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) : EndgameValueFields A B where
  pressureLower := fun f t =>
    campbellAveragedFrozenCost Seed a κ lambda (gf f t) q - probeShift f t
  pressureUpper := pressureUpper
  hvalue := finalValueIdentification_probeShifted_of_frozenCampbell
    _ pressureUpper datum Seed a κ lambda gf q
    (fun f t => (frozenProbePressureLowerField_apply Seed a κ lambda gf q f t).symm)
    hU hC hscreen

/-- **The strongest producer**: when the upper lane is the shifted stationary
readout field itself (its bridge holds definitionally), only the frozen Campbell
readout bridge and the screening data remain. -/
noncomputable def endgameValueFields_actual_lane_canonicalUpper_from_frozenCampbell
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (hscreen : StationaryScreening datum) : EndgameValueFields A B where
  pressureLower := fun f t =>
    campbellAveragedFrozenCost Seed a κ lambda (gf f t) q - probeShift f t
  pressureUpper := probeShiftedUpperField datum
  hvalue := finalValueIdentification_probeShifted_of_frozenCampbell
    _ _ datum Seed a κ lambda gf q
    (fun f t => (frozenProbePressureLowerField_apply Seed a κ lambda gf q f t).symm)
    (probeShiftedUpperReadout_canonical datum) hC hscreen

/-- The lower pressure field of the actual-lane value field is the probe-shifted
frozen Campbell readout. -/
@[simp] theorem endgameValueFields_actual_lane_pressureLower
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (pressureUpper : FinalPressureField A B)
    (hU : ProbeShiftedUpperReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) (f : FinalProbeSpace A B) (t : ℝ) :
    (endgameValueFields_actual_lane_from_frozenCampbell datum Seed a κ lambda gf q
      hC pressureUpper hU hscreen).pressureLower f t =
      campbellAveragedFrozenCost Seed a κ lambda (gf f t) q - probeShift f t := rfl

/-- Nonemptiness of the actual-lane value field from the named bridge. -/
theorem endgameValueFields_nonempty_actual_lane_from_frozenCampbell
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (pressureUpper : FinalPressureField A B)
    (hU : ProbeShiftedUpperReadout pressureUpper datum)
    (hscreen : StationaryScreening datum) : Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_actual_lane_from_frozenCampbell datum Seed a κ lambda gf q
    hC pressureUpper hU hscreen⟩

/-- Nonemptiness of the strongest-producer actual-lane value field. -/
theorem endgameValueFields_nonempty_actual_lane_canonicalUpper_from_frozenCampbell
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : forall j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (gf : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q datum)
    (hscreen : StationaryScreening datum) : Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_actual_lane_canonicalUpper_from_frozenCampbell datum Seed a κ lambda
    gf q hC hscreen⟩

end ActualLane

/-! ## 2. The datum from the actual legal original input lane -/

section OriginalLane

variable {A B : Set M} {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {μ ν : Measure ℝ}

/-- **The probe-indexed stationary datum family of the actual legal original
input lane.**  Its competitor is the matching constructed by
originalSecondMomentSubclass_nonempty from the legal lane framework
hypotheses. -/
noncomputable def originalLaneDatumFamily
    (A B : Set M) (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ D.originalFocalKinetic gap a b v) :
    FinalProbeSpace A B → StationaryPressureDatum
      (LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g) G
      (legalKineticReadout
        (Classical.choose (D.originalSecondMomentSubclass_nonempty
          hF hw hq hgap hbounds pi hpi horder hg hgb))) :=
  fun _ => originalLegalStationaryDatum D hF hw hq hgap hbounds pi hpi horder hg hgb
    hkin_nonneg

/-- **The screening data of the actual original legal lane datum family**, in the
uniformly elliptic regime. -/
theorem stationaryScreening_originalLaneDatumFamily_of_uniform_elliptic
    (A B : Set M) (D : OriginalSeedConditionalMoments S w μ ν)
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
      (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb
        hkin_nonneg) :=
  stationaryScreening_originalLegalStationaryDatum_of_uniform_elliptic
    D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin

/-- **The actual original-lane value field**, with an upper lane pressure supplied
together with its shifted readout bridge, in the uniformly elliptic regime: the
only named bridge is FrozenCampbellReadout. -/
noncomputable def endgameValueFields_originalLane_from_frozenCampbell
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
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v)
    {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : forall j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {gf : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q
      (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb
        hkin_nonneg))
    (pressureUpper : FinalPressureField A B)
    (hU : ProbeShiftedUpperReadout pressureUpper
      (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb
        hkin_nonneg)) :
    EndgameValueFields A B :=
  endgameValueFields_actual_lane_from_frozenCampbell
    (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg)
    Seed a κ lambda gf q hC pressureUpper hU
    (stationaryScreening_originalLaneDatumFamily_of_uniform_elliptic
      A B D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin)

/-- **The strongest actual original-lane value field**: the upper lane is the
shifted stationary readout field of the actual legal datum family, so the only
named bridge is FrozenCampbellReadout, in the uniformly elliptic regime. -/
noncomputable def endgameValueFields_originalLane_canonicalUpper_from_frozenCampbell
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
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v)
    {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : forall j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {gf : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q
      (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb
        hkin_nonneg)) :
    EndgameValueFields A B :=
  endgameValueFields_actual_lane_canonicalUpper_from_frozenCampbell
    (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg)
    Seed a κ lambda gf q hC
    (stationaryScreening_originalLaneDatumFamily_of_uniform_elliptic
      A B D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin)

/-- Nonemptiness of the actual original-lane value field with supplied upper
lane, in the uniformly elliptic regime (single named bridge:
FrozenCampbellReadout). -/
theorem endgameValueFields_nonempty_originalLane_from_frozenCampbell
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
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v)
    {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : forall j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {gf : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q
      (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb
        hkin_nonneg))
    (pressureUpper : FinalPressureField A B)
    (hU : ProbeShiftedUpperReadout pressureUpper
      (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb
        hkin_nonneg)) :
    Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_originalLane_from_frozenCampbell
    D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin hC
    pressureUpper hU⟩

/-- Nonemptiness of the strongest actual original-lane value field, in the
uniformly elliptic regime (single named bridge: FrozenCampbellReadout). -/
theorem endgameValueFields_nonempty_originalLane_canonicalUpper_from_frozenCampbell
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
      c * ∑ i, v i ^ 2 ≤ D.originalFocalKinetic gap a b v)
    {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : forall j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {gf : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      gf q
      (originalLaneDatumFamily A B D hF hw hq hgap hbounds pi hpi horder hg hgb
        hkin_nonneg)) :
    Nonempty (EndgameValueFields A B) :=
  ⟨endgameValueFields_originalLane_canonicalUpper_from_frozenCampbell
    D hF hw hq hgap hbounds pi hpi horder hg hgb hkin_nonneg hc hkin hC⟩

end OriginalLane

end OTSelector.Reconstruction