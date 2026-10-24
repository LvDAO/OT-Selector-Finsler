import OTSelector.Reconstruction.FinslerOriginalScreeningData
import OTSelector.Reconstruction.FinslerStationaryPalmReadouts

/-!
# The actual stationary pressure datum over the legal matching space

FinslerOriginalScreeningData.lean leaves open the construction of an actual
StationaryPressureDatum over the legal matching space (its remaining data (i)):
one competitor matching with finite second moment, serving both the weighted
and the second-moment competitor role.

This module constructs that datum:

* legalKineticReadout / legalProbeReadout: the two Palm readouts of a legal
  weighted stationary matching.  Their sum is exactly
  LegalWeightedStationaryPoissonMatching.value, so the datum pressure
  K + v * P is the actual legal pressure of the matching.
* legalStationaryDatum: the StationaryPressureDatum over the legal matching
  space, with weighted class everything and second-moment class the legal
  finite-second-moment subclass.  The competitor is any matching in the legal
  second-moment subclass, with bound Cb its kinetic readout.
* legalStationaryDatum_C2_eq_univ_of_uniform_elliptic: in the uniformly
  elliptic regime the second-moment class is everything.
* stationaryScreening_legalStationaryDatum_of_uniform_elliptic: consequently the
  screening data holds for the actual datum (probe family).
* finalValueIdentification_legalStationaryDatum_of_uniform_elliptic and
  finalValueIdentification_stationaryFields_legalDatum_of_uniform_elliptic: the
  resulting value identification for the actual pressure pair, with the readout
  bridges hL/hU as named hypotheses (or discharged definitionally for the
  canonical stationary fields).
* originalLegalStationaryDatum: the same datum for the actual original focal
  kinetic cost of the original legal lane, using
  originalSecondMomentSubclass_nonempty for the competitor.
* stationaryScreening_originalLegalStationaryDatum_of_uniform_elliptic and
  finalValueIdentification_..._originalLegalStationaryDatum...: screening and
  the value identification for that actual datum in the elliptic regime.

## Remaining named data

* the legal lane framework hypotheses hF, hw, hq, hgap, hbounds, pi, hpi,
  horder, hg, hgb (needed only for the existence of the second-moment
  competitor in the original lane);
* nonnegativity of the (original focal) kinetic coefficient and the probe bound
  hgb;
* uniform ellipticity c > 0 with c * sum v^2 <= kin (or originalFocalKinetic);
* the readout bridges hL/hU, unless the pressure pair is taken to be the
  canonical stationary readout fields, where they hold by rfl.

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

/-! ## The stationary pressure datum over the legal matching space -/

section Datum

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {G Cb : ℝ}

/-- **The actual stationary pressure datum over the legal matching space.**

The kinetic readout is the Palm kinetic energy, the probe readout the Palm probe,
the weighted class everything and the second-moment class the legal
finite-second-moment subclass.  One matching in that subclass serves as both
competitors. -/
noncomputable def legalStationaryDatum
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb) :
    StationaryPressureDatum (LegalWeightedStationaryPoissonMatching q α β kin g) G Cb :=
  { K := legalKineticReadout
    P := legalProbeReadout
    Cw := Set.univ
    C2 := {Q | Q.secondMomentSubclass}
    C2_subset_Cw := fun Q _ => Set.mem_univ Q
    kinetic_nonneg := fun Q _ => legalKineticReadout_nonneg hkin_nonneg Q
    probe_bound := fun Q _ => legalProbeReadout_abs_le hgb Q
    competitor := Q0
    competitor_mem := Set.mem_univ Q0
    kinetic_competitor_le := hCb
    competitor2 := Q0
    competitor2_mem := hQ0
    kinetic_competitor2_le := hCb }

/-- The second-moment class of the legal datum is the legal subclass. -/
theorem legalStationaryDatum_C2
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb) :
    (legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb).C2 = {Q | Q.secondMomentSubclass} :=
  rfl

/-- The weighted stationary pressure of the legal datum is exactly the legal
weighted stationary infimum of the Palm readouts. -/
theorem legalStationaryDatum_Iw
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb) (v : ℝ) :
    (legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb).Iw v =
      sInf ((fun Q : LegalWeightedStationaryPoissonMatching q α β kin g =>
        legalKineticReadout Q + v * legalProbeReadout Q) '' Set.univ) :=
  rfl

/-- **The uniformly elliptic regime: the second-moment class of the legal datum
is everything.** -/
theorem legalStationaryDatum_C2_eq_univ_of_uniform_elliptic
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v) :
    (legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb).C2 = Set.univ :=
  legalSecondMomentSubset_eq_univ_of_uniform_elliptic hc hkin

end Datum

/-! ## Screening for the actual datum, and the value identification -/

section Screening

variable {A B : Set M} {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {G Cb : ℝ}

/-- **The screening data for the actual legal datum**, in the uniformly elliptic
regime: the constant probe family of the actual datum satisfies
StationaryScreening. -/
theorem stationaryScreening_legalStationaryDatum_of_uniform_elliptic
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v) :
    StationaryScreening
      (fun _ : FinalProbeSpace A B => legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb) :=
  stationaryScreening_of_c2_univ _
    (fun _ => legalStationaryDatum_C2_eq_univ_of_uniform_elliptic hkin_nonneg hgb Q0 hQ0 hCb hc hkin)

/-- **The value identification for the actual pressure pair** once the readout
bridges to the actual legal datum hold, in the uniformly elliptic regime. -/
theorem finalValueIdentification_legalStationaryDatum_of_uniform_elliptic
    (pressureLower pressureUpper : FinalPressureField A B)
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v)
    (hL : LowerStationaryReadout pressureLower
      (fun _ : FinalProbeSpace A B => legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb))
    (hU : UpperStationaryReadout pressureUpper
      (fun _ : FinalProbeSpace A B => legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb)) :
    FinalValueIdentification pressureLower pressureUpper :=
  finalValueIdentification_of_readoutBridges pressureLower pressureUpper _
    hL hU
    (stationaryScreening_legalStationaryDatum_of_uniform_elliptic hkin_nonneg hgb Q0 hQ0 hCb hc hkin)

/-- **The value identification for the canonical stationary readout fields of
the actual legal datum**, in the uniformly elliptic regime: here the readout
bridges hold definitionally. -/
theorem finalValueIdentification_stationaryFields_legalDatum_of_uniform_elliptic
    (hkin_nonneg : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (Q0 : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ0 : Q0.secondMomentSubclass)
    (hCb : legalKineticReadout Q0 ≤ Cb)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v) :
    FinalValueIdentification
      (stationaryLowerField
        (fun _ : FinalProbeSpace A B => legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb))
      (stationaryUpperField
        (fun _ : FinalProbeSpace A B => legalStationaryDatum hkin_nonneg hgb Q0 hQ0 hCb)) :=
  finalValueIdentification_legalStationaryDatum_of_uniform_elliptic
    _ _ hkin_nonneg hgb Q0 hQ0 hCb hc hkin
    (lowerStationaryReadout_canonical _) (upperStationaryReadout_canonical _)

end Screening

/-! ## The actual original legal lane datum -/

section OriginalLane

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- **The actual stationary pressure datum of the original legal lane.**

The competitor is a matching in the original second-moment subclass, produced by
originalSecondMomentSubclass_nonempty from the legal lane framework hypotheses;
its kinetic readout bounds the competitor kinetic energies. -/
noncomputable def originalLegalStationaryDatum
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
      0 ≤ D.originalFocalKinetic gap a b v) :
    StationaryPressureDatum
      (LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g) G
      (legalKineticReadout
        (Classical.choose (D.originalSecondMomentSubclass_nonempty
          hF hw hq hgap hbounds pi hpi horder hg hgb))) :=
  legalStationaryDatum hkin_nonneg hgb
    (Classical.choose (D.originalSecondMomentSubclass_nonempty
      hF hw hq hgap hbounds pi hpi horder hg hgb))
    (Classical.choose_spec (D.originalSecondMomentSubclass_nonempty
      hF hw hq hgap hbounds pi hpi horder hg hgb))
    le_rfl

end OriginalLane

end OTSelector.Reconstruction
