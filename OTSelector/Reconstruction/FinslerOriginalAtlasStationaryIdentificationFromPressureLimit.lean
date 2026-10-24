import OTSelector.Reconstruction.FinslerOriginalMeasurablePressureLimitReduction
import OTSelector.Reconstruction.FinslerOriginalFocalValueEqualityReduction
import OTSelector.Reconstruction.FinslerOriginalFrozenCampbellReadoutReduction

/-!
# The population stationary readout identification from the pressure limit

The single remaining typed paper input of the population focal-value chain P1 is
N1, the population stationary readout identification
AtlasStationaryPressureIdentification: the weighted readout of the stationary
datum family equals the Campbell averaged per-root stationary pressure.  N2 (the
per-root frozen readout identification) is discharged from the frozen matching
minimality in FinslerOriginalFrozenCampbellReadoutFromStationary.

This module reduces N1 to the paper's pressure limit theorem.  The paper chain
is I_w = pA = P_2, followed by the atlas integration:

* FocalValueEquality pA Ag fg alpha beta is the first global paper step, the
  identity I_w = pA between the weighted stationary pressure and the legal
  pressure limit;
* MeasurablePressureLimit Seed a kappa lambda pA alpha beta coef probeFam q is
  the pressure limit theorem, the second global paper step pA = P_2;
* PerRootFocalValueEqualityAe is the paper's almost-everywhere rootwise
  focal-value equality, the frozen gluing input (in the uniformly elliptic
  regime it is a repository theorem);
* the datum readout link is the repository theorem stationaryDatumFamily_Iw for
  the canonical stationary datum family; it is carried as a hypothesis so the
  statements apply to any datum family with that readout.

What is proved here:

1. AtlasStationaryPressureIdentification quotient MeasurablePressureLimit given
   the datum readout link, the focal-value equality and the a.e. rootwise gluing
   (atlasStationaryPressureIdentification_iff_measurablePressureLimit_of_datum),
   with both directions as separate corollaries.  Thus N1 is exactly the
   pressure limit theorem once the other paper steps are granted.
2. The sharpest typed form of the limit input: the two-sided eventual sandwich
   of the finite-scale pressures against the measured atlas second-moment
   pressure (atlasStationaryPressureIdentification_iff_eventually_bounds).
3. P1 with minimal binders: from the focal-value equality, the pressure limit
   theorem and the a.e. rootwise gluing, with no datum, no scene data and no
   frozen readout (populationFocalValueLimit_of_measurablePressureLimit), and
   the same from the eventual sandwich
   (populationFocalValueLimit_of_eventually_bounds).
4. The uniformly elliptic specializations in which the rootwise gluing is a
   repository theorem.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M}

/-! ## N1 is the pressure limit theorem -/

/-- **The population stationary readout identification is the pressure limit
theorem, given the other paper steps.**  Given the datum readout link, the
focal-value equality I_w = pA and the almost-everywhere rootwise focal-value
equality, N1 is equivalent to MeasurablePressureLimit, the pressure limit
theorem pA = P_2.  Both sides are readouts of the same two pressures. -/
theorem atlasStationaryPressureIdentification_iff_measurablePressureLimit_of_datum
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q ↔
      MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q := by
  have hBridge : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      campbellAveragedStationaryPressure α β Seed a κ lambda (coef φ) (probeFam φ) q t =
        populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t :=
    fun φ t =>
      campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe
        hRoot φ t
  constructor
  · intro hN1 φ t
    exact (hFocal φ t).symm.trans
      ((hDatum φ t).symm.trans ((hN1 φ t).trans (hBridge φ t)))
  · intro hLimit φ t
    exact (hDatum φ t).trans
      ((hFocal φ t).trans ((hLimit φ t).trans (hBridge φ t).symm))

/-- **N1 from the pressure limit theorem.** -/
theorem atlasStationaryPressureIdentification_of_measurablePressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q :=
  (atlasStationaryPressureIdentification_iff_measurablePressureLimit_of_datum
    Seed a κ lambda pA α β Ag fg coef probeFam q datum hDatum hFocal hRoot).mpr hLimit

/-- **The pressure limit theorem from N1.**  Conversely, N1 together with the
same paper steps gives the pressure limit theorem. -/
theorem measurablePressureLimit_of_atlasStationaryPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hN1 : AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q :=
  (atlasStationaryPressureIdentification_iff_measurablePressureLimit_of_datum
    Seed a κ lambda pA α β Ag fg coef probeFam q datum hDatum hFocal hRoot).mp hN1

/-! ## The sharpest typed form of the limit input: the two-sided sandwich -/

/-- **N1 in the sharpest scalar form of the pressure limit theorem.**  Given the
lane identification of pA as the limit of the finite-scale pressures, N1 is
equivalent to the two-sided eventual sandwich of the finite pressures against
the measured atlas second-moment pressure: eventual lower bounds at every level
below it and eventual upper bounds at every level above it.  This is the exact
typed statement of the paper's sandwich proof. -/
theorem atlasStationaryPressureIdentification_iff_eventually_bounds
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hPA : FinitePressureLimitAt pressure pA) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q ↔
      ((∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          b < populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t →
            ∀ᶠ R in atTop, b < pressure φ R t) ∧
        (∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t < b →
            ∀ᶠ R in atTop, pressure φ R t < b)) :=
  (atlasStationaryPressureIdentification_iff_measurablePressureLimit_of_datum
    Seed a κ lambda pA α β Ag fg coef probeFam q datum hDatum hFocal hRoot).trans
    (measurablePressureLimit_iff_eventually_bounds Seed a κ lambda pA α β pressure
      coef probeFam q hPA)

/-! ## P1 with minimal binders -/

/-- **P1 from the paper's pressure limit theorem.**  From the focal-value
equality I_w = pA, the pressure limit theorem pA = P_2 and the a.e. rootwise
gluing P_2 = P_w, the population focal-value equality P1 holds.  No datum, no
frozen scene data and no frozen readout occurs in the statement: the whole P1
content is the chain I_w = pA = P_2 = P_w. -/
theorem populationFocalValueLimit_of_measurablePressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q := by
  intro φ t
  have hBridge :
      campbellAveragedStationaryPressure α β Seed a κ lambda (coef φ) (probeFam φ) q t =
        populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t :=
    campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe
      hRoot φ t
  exact (hFocal φ t).trans ((hLimit φ t).trans hBridge.symm)

/-- **P1 from the two-sided eventual sandwich.**  The same minimal-binder P1
statement read through the sharpest scalar form of the pressure limit theorem,
given the lane identification of pA as the limit of the finite-scale
pressures. -/
theorem populationFocalValueLimit_of_eventually_bounds
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (hPA : FinitePressureLimitAt pressure pA)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hbounds :
      ((∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          b < populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t →
            ∀ᶠ R in atTop, b < pressure φ R t) ∧
        (∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t < b →
            ∀ᶠ R in atTop, pressure φ R t < b))) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_measurablePressureLimit Seed a κ lambda pA Ag fg
    coef probeFam q α β hFocal
    ((measurablePressureLimit_iff_eventually_bounds Seed a κ lambda pA α β pressure
      coef probeFam q hPA).mpr hbounds)
    hRoot

/-! ## The uniformly elliptic specializations -/

/-- **N1 from the pressure limit theorem in the uniformly elliptic regime**,
where the a.e. rootwise gluing is a repository theorem. -/
theorem atlasStationaryPressureIdentification_of_measurablePressureLimit_of_uniform_elliptic
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q :=
  (atlasStationaryPressureIdentification_iff_measurablePressureLimit_of_datum
    Seed a κ lambda pA α β Ag fg coef probeFam q datum hDatum hFocal
    (perRootFocalValueEqualityAe_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound)).mpr hLimit

/-- **P1 from the pressure limit theorem in the uniformly elliptic regime.** -/
theorem populationFocalValueLimit_of_measurablePressureLimit_of_uniform_elliptic
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_measurablePressureLimit Seed a κ lambda pA Ag fg
    coef probeFam q α β hFocal hLimit
    (perRootFocalValueEqualityAe_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound)

end OTSelector.Reconstruction
