import OTSelector.Reconstruction.FinslerOriginalFrozenStationaryPressureIdentification
import OTSelector.PointProcess.StationaryForwardMatching

/-!
# The population focal-value and pressure-limit identification

This module continues F15.  The frozen Campbell readout of the lower lane has
been reduced in the preceding modules to exactly two typed statements:

* AtlasStationaryPressureIdentification (N1): the population stationary readout
  of the assembly equals the Campbell-averaged stationary pressure of the
  population atlas;
* FrozenAttainment: the frozen stationary matching of the lane attains the
  weighted stationary pressure at the scaled tilt.

This module treats N1.  It unfolds both sides and shows that N1 is exactly one
typed paper-level identity, the population focal-value and pressure-limit
statement, and it constructs the actual stationary pressure datum family so
that the datum readout link of N1 is proved from the repository definitional
theorem stationaryForwardDatum_Iw instead of being assumed.

## What is proved

* weightedStationaryPressure_eq_sInf: the left-hand side of the population
  identity, namely the weighted stationary pressure, written as the stationary
  infimum of the kinetic plus tilt times probe functional over the weighted
  stationary class;
* campbellAveragedStationaryPressure_eq_tsum_integral: the right-hand side,
  namely the Campbell-averaged stationary pressure, written as the sum over
  population seed pieces of the theta-weighted per-root weighted stationary
  pressures at the scaled tilt;
* CampbellAveragedStationaryPressureIdentification: the population identity P1
  itself, stated as a proposition in the assembly variables;
* PopulationFocalValueLimit: the single typed paper-level input, the unfolded
  per-piece population focal-value and pressure-limit identity;
* campbellAveragedStationaryPressureIdentification_of_focalValueLimit: P1 from
  that single input, with the right-hand side unfolded by the repository
  definition theorem campbellAveragedStationaryPressure_def;
* focalValueLimit_iff_campbellAveragedStationaryPressureIdentification: the
  population identity P1 is equivalent to the typed input, so the input is not
  stronger than the paper statement;
* stationaryDatumFamily: the actual stationary pressure datum family built from
  the stationary forward datum of the weighted stationary matching class;
* stationaryDatumFamily_Iw: its weighted readout is the weighted stationary
  pressure, proved by the repository definitional theorem
  stationaryForwardDatum_Iw;
* atlasStationaryPressureIdentification_stationaryDatumFamily_of_focalValueLimit:
  N1 for the actual datum family from the single typed input, with the datum
  readout link proved;
* frozenCampbellReadout_of_populationFocalValueLimit_and_attainment: the frozen
  Campbell readout of F15 from exactly two typed paper-level inputs, the
  population focal-value limit and the frozen attainment.

Provenance of the typed input: main.tex theorem general-focal-value-equality
(approximately lines 11029 to 11052), equation
general-gluing-integrated-pressures (approximately lines 11382 to 11399),
equation general-finsler-pressure-limit (approximately lines 11565 to 11582),
and proposition highd-measurable-pressure with equation
highd-measurable-pressure (approximately lines 5442 to 5460), where the
per-root frozen unit-intensity pressure integrated against the theta density is
exactly the right-hand side of campbellAveragedStationaryPressure_def.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold Module OTSelector.Probability
open OTSelector.Geometry OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M} {W : Type*} {G Cb : ℝ}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}

/-! ## Unfolding the two sides of the population identity -/

/-- The left-hand side of the population identity: the weighted stationary
pressure is the stationary infimum of the kinetic plus tilt times probe
functional over the weighted stationary matching class. -/
theorem weightedStationaryPressure_eq_sInf
    (α β : Measure OTSelector.UnitMark) (Ag : ℝ → ℝ → ℝ)
    (fg : MarkedCloudPoint → MarkedCloudPoint → ℝ) (v : ℝ) :
    weightedStationaryPressure α β Ag fg v =
      sInf ((fun M : StationaryForwardMatching α β => palmKinetic Ag M + v * palmProbe fg M) ''
        weightedClass α β Ag) := rfl

/-- The right-hand side of the population identity: the Campbell-averaged
stationary pressure is the sum over population seed pieces of the
theta-weighted per-root weighted stationary pressures at the scaled tilt. -/
theorem campbellAveragedStationaryPressure_eq_tsum_integral
    (α β : Measure OTSelector.UnitMark)
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) (q t : ℝ) :
    campbellAveragedStationaryPressure α β Seed a κ lambda A f q t =
      ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          weightedStationaryPressure α β (A j z) (f j z)
            (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ∂lambda :=
  campbellAveragedStationaryPressure_def α β Seed a κ lambda A f q t

/-! ## The population identity and the single typed paper-level input -/

/-- The population identity P1: at every probe and tilt the weighted stationary
pressure of the global stationary scene equals the Campbell-averaged stationary
pressure of the population atlas. -/
def CampbellAveragedStationaryPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    weightedStationaryPressure α β (Ag φ) (fg φ) t =
      campbellAveragedStationaryPressure α β Seed a κ lambda (coef φ) (probeFam φ) q t

/-- The single typed paper-level input: the population focal-value and
pressure-limit identity in unfolded per-piece form.  The right-hand side is the
paper's measured pressure formula: the sum over pieces of theta to the minus two
over q times the per-root frozen unit-intensity pressure at the scaled tilt. -/
def PopulationFocalValueLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    weightedStationaryPressure α β (Ag φ) (fg φ) t =
      ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          weightedStationaryPressure α β (coef φ j z) (probeFam φ j z)
            (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ∂lambda

/-- P1 from the single typed paper-level input, by the repository definition
theorem for the Campbell-averaged stationary pressure. -/
theorem campbellAveragedStationaryPressureIdentification_of_focalValueLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (h : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q) :
    CampbellAveragedStationaryPressureIdentification Seed a κ lambda Ag fg α β coef probeFam q := by
  intro φ t
  rw [h φ t]
  exact (campbellAveragedStationaryPressure_def α β Seed a κ lambda
    (coef φ) (probeFam φ) q t).symm

/-- The population identity P1 is equivalent to the typed unfolded input: the
single input is not stronger than the paper statement, it is the same identity
after the repository unfolding of the Campbell-averaged stationary pressure. -/
theorem focalValueLimit_iff_campbellAveragedStationaryPressureIdentification
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      CampbellAveragedStationaryPressureIdentification Seed a κ lambda Ag fg α β coef probeFam q := by
  constructor
  · intro h
    exact campbellAveragedStationaryPressureIdentification_of_focalValueLimit Seed a κ lambda
      Ag fg α β coef probeFam q h
  · intro h φ t
    have hpt := h φ t
    rw [hpt]
    exact (campbellAveragedStationaryPressure_def α β Seed a κ lambda
      (coef φ) (probeFam φ) q t).symm

/-! ## The actual stationary pressure datum family -/

/-- The actual stationary pressure datum family over the weighted stationary
matching class, one stationary forward datum for every physical probe. -/
noncomputable def stationaryDatumFamily
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (C : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ C φ)
    (hf : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor2 φ) ≤ Cb) :
    FinalProbeSpace A B → StationaryPressureDatum (StationaryForwardMatching α β) G Cb :=
  fun φ =>
    stationaryForwardDatum (Ag φ) (fg φ) (G := G) (Cb := Cb) (C := C φ)
      (hA_meas φ) (hA_nonneg φ) (hA_bound φ) (hf φ) (hfG φ)
      (competitor φ) (hcompetitor φ) (hcompetitor_K φ)
      (competitor2 φ) (hcompetitor2 φ) (hcompetitor2_K φ)

/-- The weighted readout of the actual datum family is the weighted stationary
pressure, by the repository definitional theorem stationaryForwardDatum_Iw. -/
theorem stationaryDatumFamily_Iw
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (C : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ C φ)
    (hf : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor2 φ) ≤ Cb)
    (φ : FinalProbeSpace A B) (t : ℝ) :
    (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg C hA_meas hA_nonneg
        hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K φ).Iw t =
      weightedStationaryPressure α β (Ag φ) (fg φ) t :=
  stationaryForwardDatum_Iw (Ag φ) (fg φ) (G := G) (Cb := Cb) (C := C φ)
    (hA_meas φ) (hA_nonneg φ) (hA_bound φ) (hf φ) (hfG φ)
    (competitor φ) (hcompetitor φ) (hcompetitor_K φ)
    (competitor2 φ) (hcompetitor2 φ) (hcompetitor2_K φ) t

/-- N1 for the actual datum family from the single typed paper-level input: the
datum readout link is proved by stationaryDatumFamily_Iw and the population
identity is the unfolded input. -/
theorem atlasStationaryPressureIdentification_stationaryDatumFamily_of_focalValueLimit
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (C : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ C φ)
    (hf : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor2 φ) ≤ Cb)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (h : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := StationaryForwardMatching α β) (G := G) (Cb := Cb)
      α β (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg C hA_meas
        hA_nonneg hA_bound hf hfG competitor competitor2 hcompetitor
        hcompetitor_K hcompetitor2 hcompetitor2_K) coef probeFam q := by
  intro φ t
  calc (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg C hA_meas hA_nonneg
          hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
          hcompetitor2 hcompetitor2_K φ).Iw t
      = weightedStationaryPressure α β (Ag φ) (fg φ) t :=
        stationaryDatumFamily_Iw (G := G) (Cb := Cb) α β Ag fg C hA_meas hA_nonneg
          hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
          hcompetitor2 hcompetitor2_K φ t
    _ = campbellAveragedStationaryPressure α β Seed a κ lambda (coef φ) (probeFam φ) q t :=
        campbellAveragedStationaryPressureIdentification_of_focalValueLimit Seed a κ lambda
      Ag fg α β coef probeFam q h φ t

/-- F15 from exactly two typed paper-level inputs: the population focal-value
and pressure-limit identity, and the frozen attainment inequality.  The datum
readout link is proved, the frozen-cost identification is the previous module
equivalence and the Campbell integration transfer is proved. -/
theorem frozenCampbellReadout_of_populationFocalValueLimit_and_attainment
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedFrozenPopMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (C : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ C φ)
    (hf : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor2 φ) ≤ Cb)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ)
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hAcoef : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        probeFam φ j z p.1 p.2))
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ)
      (z : Z) (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (h : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hAtt : FrozenAttainment (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q) :
    FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      (frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) α β coef probeFam Mst q) q
      (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg C hA_meas hA_nonneg
        hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K) := by
  have hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg C hA_meas hA_nonneg
        hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K φ).Iw t =
        weightedStationaryPressure α β (Ag φ) (fg φ) t :=
    fun φ t =>
      stationaryDatumFamily_Iw (G := G) (Cb := Cb) α β Ag fg C hA_meas hA_nonneg
        hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K φ t
  have hFocal : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      weightedStationaryPressure α β (Ag φ) (fg φ) t =
        campbellAveragedStationaryPressure α β Seed a κ lambda (coef φ) (probeFam φ) q t :=
    fun φ t =>
      campbellAveragedStationaryPressureIdentification_of_focalValueLimit Seed a κ lambda
      Ag fg α β coef probeFam q h φ t
  exact frozenCampbellReadout_of_focalValueLimit_and_attainment
    (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
    (W := StationaryForwardMatching α β) (G := G) (Cb := Cb)
    (hF := hF) (hcomplete := hcomplete) (hu := hu) (ha := ha) (hinj := hinj)
    (datum := stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg C hA_meas
      hA_nonneg hA_bound hf hfG competitor competitor2 hcompetitor
      hcompetitor_K hcompetitor2 hcompetitor2_K)
    (Ag := Ag) (fg := fg) (α := α) (β := β) (coef := coef)
    (probeFam := probeFam) (Mst := Mst) (q := q)
    (hM := hM) (hA := hAcoef) (hf := hprobe) (hG := hprobe_bound)
    (hDatum := hDatum) (hFocal := hFocal) (hAtt := hAtt)
