import OTSelector.Reconstruction.FinslerOriginalFrozenCampbellReadoutReduction
import OTSelector.Reconstruction.FinslerOriginalRootedSceneLimitLaw
import OTSelector.Reconstruction.FinslerOriginalRootedCampbellFrozenCore

/-!
# Frozen stationary pressure identification from the rooted Campbell structure

The readout glue reduces the frozen Campbell readout of the lower lane to two
typed statements:

* AtlasStationaryPressureIdentification (N1): the population stationary readout
  of the assembly equals the Campbell-averaged stationary pressure of the
  population atlas;
* FrozenStationaryPressureIdentification (N2): at almost every root of every
  population seed piece, the weighted stationary pressure at the scaled tilt
  equals the frozen cost of the lower lane.

This module shrinks N2 using the rooted Campbell structure already present in
the repository and composes the remaining paper-level inputs into the frozen
Campbell readout.

## What is proved

* frozenRootedCostReadout: the frozen root cost of the lower lane, taken to be
  the piecewise frozen root integrand rootedFrozenPieceIntegrand built from the
  per-piece coefficient, probe and stationary matching families;
* frozenRootedCostReadout_of_mem: on its own population seed piece the frozen
  cost of the lane is the Palm frozen integrand rootedFrozenIntegrand of that
  piece, by uniqueness of the owning piece;
* frozenRootedCostReadout_ae_identification: the Campbell formula on the
  limiting rooted scene at the lane cost, i.e. the frozen cost equals the Palm
  frozen integrand almost everywhere on each piece;
* weightedStationaryPressure_le_frozenRootedCostReadout: the Campbell lower
  comparison at the lane cost, proved from the repository theorem
  rootedFrozen_hdom;
* FrozenAttainment: the frozen attainment inequality, namely the reverse
  inequality saying that the stationary matching of the frozen lane realizes
  the weighted stationary pressure at the scaled tilt;
* frozenStationaryPressureIdentification_iff_frozenAttainment: N2 for the lane
  cost is equivalent to FrozenAttainment, since the lower comparison is
  already proved;
* atlasStationaryPressureIdentification_of_focalValueLimit: N1 from the paper
  population readout, with the first link of the chain, the stationary datum
  readout, kept as the typed hypothesis hDatum; that hypothesis is the
  definitional repository theorem stationaryForwardDatum_Iw for a stationary
  forward datum;
* frozenCampbellReadout_of_focalValueLimit_and_attainment: the frozen Campbell
  readout from exactly two typed paper-level inputs, the focal-value pressure
  limit hFocal and the frozen attainment hAtt, with every other step proved.

Provenance of the two paper-level inputs: main.tex theorem
general-focal-value-equality (approximately lines 11029 to 11052), proposition
general-gluing-conditional-readout and equation
general-gluing-integrated-pressures (approximately lines 11382 to 11399),
equation general-finsler-pressure-limit (approximately lines 11565 to 11582),
and the measurable pressure formula of proposition highd-measurable-pressure
(approximately lines 5442 to 5460).

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

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M} {W : Type*} {G Cb : ℝ}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}

/-- The frozen root cost of the lower lane, read off the rooted Campbell
structure: the piecewise frozen root integrand of the per-piece coefficient,
probe and stationary matching families. -/
noncomputable def frozenRootedCostReadout
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) : FinalProbeSpace A B → ℝ → Z → ℝ :=
  fun φ t ↦
    rootedFrozenPieceIntegrand (K := A ∪ B) α β Seed a κ lambda
      (fun φ' _ j z ↦ coef φ' j z)
      (fun φ' _ j z ↦ probeFam φ' j z) Mst q t φ

/-- On its own population seed piece, the frozen cost of the lane is the Palm
frozen integrand of that piece. -/
theorem frozenRootedCostReadout_of_mem
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) {φ : FinalProbeSpace A B} {t : ℝ} {j : ℕ} {z : Z}
    (hz : z ∈ populationSeedRootPiece Seed a κ lambda j) :
    frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        α β coef probeFam Mst q φ t z =
      rootedFrozenIntegrand (K := A ∪ B) α β Seed a κ lambda
        (fun φ' _ j z ↦ coef φ' j z)
        (fun φ' _ j z ↦ probeFam φ' j z) Mst q t φ j z := by
  exact rootedFrozenPieceIntegrand_of_mem (K := A ∪ B) α β Seed a κ lambda
    (fun φ' _ j z ↦ coef φ' j z)
    (fun φ' _ j z ↦ probeFam φ' j z) Mst q t φ hz

/-- The Campbell formula on the limiting rooted scene, at the frozen cost of
the lane: at almost every root of every population seed piece, the frozen cost
of the lane equals the Palm frozen integrand of that piece. -/
theorem frozenRootedCostReadout_ae_identification
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedFrozenMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) :
    ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
        frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
            α β coef probeFam Mst q φ t z =
          rootedFrozenIntegrand (K := A ∪ B) α β Seed a κ lambda
            (fun φ' _ j z ↦ coef φ' j z)
            (fun φ' _ j z ↦ probeFam φ' j z) Mst q t φ j z := by
  intro φ t j
  exact rootedFrozenPieceIntegrand_ae_identification hF hcomplete hu ha hinj
    α β Seed κ lambda
    (fun φ' _ j z ↦ coef φ' j z)
    (fun φ' _ j z ↦ probeFam φ' j z) Mst q φ t j

/-- The frozen attainment inequality: the stationary matching of the frozen
lane realizes the weighted stationary pressure at the scaled tilt.  This is
the reverse inequality of the frozen value identification; the opposite
inequality (the Campbell lower comparison) is proved below from the repository
theorem rootedFrozen_hdom. -/
def FrozenAttainment
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
    ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
      frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
          α β coef probeFam Mst q φ t z ≤
        weightedStationaryPressure α β (coef φ j z) (probeFam φ j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))

/-- The Campbell lower comparison at the frozen cost of the lane, proved from
the repository theorem rootedFrozen_hdom: along the stationary matching family
of the lane, the weighted stationary pressure at the scaled tilt is dominated
by the frozen cost of the lane at almost every root of every piece. -/
theorem weightedStationaryPressure_le_frozenRootedCostReadout
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedFrozenMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ}
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hA : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hf : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        probeFam φ j z p.1 p.2))
    (hG : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc) :
    ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
        weightedStationaryPressure α β (coef φ j z) (probeFam φ j z)
            (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ≤
          frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
            α β coef probeFam Mst q φ t z := by
  intro φ t j
  exact rootedFrozen_hdom (K := A ∪ B) α β Seed a κ lambda
    (fun φ' _ j z ↦ coef φ' j z)
    (fun φ' _ j z ↦ probeFam φ' j z) Mst
    (frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      α β coef probeFam Mst q)
    (q := q) hM hA hf hG
    (fun φ' t' j' ↦ frozenRootedCostReadout_ae_identification hF hcomplete hu ha hinj
      α β coef probeFam Mst q φ' t' j') φ t j

/-- N2 for the frozen cost of the lane is equivalent to the frozen attainment
inequality: the lower comparison is the proved theorem
weightedStationaryPressure_le_frozenRootedCostReadout, so exactly the reverse
inequality remains. -/
theorem frozenStationaryPressureIdentification_iff_frozenAttainment
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedFrozenMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ}
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hA : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hf : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        probeFam φ j z p.1 p.2))
    (hG : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc) :
    FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda)
        (g := frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ)
          (lambda := lambda) α β coef probeFam Mst q)
        α β coef probeFam q ↔
      FrozenAttainment (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        α β coef probeFam Mst q := by
  constructor
  · intro hN φ t j
    filter_upwards [hN φ t j] with z hz
    exact le_of_eq hz.symm
  · intro hAtt φ t j
    filter_upwards [hAtt φ t j,
      weightedStationaryPressure_le_frozenRootedCostReadout hF hcomplete hu ha hinj
        α β coef probeFam Mst hM hA hf hG φ t j] with z hge hle
    exact le_antisymm hle hge

/-- N1 from the paper population readout.  The first link of the chain, the
readout of the abstract stationary datum, is the typed hypothesis hDatum; for a
stationary forward datum it is the repository theorem stationaryForwardDatum_Iw,
which is definitional.  The second link hFocal is the paper's focal-value and
pressure-limit identity at population level. -/
theorem atlasStationaryPressureIdentification_of_focalValueLimit
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      weightedStationaryPressure α β (Ag φ) (fg φ) t =
        campbellAveragedStationaryPressure α β Seed a κ lambda
          (coef φ) (probeFam φ) q t) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β datum coef probeFam q := by
  intro φ t
  rw [hDatum φ t, hFocal φ t]

/-- The frozen Campbell readout from exactly two typed paper-level inputs: the
population focal-value pressure limit hFocal and the frozen attainment hAtt.
The Campbell lower comparison, the Campbell formula on the limiting rooted
scene, the piecewise identification of the frozen cost, the integration
transfer to the Campbell-averaged frozen cost and the value chain through the
stationary datum readout are all proved. -/
theorem frozenCampbellReadout_of_focalValueLimit_and_attainment
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedFrozenMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ)
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hA : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hf : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        probeFam φ j z p.1 p.2))
    (hG : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      weightedStationaryPressure α β (Ag φ) (fg φ) t =
        campbellAveragedStationaryPressure α β Seed a κ lambda
          (coef φ) (probeFam φ) q t)
    (hAtt : FrozenAttainment (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      α β coef probeFam Mst q) :
    FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      (frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        α β coef probeFam Mst q) q datum := by
  have hAtlas := atlasStationaryPressureIdentification_of_focalValueLimit
    (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
    datum Ag fg α β coef probeFam q hDatum hFocal
  have hFrozen := (frozenStationaryPressureIdentification_iff_frozenAttainment
    hF hcomplete hu ha hinj α β coef probeFam Mst hM hA hf hG).mpr hAtt
  exact frozenCampbellReadout_of_identifications (Seed := Seed) (a := a)
    (κ := κ) (lambda := lambda)
    (g := frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q) q datum α β coef probeFam
    hAtlas hFrozen
