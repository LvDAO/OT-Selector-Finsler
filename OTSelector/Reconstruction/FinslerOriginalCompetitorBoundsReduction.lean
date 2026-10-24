import OTSelector.Reconstruction.FinslerOriginalPaperTheoremConsolidated
import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality
import OTSelector.Reconstruction.FinslerOriginalFocalValueLimit

/-!
# Single-competitor stationary datum families

Under the V11 uniform ellipticity assumptions on the calibrated coefficient
(`hA_meas`, `0 < c`, `c <= Ag φ x y`, `Ag φ x y <= C φ`), the weighted class and the
second-moment class coincide (`weightedClass_eq_secondMomentClass_of_uniform_elliptic`),
so the *second* competitor of `stationaryDatumFamily` / `consolidatedStationaryDatum`
can be taken to be the first one:

* `finiteSecondMoment_of_finiteWeightedKinetic_uniform_elliptic` and
  `finiteWeightedKinetic_of_finiteSecondMoment_uniform_elliptic`: the class-level
  equivalence in predicate form (`FiniteWeightedKinetic Ag Q <-> Q.FiniteSecondMoment`);
* `stationaryDatumFamily_singleCompetitor`: `stationaryDatumFamily` with only
  `(competitor, hcompetitor, hcompetitor_K)`, deriving the second-competitor fields
  at `competitor2 := competitor`;
* `consolidatedStationaryDatum_singleCompetitor`: the same elimination for
  `consolidatedStationaryDatum`.

No `sorry`, `admit` or added axiom.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace Asymptotics
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching

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
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable {A B : Set M}

/-- **Finite weighted kinetic mean implies finite displacement second moment** under
uniform ellipticity of the calibrated coefficient. -/
theorem finiteSecondMoment_of_finiteWeightedKinetic_uniform_elliptic
    {α β : Measure OTSelector.UnitMark} {Acoef : ℝ → ℝ → ℝ} {c C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      Acoef p.1.1 p.2.1))
    (hc : 0 < c) (hA_low : ∀ a b, c ≤ Acoef a b) (hA_bound : ∀ a b, Acoef a b ≤ C)
    (Q : StationaryForwardMatching α β) (hQ : FiniteWeightedKinetic Acoef Q) :
    Q.FiniteSecondMoment := by
  have hcls := weightedClass_eq_secondMomentClass_of_uniform_elliptic
    (α := α) (β := β) (A := Acoef) (c := c) (C := C) hA_meas hc hA_low hA_bound
  show Q ∈ secondMomentClass α β
  rw [← hcls]
  exact hQ

/-- **Finite displacement second moment implies finite weighted kinetic mean** under
uniform ellipticity of the calibrated coefficient. -/
theorem finiteWeightedKinetic_of_finiteSecondMoment_uniform_elliptic
    {α β : Measure OTSelector.UnitMark} {Acoef : ℝ → ℝ → ℝ} {c C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      Acoef p.1.1 p.2.1))
    (hc : 0 < c) (hA_low : ∀ a b, c ≤ Acoef a b) (hA_bound : ∀ a b, Acoef a b ≤ C)
    (Q : StationaryForwardMatching α β) (hQ : Q.FiniteSecondMoment) :
    FiniteWeightedKinetic Acoef Q := by
  have hcls := weightedClass_eq_secondMomentClass_of_uniform_elliptic
    (α := α) (β := β) (A := Acoef) (c := c) (C := C) hA_meas hc hA_low hA_bound
  show Q ∈ weightedClass α β Acoef
  rw [hcls]
  exact hQ

/-- **The stationary datum family with a single competitor.**  The fields
`competitor2`, `hcompetitor2` and `hcompetitor2_K` are derived at
`competitor2 := competitor` from uniform ellipticity. -/
noncomputable def stationaryDatumFamily_singleCompetitor
    {G Cb : ℝ}
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Cbnd : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ Cbnd φ)
    (hf : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (c : ℝ) (hc : 0 < c)
    (hA_low : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), c ≤ (Ag φ) x y) :
    FinalProbeSpace A B → StationaryPressureDatum (StationaryForwardMatching α β) G Cb :=
  stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg Cbnd hA_meas hA_nonneg
    hA_bound hf hfG competitor competitor hcompetitor hcompetitor_K
    (fun φ => finiteSecondMoment_of_finiteWeightedKinetic_uniform_elliptic
      (hA_meas φ) hc (hA_low φ) (hA_bound φ) (competitor φ) (hcompetitor φ))
    hcompetitor_K

/-- **The consolidated stationary datum family with a single competitor.** -/
noncomputable def consolidatedStationaryDatum_singleCompetitor
    {G Cb : ℝ}
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Cbnd : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ Cbnd φ)
    (hf : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (c : ℝ) (hc : 0 < c)
    (hA_low : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), c ≤ (Ag φ) x y) :
    FinalProbeSpace A B → StationaryPressureDatum (StationaryForwardMatching α β) G Cb :=
  consolidatedStationaryDatum (G := G) (Cb := Cb) α β Ag fg Cbnd hA_meas hA_nonneg
    hA_bound hf hfG competitor competitor hcompetitor hcompetitor_K
    (fun φ => finiteSecondMoment_of_finiteWeightedKinetic_uniform_elliptic
      (hA_meas φ) hc (hA_low φ) (hA_bound φ) (competitor φ) (hcompetitor φ))
    hcompetitor_K

end OTSelector.Reconstruction
