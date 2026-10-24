import OTSelector.Reconstruction.FinslerOriginalCompetitorBoundsReduction
import OTSelector.Reconstruction.FinslerOriginalReadoutGlue

/-!
# The global stationary datum from elliptic ray data

The V12 endgame assumes the calibrated coefficient is uniformly elliptic on the ray data:
`hA_meas`, `0 < c`, `c <= Ag φ x y`, `Ag φ x y <= C φ`.  Under these assumptions:

* `nonneg_of_pos_lower_bound`: `hA_nonneg` (nonnegativity of `Ag`) is REDUNDANT — it
  follows from `0 < c` and `c <= Ag φ x y`;
* `stationaryScreening_of_singleCompetitor`: `StationaryScreening` holds for
  `stationaryDatumFamily_singleCompetitor` (take `Q' = Q`; the class equality of
  `weightedClass_eq_secondMomentClass_of_uniform_elliptic` gives `Q ∈ C_2`);
* `GlobalEllipticStationaryInputs`: ONE structure packaging
  `(c, hc, C, hA_meas, hA_low, hA_bound, hf_meas, hfG, competitor, hcompetitor,
  hcompetitor_K)`, with `hA_nonneg`, `competitor2`, `hcompetitor2`,
  `hcompetitor2_K` all ELIMINATED, and derived `.hA_nonneg`, `.datum`,
  `.consolidatedDatum`, `.screening`.

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

/-- **Nonnegativity from uniform positivity below.**  `hA_nonneg` is redundant under
`0 < c` and `c <= Ag φ x y`. -/
theorem nonneg_of_pos_lower_bound
    {Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hA_low : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), c ≤ Ag φ x y) :
    ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ Ag φ x y :=
  fun φ x y => le_trans hc.le (hA_low φ x y)

/-- **Stationary screening for the single-competitor datum family.**  The screening
witness is the point `Q` itself: uniform ellipticity puts it in `C_2`, and the value
inequality is strict by `ε > 0`. -/
theorem stationaryScreening_of_singleCompetitor
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
    StationaryScreening
      (stationaryDatumFamily_singleCompetitor (G := G) (Cb := Cb) α β Ag fg Cbnd
        hA_meas hA_nonneg hA_bound hf hfG competitor hcompetitor hcompetitor_K
        c hc hA_low) := by
  intro f v Q hQ ε hε
  refine ⟨Q, ?_, ?_⟩
  · show Q ∈ secondMomentClass α β
    rw [← weightedClass_eq_secondMomentClass_of_uniform_elliptic
      (α := α) (β := β) (A := Ag f) (c := c) (C := Cbnd f)
      (hA_meas f) hc (hA_low f) (hA_bound f)]
    exact hQ
  · linarith

/-- **The global elliptic stationary inputs.**  All global assumptions of the V12
stationary datum and screening construction in one structure: `hA_nonneg`,
`competitor2`, `hcompetitor2` and `hcompetitor2_K` are eliminated (derived from
uniform ellipticity / `competitor`). -/
structure GlobalEllipticStationaryInputs
    {G Cb : ℝ}
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Cbnd : FinalProbeSpace A B → ℝ) where
  c : ℝ
  hc : 0 < c
  hA_meas : ∀ φ : FinalProbeSpace A B,
    Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1)
  hA_low : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), c ≤ (Ag φ) x y
  hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ Cbnd φ
  hf_meas : ∀ φ : FinalProbeSpace A B,
    Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2)
  hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G
  competitor : FinalProbeSpace A B → StationaryForwardMatching α β
  hcompetitor : ∀ φ : FinalProbeSpace A B, FiniteWeightedKinetic (Ag φ) (competitor φ)
  hcompetitor_K : ∀ φ : FinalProbeSpace A B, palmKinetic (Ag φ) (competitor φ) ≤ Cb

namespace GlobalEllipticStationaryInputs

variable {G Cb : ℝ}
  {α β : Measure OTSelector.UnitMark}
  {Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ}
  {fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ}
  {Cbnd : FinalProbeSpace A B → ℝ}

/-- The derived nonnegativity of the calibrated coefficient. -/
theorem hA_nonneg (I : GlobalEllipticStationaryInputs (G := G) (Cb := Cb) α β Ag fg Cbnd) :
    ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y :=
  nonneg_of_pos_lower_bound I.hc I.hA_low

/-- The global stationary datum family, with the single-competitor reduction. -/
noncomputable def datum (I : GlobalEllipticStationaryInputs (G := G) (Cb := Cb)
    α β Ag fg Cbnd) :
    FinalProbeSpace A B → StationaryPressureDatum (StationaryForwardMatching α β) G Cb :=
  stationaryDatumFamily_singleCompetitor (G := G) (Cb := Cb) α β Ag fg Cbnd
    I.hA_meas I.hA_nonneg I.hA_bound I.hf_meas I.hfG I.competitor I.hcompetitor
    I.hcompetitor_K I.c I.hc I.hA_low

/-- The global consolidated stationary datum family, with the single-competitor
reduction. -/
noncomputable def consolidatedDatum (I : GlobalEllipticStationaryInputs (G := G)
    (Cb := Cb) α β Ag fg Cbnd) :
    FinalProbeSpace A B → StationaryPressureDatum (StationaryForwardMatching α β) G Cb :=
  consolidatedStationaryDatum_singleCompetitor (G := G) (Cb := Cb) α β Ag fg Cbnd
    I.hA_meas I.hA_nonneg I.hA_bound I.hf_meas I.hfG I.competitor I.hcompetitor
    I.hcompetitor_K I.c I.hc I.hA_low

/-- The stationary screening for the global datum. -/
theorem screening (I : GlobalEllipticStationaryInputs (G := G) (Cb := Cb)
    α β Ag fg Cbnd) :
    StationaryScreening I.datum :=
  stationaryScreening_of_singleCompetitor (G := G) (Cb := Cb) α β Ag fg Cbnd
    I.hA_meas I.hA_nonneg I.hA_bound I.hf_meas I.hfG I.competitor I.hcompetitor
    I.hcompetitor_K I.c I.hc I.hA_low

end GlobalEllipticStationaryInputs

end OTSelector.Reconstruction
