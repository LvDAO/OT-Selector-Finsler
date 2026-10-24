import OTSelector.Reconstruction.FinslerOriginalQuadraticCoercionFromFrozenMinimality
import OTSelector.Reconstruction.FinslerOriginalFocalValueLimit

/-!
# Stationary minimizer stability at the concrete stationary datum family

`FinslerOriginalQuadraticCoercionFromFrozenMinimality` reduced the readout tilt
derivative to `SquaredProbeKineticCoercion` and to minimizer stability around a tilt-0
minimizer.  This file instantiates that reduction at the concrete family
`stationaryDatumFamily` (whose `Cw` is `weightedClass α β (Ag f)`, whose `K` is
`palmKinetic (Ag f)`, whose `P` is `palmProbe (fg f)`, and whose `Iw` is
`weightedStationaryPressure α β (Ag f) (fg f)`):

* `StationaryMinimizerStability`: for every probe `f` there is a tilt-0 minimizer
  `Q0 f` in the weighted class (`palmKinetic (Ag f) (Q0 f) =
  weightedStationaryPressure α β (Ag f) (fg f) 0`, `palmProbe (fg f) (Q0 f) = p f`),
  and for every `Q` in the class the probe discrepancy is `L * sqrt (d Q (Q0 f))`
  controlled while the kinetic energy is `m_conv`-strongly convex in `d`;
* `squaredProbeKineticCoercion_stationaryDatumFamily`: hence
  `SquaredProbeKineticCoercion (stationaryDatumFamily ... f) (p f) (L * sqrt (2 / m_conv))`;
* `finslerReadoutTiltDerivative_frozenLowerField_of_stationaryMinimizerStability`:
  hence the V4 endgame readout tilt derivative of the frozen lower field!

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

/-- **Stationary minimizer stability** at the concrete stationary datum family: a
tilt-0 minimizer `Q0 f` in the weighted class, probe `L`-controlled by
`sqrt (d · ·)`, and `m_conv`-strong convexity of the palm kinetic energy in `d`. -/
def StationaryMinimizerStability
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (p : FinalProbeSpace A B → ℝ) (m_conv L : ℝ)
    (d : StationaryForwardMatching α β → StationaryForwardMatching α β → ℝ)
    (Q0 : FinalProbeSpace A B → StationaryForwardMatching α β) : Prop :=
  ∀ f : FinalProbeSpace A B,
    Q0 f ∈ weightedClass α β (Ag f) ∧
    palmKinetic (Ag f) (Q0 f) = weightedStationaryPressure α β (Ag f) (fg f) 0 ∧
    palmProbe (fg f) (Q0 f) = p f ∧
    (∀ Q ∈ weightedClass α β (Ag f),
      0 ≤ d Q (Q0 f) ∧
      |palmProbe (fg f) Q - palmProbe (fg f) (Q0 f)| ≤ L * Real.sqrt (d Q (Q0 f)) ∧
      d Q (Q0 f) ≤ (2 / m_conv) * (palmKinetic (Ag f) Q - palmKinetic (Ag f) (Q0 f)))

/-- **Stability at the concrete family implies the squared probe-kinetic coercion.** -/
theorem squaredProbeKineticCoercion_stationaryDatumFamily
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
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B, FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B, palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B, palmKinetic (Ag φ) (competitor2 φ) ≤ Cb)
    (p : FinalProbeSpace A B → ℝ) (m_conv L : ℝ) (hL : 0 ≤ L) (hm : 0 < m_conv)
    (d : StationaryForwardMatching α β → StationaryForwardMatching α β → ℝ)
    (Q0 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hstab : StationaryMinimizerStability α β Ag fg p m_conv L d Q0) :
    ∀ f : FinalProbeSpace A B,
      SquaredProbeKineticCoercion
        (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg Cbnd hA_meas hA_nonneg
          hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
          hcompetitor2 hcompetitor2_K f) (p f) (L * Real.sqrt (2 / m_conv)) := by
  intro f
  obtain ⟨hQ0, hK0, hP0, hrest⟩ := hstab f
  refine (squaredProbeKineticCoercion_of_minimizer_stability
    (D := stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg Cbnd hA_meas hA_nonneg
      hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
      hcompetitor2 hcompetitor2_K f)
    (p := p f) (L := L) (m_conv := m_conv) (c0 := Q0 f) (d := d)
    hQ0 hK0 hP0 hL hm
    (fun Q hQ => (hrest Q hQ).1) (fun Q hQ => (hrest Q hQ).2.1)
    (fun Q hQ => (hrest Q hQ).2.2)).1

/-- **Readout tilt derivative of the frozen lower field from stationary minimizer
stability.** -/
theorem finslerReadoutTiltDerivative_frozenLowerField_of_stationaryMinimizerStability
    {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
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
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B, FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B, palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B, palmKinetic (Ag φ) (competitor2 φ) ≤ Cb)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      g q (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg Cbnd hA_meas hA_nonneg
        hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K))
    (p : FinalProbeSpace A B → ℝ) (m_conv L : ℝ) (hL : 0 ≤ L) (hm : 0 < m_conv)
    (d : StationaryForwardMatching α β → StationaryForwardMatching α β → ℝ)
    (Q0 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hstab : StationaryMinimizerStability α β Ag fg p m_conv L d Q0) :
    FinslerReadoutTiltDerivative
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) :=
  finslerReadoutTiltDerivative_frozenLowerField_of_squaredCoercion Seed a κ lambda g q
    (stationaryDatumFamily (G := G) (Cb := Cb) α β Ag fg Cbnd hA_meas hA_nonneg
      hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
      hcompetitor2 hcompetitor2_K) hC p (L * Real.sqrt (2 / m_conv))
    (mul_nonneg hL (Real.sqrt_nonneg _))
    (squaredProbeKineticCoercion_stationaryDatumFamily α β Ag fg Cbnd hA_meas hA_nonneg
      hA_bound hf hfG competitor competitor2 hcompetitor hcompetitor_K
      hcompetitor2 hcompetitor2_K p m_conv L hL hm d Q0 hstab)

end OTSelector.Reconstruction
