import OTSelector.Reconstruction.FinslerOriginalReadoutTiltDerivativeActual
import OTSelector.Reconstruction.FinslerOriginalPopulationGluingIdentity

/-!
# F12: hderiv for the actual lane — the kinetic squeeze at the frozen pressure field

The squeeze hypothesis of `FinslerOriginalReadoutTiltDerivativeActual`
(`finslerReadoutTiltDerivative_stationaryReadout_of_kinetic_squeeze`) is instantiated
at the actual lane's frozen pressure field `frozenPressureLower Seed a κ lambda g q`:

* `ActualLaneReadoutSqueeze datum laneField p`: every almost kinetic-minimal admissible
  matching (`K c <= laneField f 0 + δ`) has mark probe within δ of the readout `p f`;
* `finslerReadoutTiltDerivative_actualLane`: if the lane datum family's weighted
  pressure equals the lane's frozen pressure field, then the squeeze yields
  `FinslerReadoutTiltDerivative (frozenPressureLower Seed a κ lambda g q)`;
* `finslerReadoutTiltDerivative_actualLane_atlas`: the same for the atlas-glued
  population gluing pressure family (main.tex weighted-capped-integrated-c1 setup).

The residual input is exactly the paper's zero-tilt near-minimizer readout
identification (main.tex 9046-9050: "Every weighted minimizer has paired expectation
Iw'(t). The same holds in the limit for any weighted near-minimizing sequence") — the
squeeze `hsqueeze`; the value side is supplied by the F15 frozen stationary pressure
identification.  No `sorry`, `admit` or added axiom.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace Asymptotics
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

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

/-- **The actual-lane readout squeeze.**  Every almost kinetic-minimal admissible
matching of the lane datum has mark probe close to the readout, uniformly in the
tilt tolerance δ. -/
def ActualLaneReadoutSqueeze {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (laneField : FinalPressureField A B) (p : FinalProbeSpace A B → ℝ) : Prop :=
  ∀ (f : FinalProbeSpace A B) (δ : ℝ), 0 < δ → ∀ c ∈ (datum f).Cw,
    (datum f).K c ≤ laneField f 0 + δ → |(datum f).P c - p f| ≤ δ

/-- **hderiv for the actual lane (abstract frozen readout family).**  The lane's
frozen pressure field `frozenPressureLower Seed a κ lambda g q` carries the readout
tilt derivative, from the lane datum identification and the kinetic squeeze. -/
theorem finslerReadoutTiltDerivative_actualLane
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ)
    (hIw : ∀ f : FinalProbeSpace A B,
      (datum f).Iw = frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f)
    (hsqueeze : ActualLaneReadoutSqueeze datum
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) p) :
    FinslerReadoutTiltDerivative (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) := by
  have hsqueeze' : ∀ (f : FinalProbeSpace A B) (δ : ℝ), 0 < δ → ∀ c ∈ (datum f).Cw,
      (datum f).K c ≤ (datum f).Iw 0 + δ → |(datum f).P c - p f| ≤ δ := by
    intro f δ hδ c hc hK
    have hK' : (datum f).K c ≤ frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f 0 + δ := by
      rwa [hIw f] at hK
    exact hsqueeze f δ hδ c hc hK'
  have h := finslerReadoutTiltDerivative_stationaryReadout_of_kinetic_squeeze
    datum p hsqueeze'
  have hfield : (fun f t => (datum f).Iw t) =
      fun f t => frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f t := by
    funext f t
    exact congrFun (hIw f) t
  rwa [hfield] at h

/-- **hderiv for the actual lane (atlas-glued population gluing family).**  The same
squeeze at the atlas-glued stationary pressure family of the population gluing
identity. -/
theorem finslerReadoutTiltDerivative_actualLane_atlas
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      PointProcess.MarkedCloudPoint → PointProcess.MarkedCloudPoint → ℝ)
    (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ)
    (hIw : ∀ f : FinalProbeSpace A B,
      (datum f).Iw = frozenPressureLower (K := A ∪ B) Seed a κ lambda
        (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q) q f)
    (hsqueeze : ActualLaneReadoutSqueeze datum
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda
        (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q) q) p) :
    FinslerReadoutTiltDerivative (frozenPressureLower (K := A ∪ B) Seed a κ lambda
      (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q) q) :=
  finslerReadoutTiltDerivative_actualLane (Seed := Seed) (a := a) (κ := κ)
    (lambda := lambda) (q := q)
    (g := atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q)
    datum p hIw hsqueeze

end OTSelector.Reconstruction
