import OTSelector.Reconstruction.FinslerOriginalLaneDatumIdentification
import OTSelector.Reconstruction.FinslerOriginalFrozenAttainment

/-!
# Attacking hsqueeze: the zero-tilt near-minimizer readout

The last derivative residual is `ActualLaneReadoutSqueeze datum P p`
(`FinslerOriginalActualLaneSqueeze`): every almost kinetic-minimal admissible matching
(`K c <= P f 0 + δ`) has the mark probe within δ of the limit readout `p f`.

This file attacks it and pins down the exact gap:

* `ZeroTiltNearMinimizerReadoutUniform datum p` — the same content written purely inside
  the datum family (energy tolerance and probe error the SAME δ, with `K c <= Iw 0 + δ`),
  so it no longer mentions the lane pressure field at all.
* `actualLaneReadoutSqueeze_iff_uniform`: at the lane field (`hIw`, batch107) the squeeze
  is EXACTLY this datum-internal uniform statement.
* `zeroTiltNearMinimizerReadout_of_uniform`: the uniform statement gives the paper's
  `main.tex:9046-9050` sequence form ("the same holds in the limit for any weighted
  near-minimizing sequence"): along any sequence with `K c_n -> Iw 0`, the probes
  converge to the limit readout.  The converse is NOT available without a modulus/rate.
* `finslerReadoutTiltDerivative_frozenLowerField_of_uniformNearMinimizerReadout`: with the
  endgame assembly's frozen Campbell readout (`hC`) and the uniform statement alone, the
  V4 endgame `pressureLower` field carries the readout tilt derivative.

## Exact gap
The frozen attainment / matching minimality (`FrozenMatchingMinimality`) gives the VALUE
identification (optimal frozen matching realizes the weighted stationary pressure).  The
paper's :9046-9050 gives only the LIMIT (sequence) readout form proved below from the
uniform statement.  The uniform statement itself is strictly stronger: it requires a
modulus `|P c - Iw'(0)| <= δ` at energy excess δ, which is NOT implied by value
attainment or by the sequence limit.  The paper's differentiability proof avoids this by
comparing one-sided derivatives with competitors (weighted-capped one-sided derivatives /
diffuse agreement), not by a uniform near-minimizer Lipschitz bound; the Lean producer
`hasDerivAt_stationaryValue_of_kinetic_squeeze` consumes the uniform form, so this is the
exact remaining typed input.  No `sorry`, `admit` or added axiom.
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

/-- **The sharpest typed residual, datum-internal.**  Every almost kinetic-minimal
admissible matching has probe within the SAME δ of the limit readout `p`. -/
def ZeroTiltNearMinimizerReadoutUniform {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ) : Prop :=
  ∀ (f : FinalProbeSpace A B) (δ : ℝ), 0 < δ → ∀ c ∈ (datum f).Cw,
    (datum f).K c ≤ (datum f).Iw 0 + δ → |(datum f).P c - p f| ≤ δ

/-- At the lane pressure field, the actual-lane squeeze is EXACTLY the datum-internal
uniform statement. -/
theorem actualLaneReadoutSqueeze_iff_uniform
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (laneField : FinalPressureField A B) (p : FinalProbeSpace A B → ℝ)
    (hIw : ∀ f : FinalProbeSpace A B, (datum f).Iw = laneField f) :
    ActualLaneReadoutSqueeze datum laneField p ↔
      ZeroTiltNearMinimizerReadoutUniform datum p := by
  constructor
  · intro h f δ hδ c hc hK
    refine h f δ hδ c hc ?_
    rw [← hIw f]
    exact hK
  · intro h f δ hδ c hc hK
    refine h f δ hδ c hc ?_
    rw [hIw f]
    exact hK

/-- The uniform statement gives the paper's `:9046-9050` limit form: along any weighted
near-minimizing sequence the probes converge to the limit readout. -/
theorem zeroTiltNearMinimizerReadout_of_uniform
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ)
    (h : ZeroTiltNearMinimizerReadoutUniform datum p) :
    ∀ (f : FinalProbeSpace A B) (c : ℕ → W), (∀ n, c n ∈ (datum f).Cw) →
      Tendsto (fun n => (datum f).K (c n)) atTop (𝓝 ((datum f).Iw 0)) →
      Tendsto (fun n => (datum f).P (c n)) atTop (𝓝 (p f)) := by
  intro f c hc hK
  rw [Metric.tendsto_atTop] at hK ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := hK (ε / 2) hε2
  refine ⟨N, fun n hn => ?_⟩
  have hKle : (datum f).K (c n) < (datum f).Iw 0 + ε / 2 := by
    have hd := hN n hn
    rw [Real.dist_eq] at hd
    have hlt := (abs_lt.mp hd).2
    linarith
  have hb := h f (ε / 2) hε2 (c n) (hc n) (le_of_lt hKle)
  rw [Real.dist_eq]
  calc |(datum f).P (c n) - p f| ≤ ε / 2 := hb
    _ < ε := by linarith

/-- **V4 hderiv from the uniform residual alone.**  With the endgame assembly's frozen
Campbell readout and the datum-internal uniform near-minimizer bound (no lane-field
statement needed), the endgame pressureLower field carries the readout tilt derivative. -/
theorem finslerReadoutTiltDerivative_frozenLowerField_of_uniformNearMinimizerReadout
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum)
    (p : FinalProbeSpace A B → ℝ)
    (huniform : ZeroTiltNearMinimizerReadoutUniform datum p) :
    FinslerReadoutTiltDerivative
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) := by
  have hIw := frozenCampbellReadout_Iw_eq_frozenPressureLower Seed a κ lambda g q datum hC
  exact finslerReadoutTiltDerivative_frozenLowerField_of_squeeze
    (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
    (g := g) (q := q) (datum := datum) (hC := hC) (p := p)
    (hsqueeze := (actualLaneReadoutSqueeze_iff_uniform datum
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) p hIw).mpr huniform)

end OTSelector.Reconstruction
