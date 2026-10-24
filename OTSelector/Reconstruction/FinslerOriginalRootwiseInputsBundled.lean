import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit
import OTSelector.PointProcess.StationaryForwardMatching

/-!
# Bundled rootwise stationary inputs (no vacuous tilt quantifiers)

In V13 the hypotheses `hAcoef`, `hprobe` and `hprobe_bound` are stated with a
`(t : ℝ)` binder even though the tilt `t` does NOT occur in `coef φ j z x y` or
`probeFam φ j z x y` (it only occurs in `hM`, through `(Mst φ t) j z`).  This file
eliminates the vacuous tilts into one structure and reconstructs the vacuous forms via
projections:

* `RootwiseStationaryInputs α β coef probeFam Mst` with the four fields
  `hM`, `hAcoef`, `hprobe`, `hprobe_bound` (the last three WITHOUT the vacuous `t`);
* projections `.hAcoef_t`, `.hprobe_t`, `.hprobe_bound_t` reconstructing the
  vacuous `∀ t` forms expected by
  `frozenCampbellReadout_of_populationFocalValueLimit_and_attainment`;
* `rootwiseVacuousForms`: the single triple
  `(∀ φ t j z x y, 0 ≤ coef φ j z x y, ∀ φ t j z, Measurable ..., ∃ Gc, ∀ φ t j z x y,
  |probeFam φ j z x y| ≤ Gc)` that can be spliced directly at the call site.

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

/-- **Bundled rootwise stationary coefficient/probe inputs.**  The tilt `t` occurs only
where it is mathematically needed (in `hM`, via the matching family `Mst`). -/
structure RootwiseStationaryInputs
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) → StationaryForwardMatching α β) where
  hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M),
    FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z)
  hAcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M) (x y : ℝ),
    0 ≤ coef φ j z x y
  hprobe : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M),
    Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => probeFam φ j z p.1 p.2)
  hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : ℚ → M)
    (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc

namespace RootwiseStationaryInputs

variable {α β : Measure OTSelector.UnitMark}
  {coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ}
  {probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
    MarkedCloudPoint → MarkedCloudPoint → ℝ}
  {Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) → StationaryForwardMatching α β}

/-- The vacuous-tilt form of the coefficient nonnegativity, as consumed by
`frozenCampbellReadout_of_populationFocalValueLimit_and_attainment`. -/
theorem hAcoef_t (I : RootwiseStationaryInputs α β coef probeFam Mst) :
    ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M) (x y : ℝ),
      0 ≤ coef φ j z x y :=
  fun φ _ j z x y => I.hAcoef φ j z x y

/-- The vacuous-tilt form of the probe measurability. -/
theorem hprobe_t (I : RootwiseStationaryInputs α β coef probeFam Mst) :
    ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => probeFam φ j z p.1 p.2) :=
  fun φ _ j z => I.hprobe φ j z

/-- The vacuous-tilt form of the probe bound. -/
theorem hprobe_bound_t (I : RootwiseStationaryInputs α β coef probeFam Mst) :
    ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc := by
  obtain ⟨Gc, hGc⟩ := I.hprobe_bound
  exact ⟨Gc, fun φ _ j z x y => hGc φ j z x y⟩

/-- **The three reconstructed vacuous-∀t forms in one triple**, ready to splice into
`frozenCampbellReadout_of_populationFocalValueLimit_and_attainment` together with
`I.hM`. -/
theorem rootwiseVacuousForms (I : RootwiseStationaryInputs α β coef probeFam Mst) :
    (∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M) (x y : ℝ),
        0 ≤ coef φ j z x y) ∧
    (∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M),
        Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
          probeFam φ j z p.1 p.2)) ∧
    (∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc) :=
  ⟨I.hAcoef_t, I.hprobe_t, I.hprobe_bound_t⟩

end RootwiseStationaryInputs

end OTSelector.Reconstruction
