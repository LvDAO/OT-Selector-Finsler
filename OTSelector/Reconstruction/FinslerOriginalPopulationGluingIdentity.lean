import OTSelector.Reconstruction.FinslerOriginalFocalValueEqualityReduction
import OTSelector.Reconstruction.FinslerOriginalAtlasSceneBridge
import OTSelector.Reconstruction.FinslerOriginalScenePressureWiring

/-!
# Structural reduction of the population gluing identity P1

This module attacks the population gluing identity P1 itself, the sharp residual
of the population focal-value chain.  P1 (PopulationFocalValueLimit, equivalently
CampbellAveragedStationaryPressureIdentification) is the statement

  forall (probe phi) (tilt t),
    weightedStationaryPressure alpha beta (Ag phi) (fg phi) t
      = sum over j of the integral over the population seed root piece j of
          theta_j(z) to the power (-2 over q) times
            weightedStationaryPressure alpha beta (coef phi j z) (probeFam phi j z)
              (t times theta_j(z) to the power (2 over q)).

## 1. Exact definitional unfolding of both sides

The left side is the weighted stationary pressure, the stationary infimum of the
kinetic plus tilt times probe functional over the weighted stationary class
(repository theorem weightedStationaryPressure_eq_sInf, which is definitional:

  weightedStationaryPressure alpha beta A f v
    = sInf ((fun M => palmKinetic A M + v * palmProbe f M) '' weightedClass alpha beta A)).

The right side is the Campbell average of the per-root weighted stationary
pressures: it is definitionally the sum over the population seed pieces of the
theta-to-the-minus-two-over-q weighted per-root pressure at the scaled tilt.
populationFocalValueLimit_iff_sInf_form records both unfoldings in one exact
statement: P1 holds exactly when the global stationary infimum equals the atlas
sum of the per-root stationary infima at the scaled tilts.  The right side is
also definitionally campbellAveragedStationaryPressure, hence P1 is exactly
CampbellAveragedStationaryPressureIdentification.

## 2. The structural reduction

The Campbell average is a sum of piece integrals with piece-dependent integrands,
while the repository's frozen-cost object campbellAveragedFrozenCost is a single
sum over pieces of one root function.  The atlas piece gluing atlasPiecewiseRoot
bridges the two: the first-owner gluing of the family of per-root pressures
agrees with the j-th family member almost everywhere on piece j
(ae_atlasPiecewiseRoot_eq), so there is a single population root function

  atlasGluedStationaryPressureRoot phi t
    = the atlas-glued per-root weighted stationary pressure at tilt t,

and the right side of P1 is exactly the frozen Campbell average
campbellAveragedFrozenCost of that single root function
(campbellAveragedStationaryPressure_eq_frozenCost_of_atlasGluing, an algebraic
consequence of the sum and integral definitions, with no analytic content).

Consequently P1 is equivalent to the single equality

  forall phi t,
    weightedStationaryPressure alpha beta (Ag phi) (fg phi) t
      = campbellAveragedFrozenCost Seed a kappa lambda
          (atlasGluedStationaryPressureRoot phi t) q,

named AtlasCampbellPressureIdentification: the global weighted stationary
pressure is the frozen population Campbell average of the atlas-glued per-root
weighted stationary pressure.  This is the paper's Campbell averaging identity
over the rooted scene; everything on the right side is the repository's frozen
pressure object, whose Palm identification is developed in
FinslerOriginalAtlasSceneBridge and FinslerOriginalScenePressureWiring.

The same residual can be written in the exact type of the assembly's frozen
lower-pressure readout frozenPressureLower of FinslerOriginalScenePressureWiring
(the function whose value at (phi, t) is the frozen Campbell cost of the frozen
readout family): P1 holds exactly when the global weighted stationary pressure
equals frozenPressureLower of the atlas-glued stationary pressure family.

## 3. Sharpest residual, exact type

P1 is equivalent to

  forall (phi : FinalProbeSpace A B) (t : R),
    weightedStationaryPressure alpha beta (Ag phi) (fg phi) t
      = frozenPressureLower (K := A union B) Seed a kappa lambda
          (atlasGluedStationaryPressureFamily alpha beta coef probeFam q) q phi t,

i.e. the global weighted stationary pressure is the assembled frozen population
pressure readout of the atlas-glued per-root pressure family.  This is a single
equality of real numbers per probe and tilt, with no sum, no integral and no
piece decomposition left: it is the Campbell averaging identity of the paper.

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
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}

/-! ## The per-root pressure family and its atlas gluing -/

/-- The family of per-root weighted stationary pressures of the population atlas
at one probe and tilt: the integrand family of the right side of P1. -/
noncomputable def atlasStationaryPressureFamily
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (φ : FinalProbeSpace A B) (t : ℝ) : ℕ → Z → ℝ :=
  fun j z =>
    weightedStationaryPressure α β (coef φ j z) (probeFam φ j z)
      (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))

/-- The single population root function obtained by first-owner atlas gluing of
the per-root weighted stationary pressure family. -/
noncomputable def atlasGluedStationaryPressureRoot
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (φ : FinalProbeSpace A B) (t : ℝ) : Z → ℝ :=
  atlasPiecewiseRoot Seed a κ lambda
    (atlasStationaryPressureFamily Seed a κ lambda α β coef probeFam q φ t)

/-- The atlas-glued stationary pressure family as a function of probe and tilt,
the exact argument shape of the assembly's frozen lower-pressure readout. -/
noncomputable def atlasGluedStationaryPressureFamily
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : FinalProbeSpace A B → ℝ → Z → ℝ :=
  fun φ t => atlasGluedStationaryPressureRoot Seed a κ lambda α β coef probeFam q φ t

/-! ## 1. The exact definitional unfolding of both sides -/

/-- **The exact definitional unfolding of P1.**  P1 holds if and only if, at every
probe and tilt, the global weighted stationary infimum over the global weighted
stationary class equals the atlas sum of the per-root weighted stationary
infima over the per-root weighted stationary classes at the scaled tilts.  Both
sides are written purely through the repository's stationary infimum
(weightedStationaryPressure_eq_sInf is definitional). -/
theorem populationFocalValueLimit_iff_sInf_form
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      ∀ (φ : FinalProbeSpace A B) (t : ℝ),
        sInf ((fun M : StationaryForwardMatching α β =>
            palmKinetic (Ag φ) M + t * palmProbe (fg φ) M) ''
              weightedClass α β (Ag φ)) =
          ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
            populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
              sInf ((fun M : StationaryForwardMatching α β =>
                  palmKinetic (coef φ j z) M +
                    (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
                      palmProbe (probeFam φ j z) M) ''
                weightedClass α β (coef φ j z)) ∂lambda := by
  unfold PopulationFocalValueLimit
  simp only [weightedStationaryPressure_eq_sInf]

/-- The right side of P1 is definitionally the Campbell average of the per-root
weighted stationary pressures.  Together with the stationary infimum unfolding
of the left side this gives the complete definitional reading of the identity. -/
theorem populationFocalValueLimit_iff_campbell_identification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      ∀ (φ : FinalProbeSpace A B) (t : ℝ),
        weightedStationaryPressure α β (Ag φ) (fg φ) t =
          campbellAveragedStationaryPressure α β Seed a κ lambda
            (coef φ) (probeFam φ) q t := by
  unfold PopulationFocalValueLimit
  apply forall_congr'
  intro φ
  apply forall_congr'
  intro t
  rw [campbellAveragedStationaryPressure_def α β Seed a κ lambda
    (coef φ) (probeFam φ) q t]

/-! ## 2. The algebraic reduction to the frozen Campbell average -/

/-- The right side of P1 is definitionally the piece-dependent frozen Campbell
average of the per-root pressure family. -/
theorem campbellAveragedStationaryPressure_eq_frozenCostFamily
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (φ : FinalProbeSpace A B) (t : ℝ) :
    campbellAveragedStationaryPressure α β Seed a κ lambda
        (coef φ) (probeFam φ) q t =
      campbellAveragedFrozenCostFamily Seed a κ lambda
        (atlasStationaryPressureFamily Seed a κ lambda α β coef probeFam q φ t) q := by
  rw [campbellAveragedStationaryPressure_def α β Seed a κ lambda
      (coef φ) (probeFam φ) q t,
    campbellAveragedFrozenCostFamily_def]
  rfl

/-- The piece-dependent frozen Campbell average of a family is the frozen
Campbell average of the atlas-glued root function of that family.  This is the
repository atlas piece gluing theorem, used in the structural reduction. -/
theorem campbellAveragedFrozenCostFamily_eq_frozenCost_atlasPiecewiseRoot
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (G : ℕ → Z → ℝ) (q : ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGluingMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    campbellAveragedFrozenCostFamily Seed a κ lambda G q =
      campbellAveragedFrozenCost Seed a κ lambda
        (atlasPiecewiseRoot Seed a κ lambda G) q := by
  rw [campbellAveragedFrozenCostFamily_def]
  exact (campbellAveragedFrozenCost_atlasPiecewiseRoot_eq_tsum Seed a κ lambda G
    hF hcomplete hu ha hinj (q := q)).symm

/-- **The structural identity.**  The right side of P1 equals the frozen
population Campbell average of the atlas-glued per-root weighted stationary
pressure root function.  No analytic content enters: this is the definition of
the Campbell average together with the atlas piece gluing. -/
theorem campbellAveragedStationaryPressure_eq_frozenCost_of_atlasGluing
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (φ : FinalProbeSpace A B) (t : ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGluingMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    campbellAveragedStationaryPressure α β Seed a κ lambda
        (coef φ) (probeFam φ) q t =
      campbellAveragedFrozenCost Seed a κ lambda
        (atlasGluedStationaryPressureRoot Seed a κ lambda α β coef probeFam q φ t) q := by
  rw [campbellAveragedStationaryPressure_eq_frozenCostFamily]
  exact campbellAveragedFrozenCostFamily_eq_frozenCost_atlasPiecewiseRoot
    Seed a κ lambda
    (atlasStationaryPressureFamily Seed a κ lambda α β coef probeFam q φ t) q
    hF hcomplete hu ha hinj

/-! ## 3. The single missing equality -/

/-- **The single missing equality of P1.**  The global weighted stationary
pressure is the frozen population Campbell average of the atlas-glued per-root
weighted stationary pressure root function.  This is the paper's Campbell
averaging identity over the rooted scene: a single equality per probe and tilt,
with the sum over pieces and the piece integrals absorbed into the repository's
frozen Campbell average. -/
def AtlasCampbellPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    weightedStationaryPressure α β (Ag φ) (fg φ) t =
      campbellAveragedFrozenCost Seed a κ lambda
        (atlasGluedStationaryPressureRoot Seed a κ lambda α β coef probeFam q φ t) q

/-- **P1 reduces exactly to the single missing equality.**  The population
gluing identity holds if and only if the global weighted stationary pressure is
the frozen population Campbell average of the atlas-glued per-root weighted
stationary pressure root function. -/
theorem populationFocalValueLimit_iff_atlasCampbellPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGluingMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      AtlasCampbellPressureIdentification Seed a κ lambda α β Ag fg coef probeFam q := by
  constructor
  · intro h φ t
    have hglue := campbellAveragedStationaryPressure_eq_frozenCost_of_atlasGluing
      Seed a κ lambda α β coef probeFam q φ t hF hcomplete hu ha hinj
    rw [h φ t]
    exact hglue
  · intro h φ t
    have hglue := campbellAveragedStationaryPressure_eq_frozenCost_of_atlasGluing
      Seed a κ lambda α β coef probeFam q φ t hF hcomplete hu ha hinj
    rw [h φ t]
    exact hglue.symm

/-- The single missing equality implies P1. -/
theorem populationFocalValueLimit_of_atlasCampbellPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGluingMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (h : AtlasCampbellPressureIdentification Seed a κ lambda α β Ag fg coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  (populationFocalValueLimit_iff_atlasCampbellPressureIdentification Seed a κ lambda
    Ag fg α β coef probeFam q hF hcomplete hu ha hinj).mpr h

/-! ## 4. The residual in the exact type of the assembly's pressure readout -/

/-- The frozen lower-pressure readout of the atlas-glued stationary pressure
family is the frozen Campbell average of the atlas-glued per-root pressure root
function, by definition. -/
theorem frozenPressureLower_atlasGluedStationaryPressureFamily
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    frozenPressureLower (K := A ∪ B) Seed a κ lambda
        (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q) q =
      fun φ t => campbellAveragedFrozenCost Seed a κ lambda
        (atlasGluedStationaryPressureRoot Seed a κ lambda α β coef probeFam q φ t) q := rfl

/-- **The sharpest residual in the exact type of the assembly pressure readout.**
P1 holds if and only if the global weighted stationary pressure equals the
frozen lower-pressure readout, evaluated at the atlas-glued per-root stationary
pressure family: one scalar equality per probe and tilt, with no sum, integral
or piece decomposition left. -/
theorem populationFocalValueLimit_iff_frozenPressureLowerIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGluingMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      ∀ (φ : FinalProbeSpace A B) (t : ℝ),
        weightedStationaryPressure α β (Ag φ) (fg φ) t =
          frozenPressureLower (K := A ∪ B) Seed a κ lambda
            (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q)
            q φ t := by
  rw [frozenPressureLower_atlasGluedStationaryPressureFamily]
  exact populationFocalValueLimit_iff_atlasCampbellPressureIdentification Seed a κ lambda
    Ag fg α β coef probeFam q hF hcomplete hu ha hinj

end OTSelector.Reconstruction