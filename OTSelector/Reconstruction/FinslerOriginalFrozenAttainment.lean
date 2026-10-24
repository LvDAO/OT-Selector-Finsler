import OTSelector.Reconstruction.FinslerOriginalFrozenStationaryPressureIdentification

/-!
# Frozen attainment of the weighted stationary pressure

This module closes the last F15 input, the frozen attainment inequality (P2).
Recall the frozen cost readout of the lane: for every physical probe, tilt and
population root it is the piecewise Palm frozen integrand
rootedFrozenPieceIntegrand built from the per-piece coefficient, probe and
stationary matching families, which on its own piece is the Palm frozen
integrand rootedFrozenIntegrand, namely the source-Palm kinetic moment plus
tilt times the source-Palm probe moment of the frozen matching.

## What the forward inequality already gives

The repository theorem rootedFrozen_hdom (a.e. the weighted stationary pressure
is dominated by the Palm frozen integrand along a stationary matching family in
the weighted class) yields, through
weightedStationaryPressure_le_frozenRootedCostReadout of the preceding module,

  weightedStationaryPressure at the scaled tilt <= frozen cost readout,

almost everywhere on every population seed piece.  This direction is exactly
the statement that the frozen matching is a member of the weighted stationary
class: membership, which is the hypothesis hM below, is a value upper bound for
the infimum defining the weighted stationary pressure.  Membership alone can
therefore never give the reverse inequality.

## What the reverse inequality needs

The reverse inequality is the statement that the frozen matching realizes the
infimum, i.e. that its Palm cost is a lower bound for the values of every
weighted-class matching at the root.  This is the paper's attainment theorem for
the weighted stationary pressure (main.tex definition
general-gluing-two-classes, paragraph after equation
general-gluing-uniform-pressure-bounds: the interior-collar compactness,
coercivity, lower semicontinuity and closed forward relation argument showing
that the weighted infimum is attained).  The repository proves the analogous
attainment statement for the legal original weighted stationary Poisson
matchings, exists_original_weighted_stationary_minimizer, but it does not
transfer it to the frozen limit matching family of the abstract weighted class
used by the F15 lane.

This module isolates that attainment as one typed theorem-shaped input,
FrozenMatchingMinimality: at almost every root of every piece, the frozen Palm
cost is a lower bound for the value of every finite weighted kinetic stationary
matching.  It then proves:

* frozenRootedCostReadout_eq_matchingCost: the frozen cost readout is the
  frozen matching's Palm value, by the piecewise definitional identification of
  the preceding module;
* frozenAttainment_of_frozenMatchingMinimality: the typed attainment input
  implies the frozen attainment inequality P2 (the frozen Palm cost is at most
  the infimum over the weighted class);
* frozenMatchingMinimality_of_frozenAttainment: conversely P2 implies the
  minimality input, using only the repository matching-cost bound
  weightedStationaryPressure_le_matchingCost; hence the typed input is exactly
  the content of P2 and the reduction loses nothing;
* frozenAttainment_iff_frozenMatchingMinimality: the two are equivalent under
  the lane data;
* frozenStationaryPressureIdentification_of_frozenMatchingMinimality: N2 (the
  per-root frozen stationary readout identification) follows from the single
  typed attainment input, composing with the equivalence of the preceding
  module;
* frozenStationaryPressureIdentification_iff_frozenMatchingMinimality: N2 is
  equivalent to the typed attainment input;
* frozenCampbellReadout_of_focalValueLimit_and_frozenMatchingMinimality: the
  frozen Campbell readout of F15 from the population focal-value limit and the
  typed attainment input alone.

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

/-! ## The frozen cost readout is the frozen matching's Palm value -/

/-- On its own population seed piece, the frozen cost readout of the lane is
the Palm value of the frozen stationary matching: the source-Palm kinetic
moment plus tilt times the source-Palm probe moment, both at the coefficient and
probe of that root.  This is the definitional identification of
rootedFrozenIntegrand combined with the piecewise formula of the preceding
module. -/
theorem frozenRootedCostReadout_eq_matchingCost
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) {φ : FinalProbeSpace A B} {t : ℝ} {j : ℕ} {z : Z}
    (hz : z ∈ populationSeedRootPiece Seed a κ lambda j) :
    frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        α β coef probeFam Mst q φ t z =
      palmKinetic (coef φ j z) ((Mst φ t) j z) +
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
          palmProbe (probeFam φ j z) ((Mst φ t) j z) := by
  rw [frozenRootedCostReadout_of_mem (Seed := Seed) (a := a) (κ := κ)
    (lambda := lambda) α β coef probeFam Mst q hz]
  rfl

/-! ## The typed attainment input -/

/-- The paper's attainment theorem for the weighted stationary pressure, at the
frozen limit matching of the lane, as a typed input.

At almost every root of every population seed piece, the frozen stationary
matching of the lane is value-minimal in the weighted stationary class at the
scaled tilt: its Palm frozen cost is a lower bound for the value of every
finite weighted kinetic stationary matching at that root.  Equivalently, the
frozen Palm cost is at most the infimum of the weighted stationary pressure.

Provenance: main.tex definition general-gluing-two-classes, paragraph after
equation general-gluing-uniform-pressure-bounds (the weighted infimum is
attained: increasing interior collars omit endpoint probabilities, coercivity
gives partner tails inside a collar, the prescribed endpoint marginal
probability is charged outside, a perfect matching is retained in the stationary
limit, and compact nonnegative cost truncations on interior collars prove lower
semicontinuity).  The repository proves the same statement for the legal
original weighted stationary Poisson matchings
(exists_original_weighted_stationary_minimizer) but has no transfer of that
minimizer to the frozen limit matching family of the abstract weighted class. -/
def FrozenMatchingMinimality
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
    ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
      ∀ (Q : StationaryForwardMatching α β),
        FiniteWeightedKinetic (coef φ j z) Q →
          rootedFrozenIntegrand (K := A ∪ B) α β Seed a κ lambda
            (fun φ' _ j z ↦ coef φ' j z)
            (fun φ' _ j z ↦ probeFam φ' j z) Mst q t φ j z ≤
            palmKinetic (coef φ j z) Q +
              (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
                palmProbe (probeFam φ j z) Q

/-- The typed attainment input implies the frozen attainment inequality P2: at
almost every root of every piece the frozen cost readout is at most the
weighted stationary pressure at the scaled tilt.  The frozen cost is the frozen
matching's Palm value, and a lower bound for the value of every weighted-class
matching bounds the infimum from below. -/
theorem frozenAttainment_of_frozenMatchingMinimality
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
    (q : ℝ)
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hmin : FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q) :
    FrozenAttainment (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      α β coef probeFam Mst q := by
  intro φ t j
  filter_upwards [hmin φ t j,
    frozenRootedCostReadout_ae_identification hF hcomplete hu ha hinj
      α β coef probeFam Mst q φ t j] with z hminz hzid
  rw [hzid, weightedStationaryPressure, stationaryValue]
  refine le_csInf
    ⟨(fun c : StationaryForwardMatching α β =>
        palmKinetic (coef φ j z) c +
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
            palmProbe (probeFam φ j z) c) ((Mst φ t) j z),
      ⟨(Mst φ t) j z, hM φ t j z, rfl⟩⟩ ?_
  rintro y ⟨Q, hQ, rfl⟩
  exact hminz Q hQ

/-- Conversely, the frozen attainment inequality P2 implies the typed
minimality input: the frozen cost dominates the weighted stationary pressure,
and the repository matching-cost bound
weightedStationaryPressure_le_matchingCost says the weighted stationary
pressure is dominated by the value of every weighted-class matching.  Hence P2
is not weaker than the typed attainment input. -/
theorem frozenMatchingMinimality_of_frozenAttainment
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
    (q : ℝ)
    (hA : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hf : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        probeFam φ j z p.1 p.2))
    (hG : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hAtt : FrozenAttainment (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      α β coef probeFam Mst q) :
    FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      α β coef probeFam Mst q := by
  obtain ⟨Gc, hGc⟩ := hG
  intro φ t j
  filter_upwards [hAtt φ t j,
    frozenRootedCostReadout_ae_identification hF hcomplete hu ha hinj
      α β coef probeFam Mst q φ t j] with z hatt hzid
  intro Q hQ
  rw [← hzid]
  exact hatt.trans (weightedStationaryPressure_le_matchingCost α β
    (A := coef φ j z) (f := probeFam φ j z) (G := Gc) (M := Q)
    (hA φ t j z) (hf φ t j z) (fun x y ↦ hGc φ t j z x y) hQ _)

/-- The frozen attainment inequality P2 is exactly the typed attainment input
at the frozen limit matching: lower bound over the weighted class equals the
value inequality.  This makes the residual input of the last F15 step the
paper's attainment theorem and nothing more. -/
theorem frozenAttainment_iff_frozenMatchingMinimality
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
    (q : ℝ)
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hA : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hf : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        probeFam φ j z p.1 p.2))
    (hG : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc) :
    FrozenAttainment (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        α β coef probeFam Mst q ↔
      FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) α β coef probeFam Mst q := by
  constructor
  · intro hAtt
    exact frozenMatchingMinimality_of_frozenAttainment hF hcomplete hu ha hinj
      α β coef probeFam Mst q hA hf hG hAtt
  · intro hmin
    exact frozenAttainment_of_frozenMatchingMinimality hF hcomplete hu ha hinj
      α β coef probeFam Mst q hM hmin

/-! ## N2 from the single typed attainment input -/

/-- N2, the per-root frozen stationary readout identification, follows from the
single typed attainment input: the frozen attainment inequality is the reverse
half, the forward half is the repository rootedFrozen_hdom comparison, and the
two agree at almost every root by the preceding module. -/
theorem frozenStationaryPressureIdentification_of_frozenMatchingMinimality
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
    (hmin : FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q) :
    FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda)
      (g := frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) α β coef probeFam Mst q) α β coef probeFam q :=
  (frozenStationaryPressureIdentification_iff_frozenAttainment hF hcomplete hu ha
    hinj α β coef probeFam Mst (q := q) hM hA hf hG).mpr
    (frozenAttainment_of_frozenMatchingMinimality hF hcomplete hu ha hinj
      α β coef probeFam Mst q hM hmin)

/-- N2 for the lane cost is equivalent to the typed attainment input. -/
theorem frozenStationaryPressureIdentification_iff_frozenMatchingMinimality
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
    (q : ℝ)
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
          (lambda := lambda) α β coef probeFam Mst q) α β coef probeFam q ↔
      FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) α β coef probeFam Mst q :=
  (frozenStationaryPressureIdentification_iff_frozenAttainment hF hcomplete hu ha
      hinj α β coef probeFam Mst (q := q) hM hA hf hG).trans
    (frozenAttainment_iff_frozenMatchingMinimality hF hcomplete hu ha hinj
      α β coef probeFam Mst q hM hA hf hG)

/-! ## The frozen Campbell readout from the typed attainment input -/

/-- The frozen Campbell readout of F15 from the population focal-value limit and
the typed attainment input alone: the attainment input replaces the frozen
attainment hypothesis of the preceding module, and everything else (the
population readout chain, the Campbell lower comparison, the Campbell formula on
the limiting rooted scene, the piecewise frozen cost identification and the
integration transfer) is proved. -/
theorem frozenCampbellReadout_of_focalValueLimit_and_frozenMatchingMinimality
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
    (hmin : FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q) :
    FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      (frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        α β coef probeFam Mst q) q datum :=
  frozenCampbellReadout_of_focalValueLimit_and_attainment hF hcomplete hu ha hinj
    datum Ag fg α β coef probeFam Mst q hM hA hf hG hDatum hFocal
    (frozenAttainment_of_frozenMatchingMinimality hF hcomplete hu ha hinj
      α β coef probeFam Mst q hM hmin)

end OTSelector.Reconstruction