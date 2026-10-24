import OTSelector.Reconstruction.FinslerOriginalFrozenCoreCampbellIdentification
import OTSelector.Reconstruction.FinslerCampbellLowerAssembly
import OTSelector.PointProcess.StationaryForwardMatching

/-!
# Rooted-scene Campbell identification for the frozen core functional

This module closes the *structural* half of the remaining lower-pressure input.
It proves the `hdom` input of
`campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost` -- the
per-root domination of the weighted stationary pressure by the frozen root
integrand -- from the existence of a *limiting forward stationary matching* in
the weighted class, and it isolates the one remaining analytic fact as a single
named statement `RootedFrozenCampbellIdentification`:

* `rootedFrozenIntegrand`: the source-Palm average of the frozen kinetic cost
  plus tilt times the frozen probe along a family of stationary forward
  matchings;
* `rootedFrozen_hdom`: **the `hdom` input, proved**: along any family of
  stationary forward matchings in the weighted class, the weighted stationary
  pressure at almost every root of every atlas piece is dominated by the Palm
  frozen integrand;
* `RootedFrozenCampbellIdentification`: the single named stationary-matching
  statement.  It bundles (i) the limiting matching family in the weighted class,
  (ii) the identification of the frozen root integrand `g` with the Palm frozen
  integrand of that matching at almost every root of every piece (Campbell's
  formula for the limiting rooted scene), (iii) the Campbell mean bound for the
  actual frozen core functional, and (iv) the technical integrability/boundedness
  side conditions of the atlas comparison;
* `campbellAveragedStationaryPressure_le_frozen_of_rootedCampbell`: the named
  statement implies `P_w(t) ≤` the Campbell-averaged frozen cost;
* `frozenMeanLower_of_rootedFrozenCampbell`: the named statement implies the
  frozen-core LLN, i.e. exactly the hypothesis `hfrozen_mean` of
  `physical_finsler_probability_lower_of_frozen_mean_lower`.  Hence, together
  with the already-proved finite-domination/concentration chain, the assembly's
  `hprob` at `P_w(t)` follows from this one named statement.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open OTSelector.Reconstruction OTSelector.PointProcess

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

variable {K : Set M} {u : M → ℝ}

/-- **The frozen root integrand of a family of stationary forward matchings.**

At root `z` in piece `j` and tilt `t`: the source-Palm average of the frozen
kinetic cost plus tilt times the frozen probe, evaluated on the stationary
matching `M f t j z`.  This is the frozen counterpart of the weighted stationary
pressure `I_w(z, t θ^(2/q))`. -/
noncomputable def rootedFrozenIntegrand
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) (t : ℝ) (f : (K × K) →ᵇ ℝ) (j : ℕ) (z : Z) : ℝ :=
  StationaryForwardMatching.palmKinetic ((Acoef f t) j z) ((M f t) j z) +
    (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
      StationaryForwardMatching.palmProbe ((fprobe f t) j z) ((M f t) j z)

/-- **The `hdom` input of the atlas Campbell comparison, proved.**

Along any family of stationary forward matchings in the weighted class, with
nonnegative kinetic coefficients and a bounded measurable probe family, the
weighted stationary pressure at almost every root of every atlas piece is
dominated by the Palm frozen integrand of the matching.  This is exactly the
`hdom` hypothesis of
`campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost`, so the only
remaining content is the identification of the frozen root function `g` with
that Palm integrand (Campbell's formula on the limiting rooted scene). -/
theorem rootedFrozen_hdom
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (hM : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) ((M f t) j z))
    (hA : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z) (a b : ℝ),
      0 ≤ (Acoef f t) j z a b)
    (hf : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ (fprobe f t) j z p.1 p.2))
    (hG : ∃ G : ℝ, ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z) (x y : MarkedCloudPoint),
      |(fprobe f t) j z x y| ≤ G)
    (hg : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
        (g f t) z =
          rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f j z) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
        StationaryForwardMatching.weightedStationaryPressure α β
          ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ≤ (g f t) z := by
  intro f t j
  obtain ⟨G, hG'⟩ := hG
  filter_upwards [hg f t j] with z hz
  rw [hz, rootedFrozenIntegrand]
  exact weightedStationaryPressure_le_matchingCost α β (hA f t j z)
    (hf f t j z) (fun x y ↦ hG' f t j z x y) (hM f t j z) _

/-- **The single named remaining stationary-matching statement.**

For every physical probe `f` and tilt `t` there is a root family of stationary
forward matchings `M f t` in the weighted class whose source-Palm frozen
integrand `g` (kinetic plus tilt times probe) has the following two properties:

* (Campbell's formula on the limiting rooted scene) `g` equals the Palm frozen
  integrand of `M` at almost every root of every atlas piece;
* (Campbell mean bound) the expected normalized frozen core cost is
  asymptotically at least the Campbell-averaged frozen cost of `g` plus the
  probe constant `|t| ‖f‖`;

together with the technical atlas-comparison side conditions.  This is the
precise remaining analytic input of the lower-pressure lane. -/
def RootedFrozenCampbellIdentification
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ)
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ) : Prop :=
  (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
    StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) ((M f t) j z)) ∧
  (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z) (a b : ℝ),
    0 ≤ (Acoef f t) j z a b) ∧
  (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
    Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ (fprobe f t) j z p.1 p.2)) ∧
  (∃ G : ℝ, ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z) (x y : MarkedCloudPoint),
    |(fprobe f t) j z x y| ≤ G) ∧
  (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      (g f t) z =
        rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f j z) ∧
  (∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
    campbellAveragedFrozenCost Seed a κ lambda (g f t) q + |t| * (‖f‖₊ : ℝ) - ε ≤
      ∫ s, frozenCost f t n s ∂P n) ∧
  (∃ (BI Bg : ((K × K) →ᵇ ℝ) → ℝ → ℝ),
    (∀ f t, 0 ≤ BI f t) ∧ (∀ f t, 0 ≤ Bg f t) ∧
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      IntegrableOn
        (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          StationaryForwardMatching.weightedStationaryPressure α β
            ((Acoef f t) j z) ((fprobe f t) j z)
            (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)))
        (populationSeedRootPiece Seed a κ lambda j) lambda) ∧
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      IntegrableOn
        (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * (g f t) z)
        (populationSeedRootPiece Seed a κ lambda j) lambda) ∧
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      |populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
        StationaryForwardMatching.weightedStationaryPressure α β
          ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))| ≤ BI f t) ∧
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      |populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * (g f t) z| ≤ Bg f t))


/-- **The atlas Campbell comparison from the named rooted-scene identification.**

Extracting the matching data and side conditions from
`RootedFrozenCampbellIdentification`, the `hdom` input is proved by
`rootedFrozen_hdom` and the already-proved atlas comparison yields
`P_w(t) ≤` the Campbell-averaged frozen cost for every physical probe and tilt. -/
theorem campbellAveragedStationaryPressure_le_frozen_of_rootedCampbell
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedCampbellMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (a : M → Z) (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {q : ℝ}
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hId : RootedFrozenCampbellIdentification α β Seed a κ lambda Acoef fprobe M g q P
      frozenCost) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      campbellAveragedStationaryPressure α β Seed a κ lambda (Acoef f t) (fprobe f t) q t ≤
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q := by
  obtain ⟨hM, hA, hf, hG, hg, _hmean, BI, Bg, hBI, hBg, hintI, hintg, hI_bound,
    hg_bound⟩ := hId
  have hdom := rootedFrozen_hdom α β Seed a κ lambda Acoef fprobe M g hM hA hf hG hg
  exact campbellAveragedStationaryPressure_family_le_campbellAveragedFrozenCost
    hF hcomplete u hu a ha hinj α β Seed κ lambda Acoef fprobe g BI Bg hBI hBg
    hdom hintI hintg hI_bound hg_bound

/-- **The frozen-core LLN from the named rooted-scene identification.**

This is the exact hypothesis `hfrozen_mean` consumed by
`physical_finsler_probability_lower_of_frozen_mean_lower`: from the single named
stationary-matching statement, the expected normalized frozen core cost is
asymptotically at least the Campbell-averaged stationary pressure `P_w(t)` plus
the probe constant `|t| ‖f‖`.  Consequently the whole lower-pressure lane
(assembly `hprob` at `P_w(t)`) follows from `RootedFrozenCampbellIdentification`
together with the already-proved finite-domination and concentration chain. -/
theorem frozenMeanLower_of_rootedFrozenCampbell
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedCampbellMeanMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (a : M → Z) (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {q : ℝ}
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hId : RootedFrozenCampbellIdentification α β Seed a κ lambda Acoef fprobe M g q P
      frozenCost) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      campbellAveragedStationaryPressure α β Seed a κ lambda (Acoef f t) (fprobe f t) q t +
        |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n := by
  obtain ⟨hM, hA, hf, hG, hg, hmean, BI, Bg, hBI, hBg, hintI, hintg, hI_bound,
    hg_bound⟩ := hId
  have hdom := rootedFrozen_hdom α β Seed a κ lambda Acoef fprobe M g hM hA hf hG hg
  have hle : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      campbellAveragedStationaryPressure α β Seed a κ lambda (Acoef f t) (fprobe f t) q t ≤
      campbellAveragedFrozenCost Seed a κ lambda (g f t) q :=
    campbellAveragedStationaryPressure_family_le_campbellAveragedFrozenCost
      hF hcomplete u hu a ha hinj α β Seed κ lambda Acoef fprobe g BI Bg hBI hBg
      hdom hintI hintg hI_bound hg_bound
  exact frozenMeanLower_of_campbellFrozenMean P
    (fun f t ↦ campbellAveragedStationaryPressure α β Seed a κ lambda (Acoef f t)
      (fprobe f t) q t)
    (fun f t ↦ campbellAveragedFrozenCost Seed a κ lambda (g f t) q)
    hle frozenCost hmean

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
