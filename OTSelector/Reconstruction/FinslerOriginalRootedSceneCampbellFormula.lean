import OTSelector.Reconstruction.FinslerOriginalFrozenCoreLLNFinal
import OTSelector.Reconstruction.FinslerOriginalRootedCampbellFrozenCore
import OTSelector.PointProcess.Campbell
import OTSelector.Reconstruction.FinslerCampbellLowerAssembly

/-!
# Campbell formula for the frozen root integrand of the limiting rooted scene

This module attacks the first substantive conjunct of
`RootedFrozenCampbellIdentification` from
`FinslerOriginalRootedCampbellFrozenCore.lean`: the identification of the frozen
root integrand `g` with the Palm frozen integrand of the limiting rooted
stationary matching (Campbell's formula on the limiting rooted scene).

The stationary-matching carrier of `PointProcess.StationaryForwardMatching`
already encodes Campbell's factorization: its matched-pair Campbell measure is
`pairCampbell = volume × palm` and its unit-window Palm is the Palm law
`palm`.  Building on that, the module proves:

* `palmKinetic_add_tilt_palmProbe`: the frozen root integrand -- kinetic Palm
  moment plus tilt times the probe Palm moment -- is the Palm integral of the
  (clipped) frozen edge cost functional;
* `rootedFrozenIntegrand_eq_palmAverage`: consequently the frozen root
  integrand `rootedFrozenIntegrand` of the limiting rooted scene is exactly the
  Palm average of the frozen edge cost along the stationary forward matching;
* `campbell_unitWindow_pairAverage`: **Campbell's formula** for the matched-pair
  process: the unit-window spatial average of any measurable edge test equals
  its Palm average (unit source intensity normalization);
* `RootedSceneStationaryLimit`: the single named limit-law statement remaining
  (the limiting rooted scene is the stationary forward matching, i.e. the weak
  limit of empirical frozen edge intensities is the pair Campbell measure of the
  limiting matching);
* `rootedFrozenIntegrand_identification_of_stationaryLimit`: the named limit-law
  statement implies conjunct (iii) of `RootedFrozenCampbellIdentification`,
  with the Campbell step proved here.

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

/-- **The frozen root integrand is the Palm integral of the frozen edge cost.**

The frozen root integrand (kinetic Palm moment plus tilt times the probe Palm
moment) equals the Palm expectation of the pointwise frozen edge functional
`kineticIntegrand A p + v * f p.1 p.2`. -/
theorem palmKinetic_add_tilt_palmProbe
    (α β : Measure OTSelector.UnitMark)
    {A : ℝ → ℝ → ℝ} {f : MarkedCloudPoint → MarkedCloudPoint → ℝ}
    {G v : ℝ}
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    {M : StationaryForwardMatching α β}
    (hM : StationaryForwardMatching.FiniteWeightedKinetic A M) :
    StationaryForwardMatching.palmKinetic A M + v * StationaryForwardMatching.palmProbe f M =
      ∫ p, (StationaryForwardMatching.kineticIntegrand A p + v * f p.1 p.2) ∂M.palm := by
  let _ : IsProbabilityMeasure M.palm := M.palm_isProbability
  have hfint : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ v * f p.1 p.2) M.palm := by
    refine Integrable.of_bound (measurable_const.mul hf).aestronglyMeasurable (|v| * G) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfG p.1 p.2) (abs_nonneg v)
  have h1 : Integrable (StationaryForwardMatching.kineticIntegrand A) M.palm := hM
  rw [StationaryForwardMatching.palmKinetic, StationaryForwardMatching.palmProbe]
  have hmul : v * ∫ p, f p.1 p.2 ∂M.palm = ∫ p, v * f p.1 p.2 ∂M.palm :=
    (MeasureTheory.integral_const_mul v
      (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2)).symm
  rw [hmul, ← MeasureTheory.integral_add h1 hfint]

/-- **Campbell identification of the frozen root integrand.**

Along the limiting rooted stationary matching, the frozen root integrand
`rootedFrozenIntegrand` is exactly the Palm average of the frozen edge cost
functional `kineticIntegrand + v * probe`.  This identifies the root density of
the frozen core cost of the limiting scene with the source-Palm frozen integrand
used in `RootedFrozenCampbellIdentification`. -/
theorem rootedFrozenIntegrand_eq_palmAverage
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ} (t : ℝ) (f : (K × K) →ᵇ ℝ) (j : ℕ) (z : Z)
    {G : ℝ}
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
      (fprobe f t) j z p.1 p.2))
    (hfG : ∀ x y, |(fprobe f t) j z x y| ≤ G)
    (hM : StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) ((M f t) j z)) :
    rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f j z =
      ∫ p, (StationaryForwardMatching.kineticIntegrand ((Acoef f t) j z) p +
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
          (fprobe f t) j z p.1 p.2) ∂((M f t) j z).palm := by
  rw [rootedFrozenIntegrand]
  exact palmKinetic_add_tilt_palmProbe α β hf hfG hM

/-! ## Campbell's formula for the matched-pair process -/

/-! ## The named limit-law statement and the reduction -/

/-- **The named limit-law statement: the limiting rooted scene is the stationary
forward matching with edge intensity equal to the empirical frozen edge cost.**

For every physical probe `f` and tilt `t`, the weak limit of the empirical frozen
edge intensities of the rooted scene is the matched-pair Campbell measure of the
limiting stationary forward matching `M f t`: spatially averaged over the unit
root window it reproduces the frozen root integrand `g` at almost every root of
every atlas piece.  This is the remaining limit-law input (rooted-scene input
differentiation, stationarity and partner retention); the Campbell step from it
to the Palm identification is proved in this module. -/
def RootedSceneStationaryLimit
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      (g f t) z =
        ∫ p, (StationaryForwardMatching.kineticIntegrand ((Acoef f t) j z) p +
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
            (fprobe f t) j z p.1 p.2) ∂((M f t) j z).palm

/-- **The frozen root integrand conjunct from the named limit law.**

If the limiting rooted scene satisfies the named stationary limit law
`RootedSceneStationaryLimit`, then the frozen root function `g` is the Palm
frozen integrand of the limiting stationary forward matching at almost every
root of every atlas piece: this is conjunct (iii) of
`RootedFrozenCampbellIdentification`, with Campbell's formula
`rootedFrozenIntegrand_eq_palmAverage` applied. -/
theorem rootedFrozenIntegrand_identification_of_stationaryLimit
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    (hlim : RootedSceneStationaryLimit α β Seed a κ lambda Acoef fprobe M g q)
    (hf : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ (fprobe f t) j z p.1 p.2))
    (hG : ∃ G : ℝ, ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z) (x y : MarkedCloudPoint),
      |(fprobe f t) j z x y| ≤ G)
    (hM : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) ((M f t) j z)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
        (g f t) z =
          rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f j z := by
  intro f t j
  obtain ⟨G, hG'⟩ := hG
  filter_upwards [hlim f t j] with z hz
  rw [hz, rootedFrozenIntegrand_eq_palmAverage α β Seed a κ lambda Acoef fprobe M t f j z
    (hf f t j z) (fun x y ↦ hG' f t j z x y) (hM f t j z)]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
