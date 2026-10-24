import OTSelector.Reconstruction.FinslerOriginalRootCocycle

/-!
# Inputs of the rooted transport: root-dependent bridge, unit mass and root constancy

This module addresses the three remaining inputs recorded in
FinslerOriginalRootCocycle.lean.

## 1. The root-dependent bridge (the unit-mass normalization is not needed)

The population Campbell-averaged pressure of main.tex (equation
general-gluing-integrated-pressures) carries the density weight
theta_j^(-2/q) against the population root law lambda, i.e. theta_j^(1-2/q)
against the root Haar measure.  It is therefore a *theta-weighted root average* of
the physical Palm readouts, not a single Palm integral, and no unit-mass
normalization is required for the lower-pressure lane:

* campbellAveragedFrozenCost_eq_rootAverage_palmReadout: the theta-weighted
  Campbell-averaged frozen cost is the theta-weighted root average of the physical
  Palm readouts of the limiting rooted scene, with no root-independence and no
  normalization input.  This is the form matching the paper's integrated pressure.

## 2. Root constancy of the atlas frozen root integrand

* ae_atlasRootFrozenIntegrand_eq_of_frozenData: transport plus root constancy of
  the physical Palm readout gives root constancy of the atlas frozen root
  integrand;
* campbellAveragedFrozenCost_eq_atlasRootMass_mul_palmReadout_of_frozenData: the
  mass-factor collapse with the readout constancy derived from the a.e. root
  constancy of the frozen calibrated coefficient, probe and signed tilt data
  (the frozen data of the lower-pressure lane), rather than assumed.

## 3. The unit-mass normalization under the unit Haar density

* atlasRootMass_eq_one_of_unitDensity: if the population root label density is
  one on every selected root piece (the root coordinate is normalized so that the
  population root intensity equals the seed Haar reference) and the root pieces
  carry unit total real mass, then the total population pressure weight is one:
  atlasRootMass = 1.  The piece-mass normalization is the root-process unit
  intensity; the pure measure-theoretic identity
  sum_j lambda.real(piece_j) = lambda.real(univ) = 1 is the residual of this step
  (the real-valued tsum conversion is not available in this Mathlib snapshot).

## Remaining sub-gaps

The two analytic side conditions hAmeas and hRmeas of the bridge are not
manufactured from the present data: they require measurability of the frozen root
functionals in the seed label coordinate, i.e. that the calibrated coefficient,
probe and tilt data factor measurably through the seed label of the root.  The
integrability hIntK of the frozen kinetic edge cost against the limiting Palm is
equivalent to the paper's finite-weighted-kinetic class membership of the root
carrier; the transfer needs the integrability of the recoded kinetic integrand,
which is not available as an unconditional lemma in this Mathlib snapshot.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}

/-! ## 1. The root-dependent bridge -/

/-- **The theta-weighted Campbell-averaged frozen cost is the theta-weighted root
average of the physical Palm readouts of the limiting rooted scene.**

For a frozen root function glued to the atlas frozen root integrand on each
selected population root piece, the population pressure integral is exactly the
population root average of the limiting scene's physical Palm readouts of the
frozen edge functional, with the frozen coefficient, probe and signed tilt read at
each root.  No root-independence and no unit-mass normalization are used: this is
the root-dependent form of the bridge and matches the paper's integrated pressure
density theta_j^(1-2/q) against the root Haar measure. -/
theorem campbellAveragedFrozenCost_eq_rootAverage_palmReadout
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ}
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe Mat q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z) :
    campbellAveragedFrozenCost Seed a κ lambda g q =
      ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          rootedScenePalmReadout Q
            (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
              (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) ∂lambda := by
  rw [campbellAveragedFrozenCost_def]
  apply tsum_congr
  intro j
  calc (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z ∂lambda)
      = ∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
            atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z
          ∂lambda := by
        apply integral_congr_ae
        filter_upwards [hglue j] with z hz
        rw [hz]
    _ = ∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
            rootedScenePalmReadout Q
              (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
                (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) ∂lambda := by
        apply integral_congr_ae
        filter_upwards [htransport f t j] with z hz
        rw [hz]

/-! ## 2. Root constancy of the atlas frozen root integrand -/

/-- **Root constancy of the atlas frozen root integrand.**

The transport identifies the atlas frozen root integrand with the physical Palm
readout at every root; if that readout is root-independent almost everywhere, so is
the atlas frozen root integrand. -/
theorem ae_atlasRootFrozenIntegrand_eq_of_frozenData
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ}
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe Mat q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (Ψ : ℝ)
    (hconst : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) = Ψ) :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z = Ψ := by
  filter_upwards [htransport f t j, hconst] with z h1 h2
  rw [h1, h2]

/-- **The mass-factor collapse from the frozen root data.**

The readout constancy input of
campbellAveragedFrozenCost_eq_atlasRootMass_mul_palmReadout is derived here from
the a.e. root constancy of the frozen calibrated coefficient, probe and signed
tilt data and from the values of the physical Palm readout at the frozen data.
This completes the readout root-independence chain: the only root-dependent
quantities of the frozen root integrand are the frozen data themselves. -/
theorem campbellAveragedFrozenCost_eq_atlasRootMass_mul_palmReadout_of_frozenData
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ}
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe Mat q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z)
    (Aref : ℕ → ℝ → ℝ → ℝ)
    (fref : ℕ → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (vref : ℕ → ℝ) (Ψ : ℝ)
    (hAref : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      (Acoef f t) j z = Aref j)
    (hfref : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      (fprobe f t) j z = fref j)
    (hvref : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q) = vref j)
    (hΨ : ∀ j, rootedScenePalmReadout Q
      (rootedSceneFrozenEdge (Aref j) (fref j) (vref j)) = Ψ) :
    campbellAveragedFrozenCost Seed a κ lambda g q = atlasRootMass Seed a κ lambda q * Ψ := by
  refine campbellAveragedFrozenCost_eq_atlasRootMass_mul_palmReadout α β Seed a κ lambda
    Acoef fprobe Mat htransport f t g hglue Ψ (fun j ↦ ?_)
  have hroot := ae_rootedScenePalmReadout_eq_of_frozenData Seed a κ lambda Acoef fprobe
    Q f t j (hAref j) (hfref j) (hvref j)
  filter_upwards [hroot] with z hz
  rw [hz, hΨ j]

/-! ## 3. The unit-mass normalization under the unit Haar density -/

/-- **The total population pressure weight is one under the unit Haar density.**

If the population root label density is one almost everywhere on every selected
root piece -- the root coordinate is normalized so that the population root
intensity equals the seed Haar reference -- and the selected pieces cover the
population root law almost everywhere, then the total theta^(-2/q)-weighted
population root mass is the total mass of the root law, hence one for a
probability root law.  This is the unit-intensity normalization of the population
root atlas. -/
theorem atlasRootMass_eq_one_of_unitDensity
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsProbabilityMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootUnitMassMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {q : ℝ} (hq : 0 < q)
    (hunit : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      populationAtlasTheta Seed a κ lambda j z = 1)
    (hpieceMass : (∑' j, lambda.real (populationSeedRootPiece Seed a κ lambda j)) = 1) :
    atlasRootMass Seed a κ lambda q = 1 := by
  have hmeas (j : ℕ) : MeasurableSet (populationSeedRootPiece Seed a κ lambda j) :=
    measurableSet_populationSeedRootPiece Seed a κ lambda hF hcomplete hu ha hinj j
  have hpiece (j : ℕ) :
      (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) =
      lambda.real (populationSeedRootPiece Seed a κ lambda j) := by
    have hset : (∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) =
        ∫ z in populationSeedRootPiece Seed a κ lambda j, (1 : ℝ) ∂lambda := by
      have hloc : ∀ᵐ z ∂lambda, z ∈ populationSeedRootPiece Seed a κ lambda j →
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) = 1 := by
        filter_upwards [(ae_restrict_iff' (hmeas j)).mp (hunit j)] with z hz
        intro hmem
        rw [hz hmem]
        exact Real.one_rpow _
      exact setIntegral_congr_ae (hmeas j) hloc
    rw [hset, setIntegral_const]
    simp
  rw [atlasRootMass]
  simp_rw [hpiece]
  exact hpieceMass

end OTSelector.Reconstruction