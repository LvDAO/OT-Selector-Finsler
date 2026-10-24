import OTSelector.Reconstruction.FinslerOriginalRootedCampbellFrozenCore
import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedLimit
import OTSelector.Reconstruction.FinslerOriginalAbstractCarrierConstruction
import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.FinslerSeedRootPartition
import OTSelector.Reconstruction.FinslerOriginalAtlasSceneBridge

/-!
# The limiting rooted scene law and the Palm frozen integrand

This module attacks the construction side of the remaining lower-pressure input
RootedFrozenCampbellIdentification of
OTSelector/Reconstruction/FinslerOriginalRootedCampbellFrozenCore.lean for open
input hprob.

## 1. Conjunct (iii) of RootedFrozenCampbellIdentification is not an analytic gap

The named statement leaves the frozen root integrand g free.  Since the
population seed pieces populationSeedRootPiece form a *measurable disjoint*
partition of the population root space (proved in FinslerSeedRootPartition),
the Palm frozen integrand of the root family of stationary matchings can be
*defined* piece by piece:

* rootedFrozenPieceIntegrand: at each root, the Palm frozen integrand
  rootedFrozenIntegrand of the stationary matching attached to the unique
  population seed piece that owns the root (zero off the partition);
* populationSeedRootPiece_owner_unique: the owning piece is unique;
* rootedFrozenPieceIntegrand_of_mem: on its own piece the piecewise integrand
  *is* that piece's Palm frozen integrand;
* rootedFrozenPieceIntegrand_ae_identification: **conjunct (iii)** of
  RootedFrozenCampbellIdentification for this g, proved;
* rootedFrozenCampbellIdentification_of_meanBound: consequently the whole
  named statement follows from its remaining analytic content
  RootedFrozenCoreMeanBound (the frozen-core LLN, conjunct (v)) together with
  the technical atlas-comparison integrability/boundedness conjunct (vii).

## 2. Construction of the limiting rooted stationary scene from the actual iid data

* iidTwoColorLaw, iidOptimalPlan: the actual two-colour iid product law and
  the actual finite optimal physical plan of the unchanged original sample;
* exists_iid_limiting_rooted_stationary_scene: from the actual iid data one
  common sample subsequence carries the actual Haar-rooted local scene laws to a
  limiting probability law Q which is spatially stationary under every root
  translation, whose paired-edge Campbell measure factorizes as
  volume x cubePalm, and whose Palm unit-window mass and frozen-edge energy are
  bounded by the actual mass and energy constants (no independent limit law,
  tightness bound or stationarity premise is supplied).

## 3. The limiting scene *is* a stationary forward matching, and its Palm frozen
integrand is the physical Palm readout

* rootedScenePhysicalPalm, rootedSceneRecodedPalm: the Palm measure of the
  limiting scene, and its canonical recoding to abstract marked pairs;
* exists_stationaryForwardMatching_of_iidScene: the abstract stationary
  forward matching carrier StationaryForwardMatching whose Palm law is exactly
  the recoded Palm of the limiting scene;
* palmKinetic_rootedScene_of_iidScene, palmProbe_rootedScene_of_iidScene:
  the carrier's Palm kinetic and probe moments are exactly the limiting scene's
  physical Palm averages of the frozen kinetic edge cost and probe;
* palmFrozenIntegrand_eq_rootedSceneReadout: the packaged identification of the
  frozen root integrand (kinetic Palm moment plus tilt times probe Palm moment)
  with the limiting scene's physical Palm average of the frozen edge cost;
* lintegral_palmFrozenReadout_eq_rootWindow: **Campbell's formula at the
  limiting scene law**: the Palm frozen integrand equals the expected rooted
  unit-window empirical frozen core readout of the limiting scene, i.e. the
  identification of the Palm frozen integrand with the (limiting) empirical
  frozen core functional;
* palmFrozenReadout_le_iidEnergyBound: **the Campbell lower comparison along the
  actual iid data**: a uniform bound on the actual expected global frozen edge
  energy of the unchanged finite optimal plans bounds the Palm frozen integrand
  of the limiting rooted scene, i.e. the Palm frozen integrand is at most the
  actual rooted empirical frozen core readout.  The rooted window estimate used
  in the proof is the actual Haar root averaging of the original plan's global
  energy, so no separate Palm energy premise is supplied.

The construction of the limiting rooted stationary scene reuses the existing
Haar-rooted subsequence/stationarity theorem
MarkedStationaryValuePalmRootedLimit.exists_stationary_cubePalm_of_original_finitePlans
(which formalizes main.tex's Proposition general-gluing-weighted-lower, proof at
main.tex:7880-7930, together with the rooted marginal/tail package at
main.tex:8340-8400) applied to the actual iid populations, iid arrays and original
finite optimal plans, rather than reproving it.

## What remains

The construction here identifies the Palm frozen integrand with the *limiting*
empirical frozen core functional.  Two inputs are not manufactured from the
present data and are left explicit:

1. RootedFrozenCoreMeanBound -- the expectation-level frozen-core LLN saying
   that the actual empirical frozen core cost is asymptotically at least the
   Campbell-averaged piecewise Palm frozen integrand plus the probe constant
   (the remaining analytic input of the lower-pressure lane);
2. the atlas bridge identifying the population root family M f t j z with the
   limiting rooted scene transported to the population root z (the root-change
   cocycle between the atlas root space Z and the physical Haar root of the
   scene).  Everything Campbell-theoretic downstream of that bridge is proved
   here.

The paper's endpoint tail estimates (eq:degenerate-scalar-both-tails,
eq:degenerate-scalar-target-ui, main.tex:8357-8375) and its target marginal
formula nu = sum_l E_l delta_(Y_l, b_l) are the data-level inputs of the
legal/rooted lane (MarkedStationaryValueLegal... modules); they enter the
present file only through the explicit energy constant E of
palmFrozenReadout_le_iidEnergyBound and through the forwardness hypothesis of
exists_stationaryForwardMatching_of_iidScene.

No sorry, admit or added axiom occurs.
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

/-! ## Uniqueness of the owning population seed piece -/

/-- **The owning population seed piece of a root is unique.**

The selected seed pieces populationSeedRootPiece Seed a κ lambda j are pairwise
disjoint, so a root that belongs to a piece belongs to no other piece.  This is
what makes the piecewise definition of the frozen root integrand well posed. -/
theorem populationSeedRootPiece_owner_unique
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    {z : Z} {i j : ℕ}
    (hi : z ∈ populationSeedRootPiece Seed a κ lambda i)
    (hj : z ∈ populationSeedRootPiece Seed a κ lambda j) : i = j :=
  populationSeedRootPiece_index_eq_of_mem Seed a κ lambda hi hj

/-! ## The piecewise Palm frozen integrand of the root family -/

/-- **The piecewise frozen root integrand.**

At a population root owned by seed piece j, the Palm frozen integrand
rootedFrozenIntegrand (frozen kinetic Palm moment plus tilt times the frozen
probe Palm moment) of the stationary matching M f t j z; zero at roots that no
selected seed piece owns.  By uniqueness of the owning piece this is a
well-defined function of the root, and on each piece it coincides with that
piece's Palm frozen integrand. -/
noncomputable def rootedFrozenPieceIntegrand
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) (t : ℝ) (f : (K × K) →ᵇ ℝ) : Z → ℝ := by
  classical
  exact fun z ↦ if h : ∃ j : ℕ, z ∈ populationSeedRootPiece Seed a κ lambda j then
    rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f
      (Classical.choose h) z
  else 0

/-- **On its own population seed piece, the piecewise frozen root integrand is
that piece's Palm frozen integrand.** -/
theorem rootedFrozenPieceIntegrand_of_mem
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) (t : ℝ) (f : (K × K) →ᵇ ℝ)
    {j : ℕ} {z : Z} (hz : z ∈ populationSeedRootPiece Seed a κ lambda j) :
    rootedFrozenPieceIntegrand α β Seed a κ lambda Acoef fprobe M q t f z =
      rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f j z := by
  classical
  have h : ∃ j : ℕ, z ∈ populationSeedRootPiece Seed a κ lambda j := ⟨j, hz⟩
  have hex : rootedFrozenPieceIntegrand α β Seed a κ lambda Acoef fprobe M q t f z =
      rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f
        (Classical.choose h) z := by
    unfold rootedFrozenPieceIntegrand
    rw [dite_eq_left h]
  rw [hex]
  have hch : Classical.choose h = j :=
    populationSeedRootPiece_owner_unique Seed a κ lambda (Classical.choose_spec h) hz
  rw [hch]

/-- **Conjunct (iii) of RootedFrozenCampbellIdentification, proved.**

At almost every root of every population seed piece, the piecewise frozen root
integrand equals the Palm frozen integrand rootedFrozenIntegrand of the
stationary matching of that piece.  This is exactly the identification of the
frozen root function g with the Palm frozen integrand of the limiting rooted
scene along the root family, i.e. conjunct (iii) of
RootedFrozenCampbellIdentification, for the constructed g. -/
theorem rootedFrozenPieceIntegrand_ae_identification
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedSceneLimitMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (κ : ∀ j, Measure (Seed j).seed.covector.ker)
    (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
        rootedFrozenPieceIntegrand α β Seed a κ lambda Acoef fprobe M q t f z =
          rootedFrozenIntegrand α β Seed a κ lambda Acoef fprobe M q t f j z := by
  intro f t j
  filter_upwards [ae_restrict_mem (measurableSet_populationSeedRootPiece Seed a κ lambda
    hF hcomplete hu ha hinj j)] with z hz
  exact rootedFrozenPieceIntegrand_of_mem α β Seed a κ lambda Acoef fprobe M q t f hz

/-! ## The remaining analytic input and the assembled named statement -/

/-- **The frozen-core LLN at the piecewise Palm frozen integrand.**

This is the sole remaining analytic content of
RootedFrozenCampbellIdentification once the frozen root integrand is the
piecewise Palm frozen integrand: the expected normalized frozen core cost of the
actual empirical optimal face is asymptotically at least the Campbell-averaged
piecewise Palm frozen integrand plus the probe constant |t| ||f||.  It is the
hypothesis hfrozen_mean of the lower-pressure lane, stated here at the
constructed root function. -/
def RootedFrozenCoreMeanBound
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ)
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
    campbellAveragedFrozenCost Seed a κ lambda
      (rootedFrozenPieceIntegrand α β Seed a κ lambda Acoef fprobe M q t f) q +
        |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n

/-- **RootedFrozenCampbellIdentification from the piecewise frozen root
integrand and the frozen-core LLN.**

Taking the frozen root function g to be the piecewise Palm frozen integrand,
conjunct (iii) of RootedFrozenCampbellIdentification is proved
(rootedFrozenPieceIntegrand_ae_identification), conjuncts (i), (ii) and (iv) are
the explicit matching/probe data, and the remaining conjuncts are the frozen-core
LLN RootedFrozenCoreMeanBound (conjunct (v)) together with the technical
atlas-comparison integrability and boundedness data (conjunct (vii)). -/
theorem rootedFrozenCampbellIdentification_of_meanBound
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootedSceneAssembleMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {q : ℝ}
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hM : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) ((Mat f t) j z))
    (hA : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z) (a b : ℝ),
      0 ≤ (Acoef f t) j z a b)
    (hf : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ (fprobe f t) j z p.1 p.2))
    (hG : ∃ G : ℝ, ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hmean : RootedFrozenCoreMeanBound α β Seed a κ lambda Acoef fprobe Mat q P frozenCost)
    (htail : ∃ (BI Bg : ((K × K) →ᵇ ℝ) → ℝ → ℝ),
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
          (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
            (rootedFrozenPieceIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f) z)
          (populationSeedRootPiece Seed a κ lambda j) lambda) ∧
      (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
        |populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          StationaryForwardMatching.weightedStationaryPressure α β
            ((Acoef f t) j z) ((fprobe f t) j z)
            (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))| ≤ BI f t) ∧
      (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
        |populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          (rootedFrozenPieceIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f) z| ≤
            Bg f t)) :
    RootedFrozenCampbellIdentification α β Seed a κ lambda Acoef fprobe Mat
      (fun f t ↦ rootedFrozenPieceIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f)
      q P frozenCost :=
  ⟨hM, hA, hf, hG,
    fun f t j ↦ rootedFrozenPieceIntegrand_ae_identification hF hcomplete hu ha hinj
      α β Seed κ lambda Acoef fprobe Mat q f t j,
    hmean, htail⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
namespace OTSelector.Reconstruction

open OTSelector.PointProcess

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

/-- The locally finite scene measures carry the Polish vague topology, which
upgrades the product measurability structure to the one required by the weak
topology on probability measures (the same local instance used by
MarkedStationaryValuePalmRootedLimit). -/
local instance rootedSceneLimitLocalPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-! ## The actual two-colour iid data and its finite optimal plans -/

/-- The actual product law of the original two-colour iid experiment at sample
size k+1 in each colour.  Both colours keep their complete original law. -/
noncomputable abbrev iidTwoColorLaw (μ ν : Measure M) (k : ℕ) :
    Measure ((Fin (k+1) → M) × (Fin (k+1) → M)) :=
  (Measure.pi (fun _ : Fin (k+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (k+1) ↦ ν))

/-- The actual finite optimal physical plan of the unchanged original iid sample,
paired by the fixed exact tie rule. -/
noncomputable abbrev iidOptimalPlan (cost : M → M → ℝ) (scale : ℕ → ℝ) (k : ℕ) :
    (Fin (k+1) → M) × (Fin (k+1) → M) → Measure (M × M) :=
  originalIIDOptimalPhysicalPlan (n := k+1) cost (scale k)

/-- **The limiting rooted scene law of the actual iid data is stationary.**

One common sample subsequence of the actual iid experiment carries the actual
Haar-rooted local scene laws of the unchanged optimal physical plans to a
limiting probability law Q on rooted physical scenes.  The limit is spatially
stationary under every root translation, its paired-edge Campbell measure
factorizes as volume times its unit-window cube Palm, the Palm unit-window mass
is bounded by the actual total mass, and the Palm frozen-edge energy is bounded
by the actual rooted energy constant.  No Poisson, stationarity or tightness
premise is supplied: all of them are produced from the actual data. -/
theorem exists_iid_limiting_rooted_stationary_scene
    (hq : 0 < Fintype.card ι)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℕ → ℝ)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ k, 0 < N k) (hlarge : Tendsto N atTop atTop)
    (f : PhysicalPairPalmMark ι → ℝ) (hf : Continuous f) (hf0 : ∀ m, 0 ≤ f m)
    {E : ℝ≥0∞}
    (henergy : ∀ k, (∫⁻ w : (Fin (k+1) → M) × (Fin (k+1) → M),
        ∫⁻ p : M × M, ENNReal.ofReal (f ((u p.1, u p.2), coord k p.2 - coord k p.1))
          ∂iidOptimalPlan cost scale k w ∂iidTwoColorLaw μ ν k) ≤ E) :
    ∃ Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ physicalSceneRootedLocalSceneLaw (iidTwoColorLaw μ ν (φ k))
        (iidOptimalPlan cost scale (φ k)) (iidOptimalPlan cost scale (φ k))
        (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
        (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
        (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k))
        (haarRootCube ι (haarRootRadius (Fintype.card ι) (N (φ k))))
        (volume_haarRootCube_radius ι hq (hN (φ k)))) atTop (𝓝 Q) ∧
      (∀ v : ι → ℝ, MeasurePreserving (physicalSceneReroot v)
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ∧
      cubePalm ι (physicalScenePairCampbell
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) univ ≤ 1 ∧
      (∫⁻ m, ENNReal.ofReal (f m) ∂cubePalm ι (physicalScenePairCampbell
        (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))) ≤ E ∧
      physicalScenePairCampbell (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) =
        (volume : Measure (ι → ℝ)).prod (cubePalm ι (physicalScenePairCampbell
          (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))) := by
  haveI : ∀ k, NeZero (k + 1) := fun k ↦ ⟨Nat.succ_ne_zero k⟩
  haveI : ∀ k w, IsFiniteMeasure (iidOptimalPlan cost scale k w) :=
    fun k w ↦ inferInstance
  obtain ⟨Q, φ, hφ, hweak, hstat, hmass, hEn, hcamp⟩ :=
    exists_stationary_cubePalm_of_original_finitePlans (ι := ι) (M := M) hq
      (Ω := fun k ↦ (Fin (k+1) → M) × (Fin (k+1) → M))
      (P := fun k ↦ iidTwoColorLaw μ ν k)
      (Γ := fun k ↦ iidOptimalPlan cost scale k)
      (fun k ↦ measurable_originalIIDOptimalPhysicalPlan (n := k+1) cost hcost (scale k))
      coord hcoord u hu N hN hlarge 1 (by norm_num) (fun k ↦ by simp) f hf hf0 E henergy
  exact ⟨Q, φ, hφ, hweak, hstat, hmass, hEn, hcamp⟩

/-! ## The Palm measure of the limiting rooted scene and its carrier -/

/-- The Palm measure of the limiting rooted scene: the unit-window cube Palm of
the scene's paired-edge Campbell measure.  This is the full-dimensional
paired-mark Palm law of the limiting scene. -/
noncomputable def rootedScenePhysicalPalm
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure (PhysicalPairPalmMark ι) :=
  cubePalm ι (physicalScenePairCampbell
    (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))

/-- Canonical recoding of a physical Palm pair (both clocks together with the full
transverse displacement) to the abstract marked pair of the stationary pressure
carrier. -/
def rootedScenePairRecode (m : PhysicalPairPalmMark ι) :
    MarkedCloudPoint × MarkedCloudPoint :=
  ((m.1.1, carrierUnitMarkZero), (m.1.2, carrierUnitMarkZero))

theorem measurable_rootedScenePairRecode :
    Measurable (rootedScenePairRecode (ι := ι)) :=
  (measurable_fst.fst.prodMk measurable_const).prodMk
    (measurable_fst.snd.prodMk measurable_const)

/-- The recoded Palm law of the limiting rooted scene, i.e. the Palm law of the
stationary forward matching carrier. -/
noncomputable def rootedSceneRecodedPalm
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure (MarkedCloudPoint × MarkedCloudPoint) :=
  (rootedScenePhysicalPalm Q).map (rootedScenePairRecode (ι := ι))

/-- **The limiting rooted scene is a stationary forward matching.**

The recoded Palm law of the limiting stationary rooted scene is the Palm law of an
actual stationary forward matching carrier, provided the actual optimal plans are
forward (source clock below target clock) almost everywhere.  The carrier's
Campbell, intensity and mark-marginal data are the explicit carrier fields; the
pressure functionals only use its Palm law, which is the limiting scene's Palm
law by construction. -/
theorem exists_stationaryForwardMatching_of_iidScene
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2) :
    ∃ Mat : StationaryForwardMatching
        ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
        ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2)),
      Mat.palm = rootedSceneRecodedPalm Q := by
  haveI : IsProbabilityMeasure (rootedSceneRecodedPalm Q) :=
    Measure.isProbabilityMeasure_map (measurable_rootedScenePairRecode (ι := ι)).aemeasurable
  have hfw : ∀ᵐ p ∂rootedSceneRecodedPalm Q, p.1.1 < p.2.1 := by
    have hp : MeasurableSet {p : MarkedCloudPoint × MarkedCloudPoint | p.1.1 < p.2.1} :=
      measurableSet_lt (measurable_fst.comp measurable_fst)
        (measurable_fst.comp measurable_snd)
    rw [rootedSceneRecodedPalm,
      ae_map_iff (measurable_rootedScenePairRecode (ι := ι)).aemeasurable hp]
    filter_upwards [hforward] with m hm
    exact hm
  exact exists_stationaryForwardMatching_of_palm (rootedSceneRecodedPalm Q) hfw

/-- **The Palm kinetic moment of the carrier is the limiting scene's physical Palm
frozen kinetic cost.** -/
theorem palmKinetic_rootedScene_of_iidScene
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    {A : ℝ → ℝ → ℝ}
    (hA : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A p.1.1 p.2.1))
    {Mat : StationaryForwardMatching
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))}
    (hMpalm : Mat.palm = rootedSceneRecodedPalm Q) :
    StationaryForwardMatching.palmKinetic A Mat =
      ∫ m, (1 / 2 : ℝ) * A m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2
        ∂rootedScenePhysicalPalm Q := by
  have hkin : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
      StationaryForwardMatching.kineticIntegrand A p) := by
    unfold StationaryForwardMatching.kineticIntegrand StationaryForwardMatching.edgeDisplacement
    exact (hA.const_mul (1 / 2 : ℝ)).mul
      ((measurable_snd.fst.sub measurable_fst.fst).pow_const 2)
  rw [StationaryForwardMatching.palmKinetic, hMpalm, rootedSceneRecodedPalm,
    integral_map (measurable_rootedScenePairRecode (ι := ι)).aemeasurable
      hkin.aestronglyMeasurable]
  congr 1

/-- **The Palm probe moment of the carrier is the limiting scene's physical Palm
frozen probe cost.** -/
theorem palmProbe_rootedScene_of_iidScene
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    {f : MarkedCloudPoint → MarkedCloudPoint → ℝ}
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2))
    {Mat : StationaryForwardMatching
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))}
    (hMpalm : Mat.palm = rootedSceneRecodedPalm Q) :
    StationaryForwardMatching.palmProbe f Mat =
      ∫ m, f (m.1.1, carrierUnitMarkZero) (m.1.2, carrierUnitMarkZero)
        ∂rootedScenePhysicalPalm Q := by
  rw [StationaryForwardMatching.palmProbe, hMpalm, rootedSceneRecodedPalm,
    integral_map (measurable_rootedScenePairRecode (ι := ι)).aemeasurable
      hf.aestronglyMeasurable]
  congr 1

/-- **Campbell's formula at the limiting scene law.**

The Palm frozen integrand of the limiting rooted scene -- a nonnegative measurable
frozen edge functional integrated against the unit-window cube Palm -- equals the
expected rooted unit-window empirical frozen core readout of the limiting scene:
the inner integral is one scene's actual rooted empirical frozen core functional,
and the outer integral is over the limiting rooted scene law.  This is the
identification of the Palm frozen integrand with the (limiting) empirical frozen
core functional. -/
theorem lintegral_palmFrozenReadout_eq_rootWindow
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {Φ : PhysicalPairPalmMark ι → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ m, Φ m ∂rootedScenePhysicalPalm Q) =
      ∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
          e.1.1 ∈ palmUnitCube ι},
        Φ (physicalPairAnchor e).2 ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :=
  palmReadout_eq_rootWindowExpectation Q hΦ


/-- **Packaged Palm frozen integrand identification for the limiting scene.**

At the Palm law of the limiting rooted scene, the frozen root integrand (frozen
kinetic Palm moment plus tilt times the frozen probe Palm moment) is exactly the
limiting scene's physical Palm average of the frozen kinetic edge cost plus tilt
times the frozen probe.  This is the form in which the abstract frozen root
integrand of the lower-pressure lane is identified with the limiting rooted
empirical frozen core functional. -/
theorem palmFrozenIntegrand_eq_rootedSceneReadout
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    {A : ℝ → ℝ → ℝ}
    (hA : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A p.1.1 p.2.1))
    {f : MarkedCloudPoint → MarkedCloudPoint → ℝ}
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2))
    {Mat : StationaryForwardMatching
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))}
    (hMpalm : Mat.palm = rootedSceneRecodedPalm Q) (v : ℝ) :
    StationaryForwardMatching.palmKinetic A Mat +
        v * StationaryForwardMatching.palmProbe f Mat =
      (∫ m, (1 / 2 : ℝ) * A m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2
          ∂rootedScenePhysicalPalm Q) +
        v * ∫ m, f (m.1.1, carrierUnitMarkZero) (m.1.2, carrierUnitMarkZero)
          ∂rootedScenePhysicalPalm Q := by
  rw [palmKinetic_rootedScene_of_iidScene Q hA hMpalm,
    palmProbe_rootedScene_of_iidScene Q hf hMpalm]

/-- **The Palm frozen integrand is dominated by the actual iid frozen energy.**

Along a common subsequence of the unchanged iid experiment, a uniform bound on
the actual expected global frozen edge energy of the original finite optimal
plans bounds the Palm frozen integrand of the limiting rooted scene.  This is the
Campbell lower comparison in the direction required by the lower-pressure lane:
the limiting Palm frozen integrand is at most the actual rooted empirical frozen
core readout of the iid sample.  The rooted window estimate used in the proof is
the actual Haar root averaging of the original plan's global energy, so no
separate Palm energy premise is supplied. -/
theorem palmFrozenReadout_le_iidEnergyBound
    (hq : 0 < Fintype.card ι)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℕ → ℝ)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ k, 0 < N k)
    {f : PhysicalPairPalmMark ι → ℝ} (hf : Continuous f) (hf0 : ∀ m, 0 ≤ f m)
    {E : ℝ≥0∞}
    (hglobal : ∀ n, (∫⁻ w : (Fin (n+1) → M) × (Fin (n+1) → M),
        ∫⁻ p : M × M, ENNReal.ofReal (f ((u p.1, u p.2), coord n p.2 - coord n p.1))
          ∂iidOptimalPlan cost scale n w ∂iidTwoColorLaw μ ν n) ≤ E)
    {Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    {φ : ℕ → ℕ}
    (hweak : Tendsto (fun k ↦ physicalSceneRootedLocalSceneLaw (iidTwoColorLaw μ ν (φ k))
        (iidOptimalPlan cost scale (φ k)) (iidOptimalPlan cost scale (φ k))
        (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
        (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
        (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k))
        (haarRootCube ι (haarRootRadius (Fintype.card ι) (N (φ k))))
        (volume_haarRootCube_radius ι hq (hN (φ k)))) atTop (𝓝 Q)) :
    (∫⁻ m, ENNReal.ofReal (f m) ∂rootedScenePhysicalPalm Q) ≤ E := by
  haveI : ∀ k w, IsFiniteMeasure (iidOptimalPlan cost scale k w) := fun k w ↦ inferInstance
  let Pseq : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :=
    fun k ↦ physicalSceneRootedLocalSceneLaw (iidTwoColorLaw μ ν (φ k))
      (iidOptimalPlan cost scale (φ k)) (iidOptimalPlan cost scale (φ k))
      (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
      (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
      (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k))
      (haarRootCube ι (haarRootRadius (Fintype.card ι) (N (φ k))))
      (volume_haarRootCube_radius ι hq (hN (φ k)))
  have hbound : ∀ (U : Set (ι → ℝ)), IsOpen U → ∀ k,
      (∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
        ENNReal.ofReal (f (physicalPairAnchor e).2)
        ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        ∂(Pseq k : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤
        (volume U) * E := by
    intro U hU k
    have hrooted := lintegral_physicalSceneRootedLocalSceneLaw_sourceEnergy_le
      (iidTwoColorLaw μ ν (φ k)) (iidOptimalPlan cost scale (φ k))
      (iidOptimalPlan cost scale (φ k))
      (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
      (measurable_originalIIDOptimalPhysicalPlan (n := φ k + 1) cost hcost (scale (φ k)))
      (coord (φ k)) (hcoord (φ k)) u hu (N (φ k)) (hN (φ k))
      (haarRootCube ι (haarRootRadius (Fintype.card ι) (N (φ k))))
      (volume_haarRootCube_radius ι hq (hN (φ k)))
      (f := fun m ↦ ENNReal.ofReal (f m))
      (ENNReal.measurable_ofReal.comp hf.measurable) U hU.measurableSet
    exact hrooted.trans (mul_le_mul_of_nonneg_left (hglobal (φ k)) bot_le)
  have hmain := lintegral_cubePalm_le_of_weak_energy_density_bound Pseq hweak f hf hf0 E hbound
  simpa only [rootedScenePhysicalPalm, Pseq] using hmain

end OTSelector.Reconstruction