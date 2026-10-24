import OTSelector.Reconstruction.FinslerOriginalRootCocycle
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Real-valued tsum conversion, unit root mass and the remaining transport inputs

This module closes the measure-theoretic residual of
FinslerOriginalRootedTransportInputs.lean.

## 1. The real-valued tsum conversion

* tsum_measureReal_eq_measureReal_iUnion: for pairwise disjoint measurable pieces
  of finite total measure, the real-valued sum of their masses is the real mass of
  their union.  This is the real-valued form of countable additivity obtained from
  the extended nonnegative tsum through ENNReal.tsum_toReal_eq;
* measureReal_iUnion_eq_one: if the pieces cover a probability measure almost
  everywhere, the real mass of their union is one.

## 2. The unit mass of the population root atlas, unconditionally

* setIntegral_theta_eq_measureReal_of_unitDensity: on a piece of unit Haar
  density the theta-weighted root integral is the real mass of the piece;
* atlasRootMass_eq_one: from a.e. coverage by the selected pieces and unit Haar
  density on each piece, the total population pressure weight is one.  No
  piece-mass normalization is assumed.

## 3. The integrability input hIntK

* integrable_rootedSceneFrozenKinetic: the frozen kinetic edge cost is integrable
  against the limiting Palm law as soon as the root carrier lies in the paper's
  finite-weighted-kinetic class C_w.  The transfer uses the recoding of physical
  Palm pairs and the integrability-along-a-measurable-map lemma.

## 4. Measurability of the seed label-root map

* measurableEmbedding_seedLabelRoot: the population root attached to an actual
  seed label embeds the seed labels measurably into the population root space.
  This is the measurability content of the hAmeas/hRmeas side condition: the
  frozen root functionals are functions of the population root, and the seed label
  reference maps measurably and injectively to the root.

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

/-! ## 1. The real-valued tsum conversion -/

/-- **The real-valued tsum conversion for a disjoint measurable family.**

For pairwise disjoint measurable sets of finite total measure, the real-valued sum
of their measures is the real measure of their union.  This is the real-valued
form of countable additivity obtained from the extended nonnegative tsum. -/
theorem tsum_measureReal_eq_measureReal_iUnion
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : ℕ → Set α}
    (hdisj : Pairwise (Disjoint on s)) (hmeas : ∀ j, MeasurableSet (s j))
    (hfin : μ (⋃ j, s j) ≠ (∞ : ℝ≥0∞)) :
    (∑' j, μ.real (s j)) = μ.real (⋃ j, s j) := by
  have hne : ∀ j, μ (s j) ≠ (∞ : ℝ≥0∞) := fun j ↦
    ne_top_of_le_ne_top hfin (measure_mono (Set.subset_iUnion s j))
  simp only [Measure.real_def]
  calc (∑' j, (μ (s j)).toReal) = (∑' j, μ (s j)).toReal :=
        (ENNReal.tsum_toReal_eq hne).symm
    _ = (μ (⋃ j, s j)).toReal := by rw [measure_iUnion hdisj hmeas]

/-- **The real mass of an almost-everywhere cover of a probability measure is
one.** -/
theorem measureReal_iUnion_eq_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {s : ℕ → Set α} (hmeas : ∀ j, MeasurableSet (s j))
    (hcover : ∀ᵐ z ∂μ, z ∈ ⋃ j, s j) :
    μ.real (⋃ j, s j) = 1 := by
  have hcompl : μ ((⋃ j, s j)ᶜ) = 0 := by
    have h := hcover
    rw [ae_iff] at h
    convert h using 2
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
  have hunion : μ (⋃ j, s j) = 1 := by
    have hsplit : μ ((⋃ j, s j) ∪ (⋃ j, s j)ᶜ) =
        μ (⋃ j, s j) + μ ((⋃ j, s j)ᶜ) :=
      measure_union disjoint_compl_right (MeasurableSet.iUnion hmeas).compl
    rw [Set.union_compl_self, measure_univ] at hsplit
    rw [hcompl, add_zero] at hsplit
    exact hsplit.symm
  rw [Measure.real_def, hunion, ENNReal.toReal_one]

/-! ## 2. The unit mass of the population root atlas -/

/-- **On a unit-density piece, the theta-weighted root integral is the real mass
of the piece.** -/
theorem setIntegral_theta_eq_measureReal_of_unitDensity
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootMassUnitMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℝ}
    (hunit : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      populationAtlasTheta Seed a κ lambda j z = 1) :
    (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) =
      lambda.real (populationSeedRootPiece Seed a κ lambda j) := by
  have hmeas : MeasurableSet (populationSeedRootPiece Seed a κ lambda j) :=
    measurableSet_populationSeedRootPiece Seed a κ lambda hF hcomplete hu ha hinj j
  have hset : (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) =
      ∫ z in populationSeedRootPiece Seed a κ lambda j, (1 : ℝ) ∂lambda := by
    have hloc : ∀ᵐ z ∂lambda, z ∈ populationSeedRootPiece Seed a κ lambda j →
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) = 1 := by
      filter_upwards [(ae_restrict_iff' hmeas).mp hunit] with z hz
      intro hmem
      rw [hz hmem]
      exact Real.one_rpow _
    exact setIntegral_congr_ae hmeas hloc
  rw [hset, setIntegral_const]
  simp

/-- **The unit mass of the population root atlas.**

If the selected population seed pieces cover the population root law almost
everywhere and the population root label density is one almost everywhere on every
piece (the root coordinate is normalized so that the population root intensity
equals the seed Haar reference), then the total theta^(-2/q)-weighted population
root mass is one. -/
theorem atlasRootMass_eq_one
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsProbabilityMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootMassOneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {q : ℝ} (hq : 0 < q)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece Seed a κ lambda j)
    (hunit : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      populationAtlasTheta Seed a κ lambda j z = 1) :
    atlasRootMass Seed a κ lambda q = 1 := by
  have hmeas (j : ℕ) : MeasurableSet (populationSeedRootPiece Seed a κ lambda j) :=
    measurableSet_populationSeedRootPiece Seed a κ lambda hF hcomplete hu ha hinj j
  have hdisj : Pairwise (Disjoint on populationSeedRootPiece Seed a κ lambda) :=
    pairwiseDisjoint_populationSeedRootPiece Seed a κ lambda
  have hfin : lambda (⋃ j, populationSeedRootPiece Seed a κ lambda j) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top (by rw [measure_univ]; exact ENNReal.one_ne_top)
      (measure_mono (subset_univ _))
  rw [atlasRootMass]
  simp_rw [setIntegral_theta_eq_measureReal_of_unitDensity Seed a κ lambda
    hF hcomplete hu ha hinj _ (hunit _)]
  rw [tsum_measureReal_eq_measureReal_iUnion hdisj hmeas hfin]
  exact measureReal_iUnion_eq_one hmeas hcover

/-! ## 3. The integrability input of the transport -/

/-- **The frozen kinetic edge cost is integrable against the limiting Palm law,
from finite weighted kinetic mean.**

If the root carrier of the limiting rooted scene lies in the paper's weighted
kinetic class C_w for a measurable coefficient, then the frozen kinetic edge cost
of the physical Palm pair is integrable against the limiting Palm law.  The
transfer goes through the canonical recoding of physical Palm pairs to abstract
marked pairs and the integrability-along-a-measurable-map lemma. -/
theorem integrable_rootedSceneFrozenKinetic
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    {A : ℝ → ℝ → ℝ}
    (hMK : StationaryForwardMatching.FiniteWeightedKinetic A
      (rootedSceneRootCarrier Q hforward)) :
    Integrable (fun m : PhysicalPairPalmMark ι ↦
      (1 / 2 : ℝ) * A m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2)
      (rootedScenePhysicalPalm Q) := by
  have hpalm := rootedSceneRootCarrier_palm Q hforward
  have h1 : Integrable (StationaryForwardMatching.kineticIntegrand A)
      (rootedSceneRecodedPalm Q) := by
    rw [← hpalm]
    exact hMK
  have h2 := h1.comp_measurable (measurable_rootedScenePairRecode (ι := ι))
  refine h2.congr (Filter.Eventually.of_forall (fun m => ?_))
  simp only [Function.comp_apply, StationaryForwardMatching.kineticIntegrand,
    StationaryForwardMatching.edgeDisplacement, rootedScenePairRecode]

/-! ## 4. Measurability of the seed label-root map -/

/-- **The population root attached to an actual seed label is a measurable
embedding of the seed labels into the population root space.**

This is the measurability content of the hAmeas/hRmeas side condition: the frozen
root functionals are functions of the population root, and the seed label
reference maps measurably and injectively to the root. -/
theorem measurableEmbedding_seedLabelRoot
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedLabelRootMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) :
    MeasurableEmbedding
      (fun w : (Seed j).seed.labels ↦ seedLabelRoot Seed a j (w : (Seed j).seed.covector.ker)) :=
  measurableEmbedding_populationSeedLabel (Seed j).seed hF hcomplete hu ha hinj

end OTSelector.Reconstruction