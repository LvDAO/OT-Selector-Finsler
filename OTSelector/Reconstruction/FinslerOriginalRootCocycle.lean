import OTSelector.Reconstruction.FinslerOriginalRootedSceneLimitLaw
import OTSelector.Reconstruction.FinslerOriginalAtlasSceneBridge

/-!
# The root-coordinate cocycle and the atlas transport of the limiting rooted scene

This module closes the named bridge input RootedSceneAtlasTransport of
OTSelector/Reconstruction/FinslerOriginalAtlasSceneBridge.lean: it constructs the
atlas root family from the limiting rooted scene through the root-change cocycle,
and then proves the stationarity/normalization consequences needed by the
lower-pressure lane.

## 1. The root-coordinate cocycle

* seedLabelRoot: the population root attached to a seed label of the j-th
  calibrated window, i.e. the image of the original seed curve under the label map;
* seedLabelRoot_populationSeedRootLabelValue: **the root-change cocycle**.  On
  every selected population root piece, reading the seed label of a population
  root and then attaching the seed curve at time zero returns the original
  population root.  This is the exact root-coordinate cocycle between the atlas
  root space and the physical Haar root of the scene.

## 2. Construction of the atlas root family from the limiting rooted scene

* rootedSceneRootCarrier: the stationary forward matching carrier whose Palm law
  is the recoded Palm law of the limiting rooted scene (constructed from the
  connected scene law by exists_stationaryForwardMatching_of_iidScene);
* atlasRootFrozenIntegrand_rootCarrier: the Palm kinetic-plus-probe moment of the
  constructed carrier is the physical Palm readout of the limiting rooted scene at
  the same root;
* rootedSceneAtlasTransport_rootCarrier: **RootedSceneAtlasTransport, proved**
  for the canonical recoded mark laws.  The atlas root family is the root-change
  transport of the limiting rooted scene: the abstract Palm moments of the
  constructed carrier equal the physical Palm readout of the limiting scene at
  every population root;
* rootedSceneAtlasTransport_of_markLaws: the same for arbitrary mark laws equal
  to the recoded Palm mark marginals.

## 3. Stationarity and normalization

* measurable_ennreal_toReal_rpow_neg: the negative density power is measurable
  (the single analytic point needed by the atlas change of measure);
* atlasRootMass, atlasHaarMass, atlasRootMass_eq_atlasHaarMass: the total
  population pressure weight of the root atlas equals its Haar-reference total
  mass sum_j int theta^(1-2/q) dkappa_j;
* ae_rootedScenePalmReadout_eq_of_frozenData: root-change invariance of the
  limiting stationary scene: once the frozen coefficient, probe and tilt data are
  root-independent almost everywhere on a piece, the physical Palm readout of the
  frozen edge functional is root-independent there;
* campbellAveragedFrozenCost_eq_tsum_mass_mul_palmReadout: **the collapse**: the
  theta-weighted Campbell-averaged frozen cost is the mass-weighted sum of the
  per-piece physical Palm readouts of the limiting rooted scene;
* campbellAveragedFrozenCost_eq_atlasRootMass_mul_palmReadout and
  campbellAveragedFrozenCost_eq_palmReadout_of_unitMass: the common-readout collapse
  and its unit-mass normalized form;
* campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit: **the end-to-end
  form**, with the transport instantiated at the constructed root carrier of the
  limiting rooted scene.

## What remains

The remaining inputs are explicit: the a.e. root-independence of the frozen
coefficient/probe/tilt data on each population root piece (the frozen data of the
lower-pressure lane), the unit-mass normalization of the population root atlas
(atlasRootMass = 1, equivalently atlasHaarMass = 1), and the measurability of the
frozen root functional in the population label reference (the hAmeas/hRmeas side
conditions of the bridge).  No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

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

/-! ## 1. The root-coordinate cocycle -/

/-- The population root attached to a seed label of the j-th calibrated window:
the image under the label map of the original seed curve at time zero. -/
noncomputable def seedLabelRoot (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (j : ℕ) (w : (Seed j).seed.covector.ker) : Z :=
  a ((Seed j).seed.curve w 0)

/-- **The root-change cocycle.**

On every selected population root piece, reading the seed label of a population
root and then attaching the seed curve at time zero returns the original
population root.  This is the exact inverse cocycle between the population root
space and the seed Haar label reference. -/
theorem seedLabelRoot_populationSeedRootLabelValue
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootCocycleMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {z : Z} (hz : z ∈ populationSeedRootPiece Seed a κ lambda j) :
    seedLabelRoot Seed a j
      (populationSeedRootLabelValue (Seed j).seed a z) = z := by
  rw [seedLabelRoot,
    populationSeedRootLabelValue_on_piece (a := a) (P := Seed) (κ := κ) (lambda := lambda)
      hF hcomplete hu ha hinj j ⟨z, hz⟩]
  exact populationSeedPieceLabel_root Seed a κ lambda j ⟨z, hz⟩

/-- The zero mark of the bridge and the zero mark of the carrier agree; this
identifies the two recodings of a physical Palm pair. -/
theorem bridgeUnitMarkZero_eq_carrierUnitMarkZero :
    bridgeUnitMarkZero = carrierUnitMarkZero :=
  Subtype.ext rfl

/-! ## 2. Construction of the atlas root family from the limiting rooted scene -/

/-- The stationary forward matching carrier of the limiting rooted scene: its
Palm law is the recoded Palm law of the limiting scene.  This is the carrier
constructed by exists_stationaryForwardMatching_of_iidScene, with the Palm law
kept instead of erased. -/
noncomputable def rootedSceneRootCarrier
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2) :
    StationaryForwardMatching
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2)) :=
  (exists_stationaryForwardMatching_of_iidScene Q hforward).choose

/-- The constructed root carrier has exactly the recoded Palm law of the limiting
rooted scene. -/
theorem rootedSceneRootCarrier_palm
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2) :
    (rootedSceneRootCarrier Q hforward).palm = rootedSceneRecodedPalm Q :=
  (exists_stationaryForwardMatching_of_iidScene Q hforward).choose_spec

/-- The Palm law of the bridge (the cube Palm of the paired-edge Campbell measure
of the limiting scene) is the Palm measure of the rooted-scene limit law.  The two
modules describe the same object. -/
theorem rootedScenePalmMeasure_eq_rootedScenePhysicalPalm
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    rootedScenePalmMeasure Q = rootedScenePhysicalPalm Q := rfl

/-- **The atlas root family frozen integrand is the physical Palm readout of the
limiting rooted scene at the same root.**

At every population root, the Palm kinetic-plus-probe moment of the constructed
root carrier is the physical Palm readout of the frozen edge functional of the
limiting rooted scene with the same calibrated coefficient, probe and signed
tilt.  This is the pointwise form of the atlas transport. -/
theorem atlasRootFrozenIntegrand_rootCarrier
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ}
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hA : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (Acoef f t) j z p.1.1 p.2.1))
    (hf : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (fprobe f t) j z p.1 p.2))
    {G : ℝ} (hG : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hIntK : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Integrable (fun m : PhysicalPairPalmMark ι ↦
        (1 / 2 : ℝ) * (Acoef f t) j z m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2)
        (rootedScenePhysicalPalm Q))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z) :
    atlasRootFrozenIntegrand
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
      Seed a κ lambda Acoef fprobe
      (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q t f j z =
    rootedScenePalmReadout Q
      (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) := by
  have hpalm := rootedSceneRootCarrier_palm Q hforward
  rw [atlasRootFrozenIntegrand,
    palmFrozenIntegrand_eq_rootedSceneReadout Q (hA f t j z) (hf f t j z) hpalm]
  simp only [rootedScenePalmReadout, rootedSceneFrozenEdge,
    rootedScenePalmMeasure_eq_rootedScenePhysicalPalm,
    bridgeUnitMarkZero_eq_carrierUnitMarkZero]
  have hintp : Integrable
      (fun m : PhysicalPairPalmMark ι ↦
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
          (fprobe f t) j z (m.1.1, carrierUnitMarkZero) (m.1.2, carrierUnitMarkZero))
      (rootedScenePhysicalPalm Q) := by
    haveI : IsFiniteMeasure (rootedScenePhysicalPalm Q) := inferInstance
    refine Integrable.of_bound ?_
      (|t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)| * |G|) ?_
    · have hrec : Measurable (fun m : PhysicalPairPalmMark ι ↦
          ((m.1.1, carrierUnitMarkZero), (m.1.2, carrierUnitMarkZero))) :=
        (measurable_fst.fst.prodMk measurable_const).prodMk
          (measurable_fst.snd.prodMk measurable_const)
      exact (((hf f t j z).comp hrec).const_mul _).aestronglyMeasurable
    · filter_upwards with m
      have hG0 : 0 ≤ G :=
        le_trans (abs_nonneg (fprobe f t j z (0, carrierUnitMarkZero) (0, carrierUnitMarkZero)))
          (hG f t j z (0, carrierUnitMarkZero) (0, carrierUnitMarkZero))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hG0]
      exact mul_le_mul_of_nonneg_left (hG f t j z _ _) (abs_nonneg _)
  rw [integral_add (hIntK f t j z) hintp, integral_const_mul]

/-- **RootedSceneAtlasTransport, proved for the canonical recoded mark laws.**

The atlas root family of the lower-pressure lane is the root-change transport of
the limiting rooted scene: with the root carrier of the limiting scene, the atlas
frozen root integrand equals the physical Palm readout of the limiting rooted
scene at every population root.  This discharges the named bridge input of
FinslerOriginalAtlasSceneBridge. -/
theorem rootedSceneAtlasTransport_rootCarrier
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ}
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hA : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (Acoef f t) j z p.1.1 p.2.1))
    (hf : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (fprobe f t) j z p.1 p.2))
    {G : ℝ} (hG : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hIntK : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Integrable (fun m : PhysicalPairPalmMark ι ↦
        (1 / 2 : ℝ) * (Acoef f t) j z m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2)
        (rootedScenePhysicalPalm Q)) :
    RootedSceneAtlasTransport
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
      ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
      Seed a κ lambda Acoef fprobe
      (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q Q := by
  intro f t j
  filter_upwards with z
  exact atlasRootFrozenIntegrand_rootCarrier Seed a κ lambda Acoef fprobe Q hforward
    hA hf hG hIntK f t j z

/-- **The transport for arbitrary mark laws.**

If the source and target mark laws are the recoded Palm mark marginals of the
limiting rooted scene, the transport holds for the corresponding carrier. -/
theorem rootedSceneAtlasTransport_of_markLaws
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ}
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hα : α = (rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
    (hβ : β = (rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
    (hA : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (Acoef f t) j z p.1.1 p.2.1))
    (hf : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (fprobe f t) j z p.1 p.2))
    {G : ℝ} (hG : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hIntK : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Integrable (fun m : PhysicalPairPalmMark ι ↦
        (1 / 2 : ℝ) * (Acoef f t) j z m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2)
        (rootedScenePhysicalPalm Q)) :
    RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe
      (fun _ _ _ _ ↦ hα.symm ▸ hβ.symm ▸ rootedSceneRootCarrier Q hforward) q Q := by
  cases hα
  cases hβ
  exact rootedSceneAtlasTransport_rootCarrier Seed a κ lambda Acoef fprobe Q hforward
    hA hf hG hIntK


/-! ## 3. Stationarity and normalization of the population root atlas -/

/-- The negative power of a measurable extended nonnegative density is measurable
as a real function.  This is the single analytic point needed by the atlas change
of measure for the Haar weight theta^(1-2/q). -/
theorem measurable_ennreal_toReal_rpow_neg {Ω : Type*} [MeasurableSpace Ω]
    {d : Ω → ℝ≥0∞} (hd : Measurable d) {q : ℝ} (hq : 0 < q) :
    Measurable (fun w ↦ (d w).toReal ^ (-2 / q)) := by
  have hpos : Measurable (fun w ↦ (d w).toReal ^ (2 / q)) :=
    (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 2 / q)).measurable.comp
      hd.ennreal_toReal
  have hEq : (fun w ↦ (d w).toReal ^ (-2 / q)) =
      fun w ↦ ((d w).toReal ^ (2 / q))⁻¹ := by
    funext w
    have h : (-2 / q : ℝ) = -(2 / q) := by ring
    rw [h]
    exact Real.rpow_neg ENNReal.toReal_nonneg (2 / q)
  rw [hEq]
  exact hpos.inv

/-- **The population pressure weight of one root piece is its Haar mass.**

The theta^(-2/q)-weighted population root mass of one selected seed piece equals
its theta^(1-2/q)-weighted Haar-reference label mass.  This is the change of
measure of the bridge applied to the constant root function, and it is the
normalization identity of the population root atlas. -/
theorem atlasPieceMass_eq_haarMass
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootMassMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) [SigmaFinite (κ j)]
    {q : ℝ} (hq : 2 < q) :
    (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) =
      ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j,
        (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q) ∂κ j := by
  have hq0 : 0 < q := by linarith
  have hg : AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) * (1 : ℝ))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)) := by
    have hmeas := measurable_ennreal_toReal_rpow_neg
      (measurable_populationSeedPieceHaarDensity Seed a κ lambda hF hcomplete hu ha hinj j) hq0
    simpa only [mul_one] using hmeas.aestronglyMeasurable
  have hmain := atlasPieceIntegral_eq_haarReadout Seed a κ lambda hF hcomplete hu ha hinj
    j hq (fun _ ↦ 1) hg
  simpa using hmain

/-- The total population pressure weight of the population root atlas:
sum_j int over piece_j of theta_j^(-2/q) against the population root law. -/
noncomputable def atlasRootMass
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (q : ℝ) : ℝ :=
  ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
    populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda

/-- The total Haar-reference mass of the population root atlas:
sum_j int over the label image of piece_j of theta_j^(1-2/q) against kappa_j. -/
noncomputable def atlasHaarMass
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (q : ℝ) : ℝ :=
  ∑' j, ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
      populationSeedRootPiece Seed a κ lambda j,
    (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q) ∂κ j

/-- **The normalization identification of the population root atlas.**

The total population pressure weight equals the Haar-reference total mass.  The
remaining normalization input is the unit value of this common total mass. -/
theorem atlasRootMass_eq_atlasHaarMass
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootMassEqMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {q : ℝ} (hq : 2 < q) :
    atlasRootMass Seed a κ lambda q = atlasHaarMass Seed a κ lambda q := by
  rw [atlasRootMass, atlasHaarMass]
  exact tsum_congr (fun j ↦
    atlasPieceMass_eq_haarMass Seed a κ lambda hF hcomplete hu ha hinj j hq)

/-- **Root-change invariance of the limiting rooted scene readout.**

Once the frozen calibrated coefficient, probe and signed tilt data are
root-independent almost everywhere on a population root piece, the physical Palm
readout of the frozen edge functional of the limiting rooted scene is
root-independent there.  This is the stationarity input of the lower-pressure
lane: the Palm law of the limiting scene does not see the root, so only the
frozen root data can vary with it. -/
theorem ae_rootedScenePalmReadout_eq_of_frozenData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ}
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ)
    {Aref : ℝ → ℝ → ℝ}
    {fref : MarkedCloudPoint → MarkedCloudPoint → ℝ} {vref : ℝ}
    (hAref : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      (Acoef f t) j z = Aref)
    (hfref : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      (fprobe f t) j z = fref)
    (hvref : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q) = vref) :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) =
        rootedScenePalmReadout Q (rootedSceneFrozenEdge Aref fref vref) := by
  filter_upwards [hAref, hfref, hvref] with z h1 h2 h3
  rw [h1, h2, h3]

/-! ## 4. The collapse to the physical Palm integral -/

/-- **The theta-weighted Campbell-averaged frozen cost is a mass-weighted sum of
the physical Palm readouts of the limiting rooted scene.**

For a frozen root function g that is glued to the atlas frozen root integrand on
each selected population root piece, and whose per-piece physical Palm readouts of
the limiting rooted scene are the constants Psi j almost everywhere, the
theta-weighted Campbell-averaged frozen cost is the population root weight of each
piece times that piece's Palm readout.  The readout constancy is supplied by
stationarity of the limiting scene together with
ae_rootedScenePalmReadout_eq_of_frozenData. -/
theorem campbellAveragedFrozenCost_eq_tsum_mass_mul_palmReadout
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
    (Ψ : ℕ → ℝ)
    (hconst : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) = Ψ j) :
    campbellAveragedFrozenCost Seed a κ lambda g q =
      ∑' j, (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) * Ψ j := by
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
    _ = ∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * Ψ j ∂lambda := by
        apply integral_congr_ae
        filter_upwards [hconst j] with z hz
        rw [hz]
    _ = (∫ z in populationSeedRootPiece Seed a κ lambda j,
          populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) ∂lambda) * Ψ j :=
        integral_mul_const _ _

/-- **The collapse to a single physical Palm integral (mass form).**

If, in addition, the physical Palm readout of the limiting rooted scene is the
same constant Psi at almost every population root of every piece, then the
theta-weighted Campbell-averaged frozen cost is the total population root mass
times Psi. -/
theorem campbellAveragedFrozenCost_eq_atlasRootMass_mul_palmReadout
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
    (Ψ : ℝ)
    (hconst : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) = Ψ) :
    campbellAveragedFrozenCost Seed a κ lambda g q = atlasRootMass Seed a κ lambda q * Ψ := by
  rw [campbellAveragedFrozenCost_eq_tsum_mass_mul_palmReadout α β Seed a κ lambda
    Acoef fprobe Mat htransport f t g hglue (fun _ ↦ Ψ) (fun j ↦ hconst j)]
  rw [atlasRootMass]
  exact tsum_mul_right

/-- **The theta-weighted Campbell-averaged frozen cost equals the physical Palm
integral of the limiting rooted scene (unit-mass normalization).**

This is the target form of the bridge: under the atlas transport, the a.e. root
constancy of the frozen root data together with the unit-mass normalization
atlasRootMass = 1 (equivalently atlasHaarMass = 1 by
atlasRootMass_eq_atlasHaarMass), the population Campbell-averaged frozen cost is
the single physical Palm integral of the frozen edge functional of the limiting
rooted scene. -/
theorem campbellAveragedFrozenCost_eq_palmReadout_of_unitMass
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
    (Ψ : ℝ)
    (hconst : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) = Ψ)
    (hunit : atlasRootMass Seed a κ lambda q = 1) :
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ := by
  rw [campbellAveragedFrozenCost_eq_atlasRootMass_mul_palmReadout α β Seed a κ lambda
    Acoef fprobe Mat htransport f t g hglue Ψ hconst, hunit, one_mul]


/-- **End-to-end: the population Campbell-averaged frozen cost of the constructed
root carrier is the physical Palm integral of the limiting rooted scene.**

The transport of this module is instantiated at the constructed root carrier of
the limiting rooted scene, so no transport hypothesis remains: under the a.e. root
constancy of the frozen root data and the unit-mass normalization of the
population root atlas, the theta-weighted Campbell-averaged frozen cost is the
single physical Palm integral of the frozen edge functional. -/
theorem campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ}
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hA : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (Acoef f t) j z p.1.1 p.2.1))
    (hf : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        (fprobe f t) j z p.1 p.2))
    {G : ℝ} (hG : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hIntK : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Integrable (fun m : PhysicalPairPalmMark ι ↦
        (1 / 2 : ℝ) * (Acoef f t) j z m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2)
        (rootedScenePhysicalPalm Q))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand
        ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
        ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
        Seed a κ lambda Acoef fprobe
        (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q t f j z)
    (Ψ : ℝ)
    (hconst : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))) = Ψ)
    (hunit : atlasRootMass Seed a κ lambda q = 1) :
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ :=
  campbellAveragedFrozenCost_eq_palmReadout_of_unitMass
    ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
    ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
    Seed a κ lambda Acoef fprobe
    (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward)
    (rootedSceneAtlasTransport_rootCarrier Seed a κ lambda Acoef fprobe Q hforward
      hA hf hG hIntK) f t g hglue Ψ hconst hunit

end OTSelector.Reconstruction