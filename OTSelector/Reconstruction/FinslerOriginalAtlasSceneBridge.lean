import OTSelector.Reconstruction.FinslerPopulationAtlasChangeOfMeasure
import OTSelector.Reconstruction.FinslerCampbellLowerAssembly
import OTSelector.Reconstruction.MarkedStationaryValuePalmScene
import OTSelector.Reconstruction.FinslerSeedRootPartition

/-!
# The atlas-to-physical-scene bridge for the rooted Campbell identification

The lower-pressure lane computes the population Campbell-averaged frozen cost in
the *atlas* language

  campbellAveragedFrozenCost Seed a κ lambda (g f t) q
    = ∑' j, ∫_{piece_j} θ_j(z)^(-2/q) * (g f t) z ∂lambda,

while the limiting rooted scene and its Palm frozen integrand live in the
*physical scene* language,

  rootedScenePalmMeasure Q = cubePalm (physicalScenePairCampbell Q),
  rootedScenePalmReadout Q Φ = ∫ m, Φ m ∂rootedScenePalmMeasure Q.

This module builds the bridge between the two languages.

## What is proved

* atlasPieceIntegral_eq_haarReadout: **the exact atlas change of measure**.  On
  every selected population root piece, the population-weighted frozen root
  integral with weight θ^(-2/q) against the population root law lambda equals its
  Haar-reference integral with weight θ^(1-2/q) against the seed label measure
  κ_j, evaluated at the original seed label root.  This is the measured-atlas
  change of measure of FinslerPopulationAtlasChangeOfMeasure applied to the frozen
  root integrand;
* atlasPieceHaarReadout_eq_of_palmRootIdentification: **the transport step**.
  If, at almost every population root of a piece, the atlas root-family frozen
  integrand equals the limiting rooted scene's physical Palm readout at that root
  (the named statement RootedSceneAtlasTransport), then the Haar-reference label
  integral of the atlas frozen root integrand equals the Haar-reference label
  integral of the physical Palm readout;
* campbellAveragedFrozenCost_eq_rootedScenePalmHaar: **the bridge**.  For any root
  function g that on each piece is the atlas frozen root integrand, the
  θ-weighted Campbell-averaged frozen cost equals the Haar-reference integral of
  the limiting scene's physical Palm readout.  This turns the atlas population
  pressure integrand into a physical Palm average;
* campbellAveragedFrozenCost_eq_rootedScenePalmReadout: **the collapse**.  Under
  the stationary root-independence of the limiting scene's frozen readout and the
  unit-mass normalization of the population root atlas, the θ-weighted
  Campbell-averaged frozen cost equals the single physical Palm integral
  rootedScenePalmReadout Q of the frozen edge functional;
* palmReadout_eq_rootWindowExpectation: the physical Palm readout is the expected
  rooted unit-window empirical frozen core readout of the limiting scene
  (Campbell's formula at the limiting scene law), closing the loop with the
  rooted-scene Campbell identification;
* atlasPiecewiseRoot, atlasPiecewiseRoot_of_mem, ae_atlasPiecewiseRoot_eq,
  campbellAveragedFrozenCost_atlasPiecewiseRoot_eq_tsum: **the piecewise gluing
  of the atlas root family**.  The frozen root function of the lower-pressure
  lane is the first-owner gluing of the atlas frozen root integrand on the
  disjoint population seed pieces, so the gluing hypothesis of the bridge is
  proved, not assumed, for the constructed frozen root function;
* campbellAveragedFrozenCost_piecewise_eq_rootedScenePalmReadout: **the
  end-to-end bridge for the constructed piecewise frozen root function**: under
  the named atlas transport, the stationarity root-independence and the unit-mass
  normalization, its theta-weighted Campbell-averaged frozen cost is the single
  physical Palm integral of the limiting rooted scene.

## What remains an explicit named input

The single named identification is RootedSceneAtlasTransport: at almost every
population root of every selected seed piece, the Palm kinetic-plus-probe moment
of the atlas root family M f t j z is the physical Palm readout of the limiting
rooted scene at that root, i.e. the atlas root family is the root-change-cocycle
transport of the limiting rooted scene.  Everything measure-theoretic downstream
of it (the change of measure, the Haar transport, the collapse and the Campbell
window formula) is proved here.

No sorry, admit or added axiom occurs.
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
/-! ## The frozen edge functional and the physical Palm readout of the limiting scene -/

/-- The zero mark of the abstract marked cloud carrier (the two clocks of a
physical Palm pair are recoded with this mark). -/
def bridgeUnitMarkZero : UnitMark := ⟨0, by norm_num⟩

/-- The frozen edge functional of the limiting rooted scene at one root: the
frozen kinetic cost plus tilt times the frozen probe, evaluated on the physical
Palm pair (both original clocks together with the full transverse displacement). -/
noncomputable def rootedSceneFrozenEdge
    (A : ℝ → ℝ → ℝ) (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) (v : ℝ)
    (m : PhysicalPairPalmMark ι) : ℝ :=
  (1 / 2 : ℝ) * A m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2 +
    v * f (m.1.1, bridgeUnitMarkZero) (m.1.2, bridgeUnitMarkZero)

/-- The Palm measure of the limiting rooted scene: the unit-window cube Palm of
the scene's paired-edge Campbell measure.  This is the Palm law produced by the
limiting-scene construction of FinslerOriginalRootedSceneLimitLaw. -/
noncomputable def rootedScenePalmMeasure
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure (PhysicalPairPalmMark ι) :=
  cubePalm ι (physicalScenePairCampbell
    (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))

/-- The physical Palm readout of the limiting rooted scene: the Palm average of a
physical frozen edge functional.  This is the physical counterpart of the atlas
frozen root integral. -/
noncomputable def rootedScenePalmReadout
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (Φ : PhysicalPairPalmMark ι → ℝ) : ℝ :=
  ∫ m, Φ m ∂rootedScenePalmMeasure Q

/-- The atlas root-family frozen integrand: the Palm kinetic moment plus tilt
times the Palm probe moment of the stationary matching of seed piece j at root z.
This is the atlas-language frozen root integrand of the lower-pressure lane (the
body is the one of rootedFrozenIntegrand of FinslerOriginalRootedCampbellFrozenCore,
repeated here so that this module needs no olean of the rooted-scene limit module). -/
noncomputable def atlasRootFrozenIntegrand
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ) (t : ℝ) (f : (K × K) →ᵇ ℝ) (j : ℕ) (z : Z) : ℝ :=
  StationaryForwardMatching.palmKinetic ((Acoef f t) j z) ((Mat f t) j z) +
    (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
      StationaryForwardMatching.palmProbe ((fprobe f t) j z) ((Mat f t) j z)

/-! ## The atlas change of measure for the frozen root integrand -/

/-- **The population-weighted frozen root integral is the Haar-reference frozen
root integral, on every selected population root piece.**

On the j-th selected population seed piece, the population root law lambda with
the population pressure weight theta^(-2/q) integrates a root function to the
seed Haar label measure kappa_j with the Haar weight theta^(1-2/q), evaluated at
the original seed label root.  This is the measured-atlas change of measure of
FinslerPopulationAtlasChangeOfMeasure applied to an arbitrary root function; the
specialized integrand of the lower-pressure lane is the frozen root integrand. -/
theorem atlasPieceIntegral_eq_haarReadout
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasBridgeMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) [SigmaFinite (κ j)]
    {q : ℝ} (hq : 2 < q) (g : Z → ℝ)
    (hg : AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        g (a ((P j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).map
        (populationSeedRootLabelValue (P j).seed a))) :
    (∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z ∂lambda) =
      ∫ w in populationSeedRootLabelValue (P j).seed a ''
          populationSeedRootPiece P a κ lambda j,
        (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (1 - 2 / q) *
          g (a ((P j).seed.curve w 0)) ∂κ j := by
  have hK := measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j
  have hmain := integral_populationSeedCore_root_pressure_eq_haar P a κ lambda
    hF hcomplete hu ha hinj j hK (subset_rfl) hq (fun z _ ↦ g z) 0 hg
  simpa only [populationAtlasTheta, zero_mul] using hmain
/-! ## The physical Palm readout is the rooted empirical frozen core readout -/

/-- **Campbell's formula at the limiting scene law, for the frozen edge
functional.**

The physical Palm readout of the limiting rooted scene -- a nonnegative measurable
frozen edge functional integrated against the unit-window cube Palm -- is the
expected rooted unit-window empirical frozen core readout of the limiting scene.
The inner integral is one scene's rooted empirical frozen core functional and the
outer integral is over the limiting rooted scene law.  This identifies the
physical Palm integral of the bridge with the empirical frozen core functional. -/
theorem palmReadout_eq_rootWindowExpectation
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {Φ : PhysicalPairPalmMark ι → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ m, Φ m ∂rootedScenePalmMeasure Q) =
      ∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
          e.1.1 ∈ palmUnitCube ι},
        Φ (physicalPairAnchor e).2
        ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :=
  lintegral_cubePalm_physicalScenePairCampbell
    (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) hΦ

/-! ## The named rooted-scene atlas transport -/

/-- **The named atlas-to-physical-scene transport of the root family.**

At almost every population root of every selected seed piece, the atlas
root-family frozen integrand -- the Palm kinetic moment plus tilt times the Palm
probe moment of the stationary matching M f t j z -- is the physical Palm readout
of the limiting rooted scene at that same root, for the frozen edge functional
with the root's calibrated coefficient, probe and signed tilt.  In other words the
atlas root family is the root-change-cocycle transport of the limiting rooted
scene, and the frozen root integrand of the atlas is the Palm frozen integrand of
the limiting scene.  This is the single remaining named identification of the
bridge; every measure-theoretic step downstream of it is proved in this module. -/
def RootedSceneAtlasTransport
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (q : ℝ)
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z =
        rootedScenePalmReadout Q
          (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
            (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)))

/-! ## The transport step to the population Haar label reference -/

/-- **The named rooted-scene identification transported to the seed label
reference.**

If two root functions agree at almost every population root of the j-th seed
piece, then their Haar-reference label integrals with weight theta^(1-2/q) agree.
Both sides are put in the Haar label reference by the atlas change of measure: the
population-weighted lambda integral of each function equals its Haar kappa_j
integral, and the two population-weighted integrals agree by the almost
everywhere root identity.  This is the step that turns the root-coordinate
identification RootedSceneAtlasTransport into the label-coordinate statement used
by the population Campbell average. -/
theorem atlasPieceHaarReadout_eq_of_palmRootIdentification
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasBridgeTransportMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) [SigmaFinite (κ j)]
    {q : ℝ} (hq : 2 < q) {A R : Z → ℝ}
    (hA : AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        A (a ((P j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).map
        (populationSeedRootLabelValue (P j).seed a)))
    (hR : AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        R (a ((P j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).map
        (populationSeedRootLabelValue (P j).seed a)))
    (hroot : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j), A z = R z) :
    (∫ w in populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j,
      (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (1 - 2 / q) *
        A (a ((P j).seed.curve w 0)) ∂κ j) =
    ∫ w in populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j,
      (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (1 - 2 / q) *
        R (a ((P j).seed.curve w 0)) ∂κ j := by
  have hAeq := atlasPieceIntegral_eq_haarReadout P a κ lambda hF hcomplete hu ha hinj
    j hq A hA
  have hReq := atlasPieceIntegral_eq_haarReadout P a κ lambda hF hcomplete hu ha hinj
    j hq R hR
  have hmid : (∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * A z ∂lambda) =
      ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * R z ∂lambda := by
    apply integral_congr_ae
    filter_upwards [hroot] with z hz
    rw [hz]
  exact hAeq.symm.trans (hmid.trans hReq)

/-! ## The piecewise gluing of a root family -/

/-- The first-owner gluing of a family of root functions on the disjoint
population seed pieces: at a root owned by piece j the glued function takes the
piece-j member of the family, and zero at roots that no selected piece owns.
This is the atlas counterpart of the piecewise frozen root function of the
rooted-scene limit module. -/
noncomputable def atlasPiecewiseRoot
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (G : ℕ → Z → ℝ) : Z → ℝ := by
  classical
  exact fun z ↦ if h : ∃ j : ℕ, z ∈ populationSeedRootPiece P a κ lambda j then
    G (Classical.choose h) z
  else 0

/-- The owning population seed piece of a root is unique: the selected pieces are
pairwise disjoint. -/
theorem populationSeedRootPieceOwner_unique
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    {z : Z} {i j : ℕ}
    (hi : z ∈ populationSeedRootPiece P a κ lambda i)
    (hj : z ∈ populationSeedRootPiece P a κ lambda j) : i = j :=
  populationSeedRootPiece_index_eq_of_mem P a κ lambda hi hj

/-- On its own piece the glued root function is that piece's family member. -/
theorem atlasPiecewiseRoot_of_mem
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (G : ℕ → Z → ℝ) {j : ℕ} {z : Z}
    (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    atlasPiecewiseRoot P a κ lambda G z = G j z := by
  classical
  have h : ∃ i : ℕ, z ∈ populationSeedRootPiece P a κ lambda i := ⟨j, hz⟩
  have hex : atlasPiecewiseRoot P a κ lambda G z =
      G (Classical.choose h) z := by
    unfold atlasPiecewiseRoot
    rw [dite_eq_left h]
  rw [hex]
  have hch : Classical.choose h = j :=
    populationSeedRootPieceOwner_unique P a κ lambda (Classical.choose_spec h) hz
  rw [hch]

/-- Almost everywhere on every selected piece the glued root function is the
piece's own family member.  This is exactly the gluing hypothesis of the bridge
theorems, so the gluing hypothesis is not an extra input: it holds for the
constructed piecewise frozen root function. -/
theorem ae_atlasPiecewiseRoot_eq
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (G : ℕ → Z → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasBridgeGlueMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      atlasPiecewiseRoot P a κ lambda G z = G j z := by
  filter_upwards [ae_restrict_mem (measurableSet_populationSeedRootPiece P a κ lambda
    hF hcomplete hu ha hinj j)] with z hz
  exact atlasPiecewiseRoot_of_mem P a κ lambda G hz

/-- The atlas Campbell-averaged frozen cost of the glued root function is the sum
of the population-weighted piece integrals of the family members.  This is the
form in which the bridge theorems apply to the constructed piecewise frozen root
function. -/
theorem campbellAveragedFrozenCost_atlasPiecewiseRoot_eq_tsum
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (G : ℕ → Z → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasBridgeGlueTsumMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {q : ℝ} :
    campbellAveragedFrozenCost P a κ lambda (atlasPiecewiseRoot P a κ lambda G) q =
      ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda := by
  rw [campbellAveragedFrozenCost_def]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards [ae_atlasPiecewiseRoot_eq P a κ lambda G hF hcomplete hu ha hinj j]
    with z hz
  rw [hz]

/-! ## The bridge: the atlas Campbell-averaged frozen cost is a Palm average -/

/-- **The atlas-to-physical-scene bridge.**

Let the root function g coincide, on each selected population seed piece, with
that piece's atlas frozen root integrand (this is the piecewise gluing of the
constructed frozen root function).  If the atlas root family is the transport of
the limiting rooted scene (the named statement RootedSceneAtlasTransport), then
the theta-weighted Campbell-averaged frozen cost of g equals the Haar-reference
integral, with weight theta^(1-2/q) against the seed label measures, of the
limiting scene's physical Palm readout of the frozen edge functional.

This expresses the population Campbell-averaged frozen cost as a Palm average of
the limiting rooted scene: the atlas lane's pressure integrand and the physical
Palm frozen integrand are the same object in the two languages. -/
theorem campbellAveragedFrozenCost_eq_rootedScenePalmHaar
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasBridgeMainMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe Mat q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z)
    (hAmeas : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j
          (a ((Seed j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)))
    (hRmeas : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        rootedScenePalmReadout Q
          (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
            ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
            (t * populationAtlasTheta Seed a κ lambda j
              (a ((Seed j).seed.curve w 0)) ^ (2 / q))))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a))) :
    campbellAveragedFrozenCost Seed a κ lambda g q =
      ∑' j, ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j,
        (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q) *
          rootedScenePalmReadout Q
            (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
              ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
              (t * populationAtlasTheta Seed a κ lambda j
                (a ((Seed j).seed.curve w 0)) ^ (2 / q))) ∂κ j := by
  rw [campbellAveragedFrozenCost_def]
  refine tsum_congr (fun j ↦ ?_)
  have hstep : (∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g z ∂lambda) =
      ∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z
          ∂lambda := by
    apply integral_congr_ae
    filter_upwards [hglue j] with z hz
    rw [hz]
  rw [hstep, atlasPieceIntegral_eq_haarReadout Seed a κ lambda hF hcomplete hu ha hinj
    j hq (fun z ↦ atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z)
    (hAmeas j)]
  exact atlasPieceHaarReadout_eq_of_palmRootIdentification Seed a κ lambda hF hcomplete hu
    ha hinj j hq (hAmeas j) (hRmeas j) (htransport f t j)

/-! ## The collapse to the single physical Palm integral -/

/-- **The theta-weighted Campbell-averaged frozen cost equals the physical Palm
integral of the limiting rooted scene.**

In addition to the atlas transport, assume the two stationarity/normalization
inputs of the limiting rooted scene: the physical Palm readout of the frozen edge
functional is the same at almost every population root of every piece (root-change
invariance of the limiting stationary scene), and the total mass of the population
root atlas in its Haar reference is one (unit intensity normalization).  Then the
theta-weighted Campbell-averaged frozen cost of the frozen root function equals
the single physical Palm integral Psi of the limiting rooted scene. -/
theorem campbellAveragedFrozenCost_eq_rootedScenePalmReadout
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasBridgeCollapseMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe Mat q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j z)
    (hAmeas : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j
          (a ((Seed j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)))
    (hRmeas : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        rootedScenePalmReadout Q
          (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
            ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
            (t * populationAtlasTheta Seed a κ lambda j
              (a ((Seed j).seed.curve w 0)) ^ (2 / q))))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)))
    (Ψ : ℝ)
    (hconst : ∀ j, ∀ᵐ w ∂((κ j).restrict
        (populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j)),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
          ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
          (t * populationAtlasTheta Seed a κ lambda j
            (a ((Seed j).seed.curve w 0)) ^ (2 / q))) = Ψ)
    (hnorm : (∑' j, ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
        populationSeedRootPiece Seed a κ lambda j,
        (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q)
        ∂κ j) = 1) :
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ := by
  rw [campbellAveragedFrozenCost_eq_rootedScenePalmHaar α β Seed a κ lambda Acoef fprobe
    Mat hq hF hcomplete hu ha hinj htransport f t g hglue hAmeas hRmeas]
  calc (∑' j, ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j,
        (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q) *
          rootedScenePalmReadout Q
            (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
              ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
              (t * populationAtlasTheta Seed a κ lambda j
                (a ((Seed j).seed.curve w 0)) ^ (2 / q))) ∂κ j) =
      ∑' j, ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j,
        (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q) * Ψ
        ∂κ j := by
        apply tsum_congr
        intro j
        apply integral_congr_ae
        filter_upwards [hconst j] with w hw
        rw [hw]
    _ = ∑' j, (∫ w in populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j,
          (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q)
          ∂κ j) * Ψ := by
        apply tsum_congr
        intro j
        exact integral_mul_const Ψ _
    _ = (∑' j, ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j,
          (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q)
          ∂κ j) * Ψ := tsum_mul_right
    _ = Ψ := by rw [hnorm, one_mul]


/-- **The collapse for the constructed piecewise frozen root function.**

The frozen root function of the lower-pressure lane is the first-owner gluing of
the atlas root-family frozen integrand.  Hence, under the named atlas transport,
the stationarity root-independence and the unit-mass normalization, its
theta-weighted Campbell-averaged frozen cost is the single physical Palm integral
of the limiting rooted scene.  This is the end-to-end form of the bridge: it
applies to the actual constructed frozen root function, since the gluing
hypothesis is proved by ae_atlasPiecewiseRoot_eq. -/
theorem campbellAveragedFrozenCost_piecewise_eq_rootedScenePalmReadout
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasBridgePiecewiseMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe Mat q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (hAmeas : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j
          (a ((Seed j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)))
    (hRmeas : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        rootedScenePalmReadout Q
          (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
            ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
            (t * populationAtlasTheta Seed a κ lambda j
              (a ((Seed j).seed.curve w 0)) ^ (2 / q))))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)))
    (Ψ : ℝ)
    (hconst : ∀ j, ∀ᵐ w ∂((κ j).restrict
        (populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j)),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
          ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
          (t * populationAtlasTheta Seed a κ lambda j
            (a ((Seed j).seed.curve w 0)) ^ (2 / q))) = Ψ)
    (hnorm : (∑' j, ∫ w in populationSeedRootLabelValue (Seed j).seed a ''
        populationSeedRootPiece Seed a κ lambda j,
        (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (1 - 2 / q)
        ∂κ j) = 1) :
    campbellAveragedFrozenCost Seed a κ lambda
      (atlasPiecewiseRoot Seed a κ lambda
        (fun j z ↦ atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat
          q t f j z)) q = Ψ :=
  campbellAveragedFrozenCost_eq_rootedScenePalmReadout α β Seed a κ lambda Acoef fprobe
    Mat hq hF hcomplete hu ha hinj htransport f t _
    (fun j ↦ ae_atlasPiecewiseRoot_eq Seed a κ lambda
      (fun j z ↦ atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat
        q t f j z) hF hcomplete hu ha hinj j)
    hAmeas hRmeas Ψ hconst hnorm

end OTSelector.Reconstruction