import OTSelector.Reconstruction.FinslerOriginalPopulationGluingIdentity

/-!
# Closing the population gluing identity: the atlas Campbell identification

FinslerOriginalPopulationGluingIdentity.lean reduced the population gluing
identity P1 (PopulationFocalValueLimit) to the single missing equality
AtlasCampbellPressureIdentification: for every probe and tilt the global
weighted stationary pressure equals the frozen population Campbell average of
the atlas-glued per-root weighted stationary pressure root function, equivalently
the frozen lower-pressure readout frozenPressureLower of
FinslerOriginalScenePressureWiring evaluated at the atlas-glued stationary
pressure family.

This module closes that step.  The frozen scene collapse of
FinslerOriginalRootedDataMeasurability.lean, wired in
frozenPressureLower_eq_sceneReadout_of_frozenData, identifies the frozen lower
pressure with the assembled limiting Palm readout Psi from the paper's frozen
scene data: one joint measurability statement for the frozen data, a uniform
probe bound, finite weighted kinetic class of the rooted scene carrier, a.e.
coverage and unit density of the root partition, frozen gluing of the readout
family, and Palm readout constancy.  We instantiate that bridge at the
atlas-glued stationary pressure family (with the population coefficients read as
tilt-independent families) and obtain, from the paper's frozen scene data alone,

  frozenPressureLower Seed a kappa lambda (atlas-glued family) q = Psi.

Hence AtlasCampbellPressureIdentification is equivalent to the single equality

  for all phi t, weightedStationaryPressure alpha beta (Ag phi) (fg phi) t
    = Psi phi t,

the global pressure-readout identification: the weighted stationary pressure
agrees with the assembled limiting Palm readout value.  No sum, integral, piece
decomposition or frozen convolution remains; this residual is one scalar
identity per probe and tilt.

Composing with populationFocalValueLimit_of_atlasCampbellPressureIdentification
gives P1 from the frozen scene data plus that single readout equality, and shows
that, the frozen scene data being given, P1 is *equivalent* to the readout
equality: the sharpest form of the remaining gap.

The frozen scene data are packaged as the structure AtlasFrozenSceneData, so the
single residual is exactly one typed hypothesis.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open OTSelector.PointProcess.StationaryForwardMatching
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
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M}

/-! ## The single residual: the global pressure-readout identification -/

/-- **The global pressure-readout identification.**  The weighted stationary
pressure of the global probe equals the assembled limiting Palm readout Psi at
every probe and tilt.  This is the only remaining equality once the frozen scene
data and the frozen Campbell collapse are granted. -/
def AtlasGlobalPressureReadoutIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Ψ : FinalProbeSpace A B → ℝ → ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    weightedStationaryPressure α β (Ag φ) (fg φ) t = Ψ φ t

/-! ## The frozen scene data of the paper -/

/-- **The paper's frozen scene pressure data.**  This is the hypothesis list of
the frozen scene collapse frozenPressureLower_eq_sceneReadout_of_frozenData
instantiated at the atlas-glued stationary pressure family, together with the
assembled Palm readout Psi and its constancy.  The population coefficients are
read as tilt-independent families, as in the population pressure chain.  No
statement about the global weighted stationary pressure is included: the only
remaining input of P1 is AtlasGlobalPressureReadoutIdentification. -/
structure AtlasFrozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Type _ where
  hq : 2 < q
  hsigma : ∀ j, SigmaFinite (κ j)
  hprob : IsProbabilityMeasure lambda
  hF : F.IsSmoothStronglyConvex
  hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace
  hu : let _instAtlasCampbellMetric : MetricSpace M := F.metricSpace;
    LipschitzWith 1 u
  ha : Measurable a
  hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))
  Q : ProbabilityMeasure
    (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))
  hpalm : IsProbabilityMeasure (rootedScenePhysicalPalm Q)
  hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2
  hData : ∀ (f : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
    Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (coef f j q'.1 q'.2.1.1 q'.2.2.1,
        probeFam f j q'.1 q'.2.1 q'.2.2))
  G : ℝ
  hG : ∀ (f : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
    (x y : MarkedCloudPoint), |probeFam f j z x y| ≤ G
  hMK : ∀ (f : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
    StationaryForwardMatching.FiniteWeightedKinetic (coef f j z)
      (rootedSceneRootCarrier Q hforward)
  hglue : ∀ (f : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q f t z =
        atlasRootFrozenIntegrand ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
          ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
          Seed a κ lambda (fun f' _ j z ↦ coef f' j z)
          (fun f' _ j z ↦ probeFam f' j z)
          (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q t f j z
  hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece Seed a κ lambda j
  hunithaar : ∀ j, ∀ᵐ z ∂lambda.restrict
    (populationSeedRootPiece Seed a κ lambda j),
    populationAtlasTheta Seed a κ lambda j z = 1
  Ψ : FinalProbeSpace A B → ℝ → ℝ
  hconst : ∀ (f : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
    ∀ᵐ w ∂((κ j).restrict
      (populationSeedRootLabelValue (Seed j).seed a ''
        populationSeedRootPiece Seed a κ lambda j)),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge (coef f j (a ((Seed j).seed.curve w 0)))
          (probeFam f j (a ((Seed j).seed.curve w 0)))
          (t * populationAtlasTheta Seed a κ lambda j
            (a ((Seed j).seed.curve w 0)) ^ (2 / q))) = Ψ f t

/-- **The frozen scene collapse at the atlas-glued stationary pressure family.**
From the paper's frozen scene data, the frozen lower-pressure readout of the
atlas-glued stationary pressure family is exactly the assembled limiting Palm
readout Psi.  This is frozenPressureLower_eq_sceneReadout_of_frozenData
instantiated at the atlas-glued family, with the population coefficients read as
tilt-independent families. -/
theorem frozenPressureLower_atlasGlued_eq_sceneReadout
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q) :
    frozenPressureLower (K := A ∪ B) Seed a κ lambda
      (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q) q =
        data.Ψ := by
  haveI : IsProbabilityMeasure lambda := data.hprob
  haveI : ∀ j, SigmaFinite (κ j) := data.hsigma
  haveI : IsProbabilityMeasure (rootedScenePhysicalPalm data.Q) := data.hpalm
  exact frozenPressureLower_eq_sceneReadout_of_frozenData (K := A ∪ B) Seed a κ lambda
    (fun f _ j z ↦ coef f j z) (fun f _ j z ↦ probeFam f j z)
    (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q)
    (q := q) data.hq data.hF data.hcomplete data.hu data.ha data.hinj data.Q
    data.hforward data.hData (G := data.G) data.hG data.hMK data.hglue data.hcover
    data.hunithaar data.Ψ data.hconst

/-! ## The residual reduction with the frozen collapse granted -/

/-- **AtlasCampbellPressureIdentification is equivalent to the single readout
equality** once the frozen descent gives frozenPressureLower = Psi.  No analytic
content: the atlas Campbell identification is exactly the global pressure-readout
identification, because its right side is by construction the frozen lower
pressure readout of the atlas-glued family. -/
theorem atlasCampbellPressureIdentification_iff_globalPressureReadout
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (Ψ : FinalProbeSpace A B → ℝ → ℝ)
    (hread : frozenPressureLower (K := A ∪ B) Seed a κ lambda
      (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q) q = Ψ) :
    AtlasCampbellPressureIdentification Seed a κ lambda α β Ag fg coef probeFam q ↔
      AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg Ψ := by
  constructor
  · intro h φ t
    rw [h φ t]
    exact congrFun (congrFun hread φ) t
  · intro h φ t
    rw [h φ t]
    exact (congrFun (congrFun hread φ) t).symm

/-- **The atlas Campbell identification from the frozen collapse and the readout
identification**, with the frozen descent taken as a hypothesis. -/
theorem atlasCampbellPressureIdentification_of_sceneReadout
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (Ψ : FinalProbeSpace A B → ℝ → ℝ)
    (hread : frozenPressureLower (K := A ∪ B) Seed a κ lambda
      (atlasGluedStationaryPressureFamily Seed a κ lambda α β coef probeFam q) q = Ψ)
    (hglobal : AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg Ψ) :
    AtlasCampbellPressureIdentification Seed a κ lambda α β Ag fg coef probeFam q :=
  (atlasCampbellPressureIdentification_iff_globalPressureReadout Seed a κ lambda α β Ag fg
    coef probeFam q Ψ hread).mpr hglobal

/-- **The atlas Campbell identification from the paper's frozen scene data and
the single readout equality.** -/
theorem atlasCampbellPressureIdentification_of_frozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q)
    (hglobal : AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg
      data.Ψ) :
    AtlasCampbellPressureIdentification Seed a κ lambda α β Ag fg coef probeFam q :=
  atlasCampbellPressureIdentification_of_sceneReadout Seed a κ lambda α β Ag fg coef probeFam
    q data.Ψ (frozenPressureLower_atlasGlued_eq_sceneReadout Seed a κ lambda α β coef probeFam
      q data) hglobal

/-- **P1 from the frozen scene data and the single readout equality.** -/
theorem populationFocalValueLimit_of_frozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q)
    (hglobal : AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg
      data.Ψ) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_atlasCampbellPressureIdentification Seed a κ lambda
    Ag fg α β coef probeFam q data.hF data.hcomplete data.hu data.ha data.hinj
    (atlasCampbellPressureIdentification_of_frozenSceneData Seed a κ lambda α β Ag fg
      coef probeFam q data hglobal)

/-- **The sharpest residual form of P1.**  Given the paper's frozen scene data,
the population gluing identity P1 is equivalent to the single global
pressure-readout identification: the weighted stationary pressure agrees with the
assembled limiting Palm readout Psi at every probe and tilt.  Everything else in
the chain is discharged by the frozen scene collapse. -/
theorem populationFocalValueLimit_iff_globalPressureReadout_of_frozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg data.Ψ := by
  rw [populationFocalValueLimit_iff_atlasCampbellPressureIdentification Seed a κ lambda
    Ag fg α β coef probeFam q data.hF data.hcomplete data.hu data.ha data.hinj]
  exact atlasCampbellPressureIdentification_iff_globalPressureReadout Seed a κ lambda
    α β Ag fg coef probeFam q data.Ψ (frozenPressureLower_atlasGlued_eq_sceneReadout
      Seed a κ lambda α β coef probeFam q data)

end OTSelector.Reconstruction