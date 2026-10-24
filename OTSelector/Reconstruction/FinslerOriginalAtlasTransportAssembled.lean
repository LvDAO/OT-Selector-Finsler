import OTSelector.Reconstruction.FinslerOriginalRootFrozenMeasurability

/-!
# Assembled atlas transport with discharged measurability

This module assembles the measure-theoretic lane of the general Finsler selector.
The atlas bridge collapse campbellAveragedFrozenCost_eq_rootedScenePalmReadout of
FinslerOriginalAtlasSceneBridge.lean carried two analytic side conditions hAmeas
and hRmeas.  They are now discharged by hAmeas_bridge_discharged and
hRmeas_bridge_discharged of FinslerOriginalRootFrozenMeasurability.lean, whose
inputs are root-variable joint measurability of the frozen coefficient and probe
families and root-variable measurability/integrability of the frozen physical
edge functional.

## Contents

* campbellAveragedFrozenCost_eq_rootedScenePalmReadout_assembled: the bridge
  collapse for a root-independent matching, with hAmeas and hRmeas supplied by
  the discharge lemmas (no analytic side condition remains);
* campbellAveragedFrozenCost_eq_palmReadout_of_unitDensity_assembled: the same
  collapse at unit root mass, where the normalisation hypothesis is derived from
  a.e. unit Haar density on the root pieces via atlasRootMass_eq_one, so the
  root-mass condition is unconditional.

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

/-- **Assembled atlas transport theorem.**

The bridge collapse for a matching that does not depend on the root, with the
measurability side conditions hAmeas and hRmeas discharged from root-variable
joint measurability of the frozen coefficient and probe families and from
measurability and integrability of the frozen physical edge functional. -/
theorem campbellAveragedFrozenCost_eq_rootedScenePalmReadout_assembled
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mm : StationaryForwardMatching α β)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasAssembledMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    [SFinite (rootedScenePalmMeasure Q)]
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe
      (fun _ _ _ _ ↦ Mm) q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe
        (fun _ _ _ _ ↦ Mm) q t f j z)
    (hAjoint : ∀ j, Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (Acoef f t) j q'.1 q'.2.1.1 q'.2.2.1))
    (hfpjoint : ∀ j, Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (fprobe f t) j q'.1 q'.2.1 q'.2.2))
    {G : ℝ} (hG : ∀ j z (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hMK : ∀ j z,
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) Mm)
    (hEdge : ∀ j, Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j p.1) ((fprobe f t) j p.1)
        (t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) p.2))
    (hint : ∀ j z, Integrable (fun m : PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) m)
      (rootedScenePalmMeasure Q))
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
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ :=
  campbellAveragedFrozenCost_eq_rootedScenePalmReadout α β Seed a κ lambda Acoef fprobe
    (fun _ _ _ _ ↦ Mm) hq hF hcomplete hu ha hinj htransport f t g hglue
    (fun j ↦ hAmeas_bridge_discharged α β Seed a κ lambda Acoef fprobe Mm
      hF hcomplete hu ha hinj j hq t f (hAjoint j) (hfpjoint j) (hMK j) (hG j))
    (fun j ↦ hRmeas_bridge_discharged Seed a κ lambda Acoef fprobe
      hF hcomplete hu ha hinj j hq t f (hEdge j) (hint j))
    Ψ hconst hnorm

/-- **Assembled atlas transport at unit root mass.**

The assembled collapse with the normalisation hypothesis replaced by the two
concrete unit-density conditions: the root pieces cover lambda almost everywhere
and the pressure weight theta is one almost everywhere on each piece.  The
root-mass normalisation then follows from atlasRootMass_eq_one, so no mass
hypothesis remains. -/
theorem campbellAveragedFrozenCost_eq_palmReadout_of_unitDensity_assembled
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsProbabilityMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mm : StationaryForwardMatching α β)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasAssembledUnitMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    [SFinite (rootedScenePalmMeasure Q)]
    (htransport : RootedSceneAtlasTransport α β Seed a κ lambda Acoef fprobe
      (fun _ _ _ _ ↦ Mm) q Q)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe
        (fun _ _ _ _ ↦ Mm) q t f j z)
    (hAjoint : ∀ j, Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (Acoef f t) j q'.1 q'.2.1.1 q'.2.2.1))
    (hfpjoint : ∀ j, Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (fprobe f t) j q'.1 q'.2.1 q'.2.2))
    {G : ℝ} (hG : ∀ j z (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hMK : ∀ j z,
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) Mm)
    (hEdge : ∀ j, Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j p.1) ((fprobe f t) j p.1)
        (t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) p.2))
    (hint : ∀ j z, Integrable (fun m : PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) m)
      (rootedScenePalmMeasure Q))
    (hcover : ∀ᵐ z ∂lambda,
      z ∈ ⋃ j, populationSeedRootPiece Seed a κ lambda j)
    (hunithaar : ∀ j, ∀ᵐ z ∂lambda.restrict
      (populationSeedRootPiece Seed a κ lambda j),
      populationAtlasTheta Seed a κ lambda j z = 1)
    (Ψ : ℝ)
    (hconst : ∀ j, ∀ᵐ w ∂((κ j).restrict
        (populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j)),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
          ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
          (t * populationAtlasTheta Seed a κ lambda j
            (a ((Seed j).seed.curve w 0)) ^ (2 / q))) = Ψ) :
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ :=
  campbellAveragedFrozenCost_eq_rootedScenePalmReadout_assembled α β Seed a κ lambda
    Acoef fprobe Mm hq hF hcomplete hu ha hinj htransport f t g hglue
    hAjoint hfpjoint hG hMK hEdge hint Ψ hconst
    (by
      have hhaar : atlasHaarMass Seed a κ lambda q = 1 := by
        rw [← atlasRootMass_eq_atlasHaarMass Seed a κ lambda hF hcomplete hu ha hinj hq]
        exact atlasRootMass_eq_one Seed a κ lambda hF hcomplete hu ha hinj
          (by linarith) hcover hunithaar
      exact hhaar)

/-- **Assembled atlas transport in the limiting scene, at unit root mass.**

The final form of the measure-theoretic lane: in the limiting rooted scene the
matching is the root carrier rootedSceneRootCarrier Q hforward, the coefficient
and probe families are jointly measurable in (root, pair), every root coefficient
lies in the finite weighted kinetic class of the carrier, and the frozen physical
edge functional is jointly measurable and pointwise integrable.  Under the
concrete unit-density conditions on the root partition (a.e. cover and pressure
weight one a.e. on each piece) the frozen Campbell cost collapses to the constant
Palm readout. -/
theorem campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_assembled
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsProbabilityMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasSceneMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hAjoint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        (Acoef f t) j q'.1 q'.2.1.1 q'.2.2.1))
    (hfpjoint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        (fprobe f t) j q'.1 q'.2.1 q'.2.2))
    {G : ℝ} (hG : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hMK : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z)
        (rootedSceneRootCarrier Q hforward))
    (hEdge : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
        rootedSceneFrozenEdge ((Acoef f t) j p.1) ((fprobe f t) j p.1)
          (t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) p.2))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      Integrable (fun m : PhysicalPairPalmMark ι ↦
        rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) m)
        (rootedScenePalmMeasure Q))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (g : Z → ℝ)
    (hglue : ∀ j, ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
      g z = atlasRootFrozenIntegrand
        ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
        ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
        Seed a κ lambda Acoef fprobe
        (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q t f j z)
    (hcover : ∀ᵐ z ∂lambda,
      z ∈ ⋃ j, populationSeedRootPiece Seed a κ lambda j)
    (hunithaar : ∀ j, ∀ᵐ z ∂lambda.restrict
      (populationSeedRootPiece Seed a κ lambda j),
      populationAtlasTheta Seed a κ lambda j z = 1)
    (Ψ : ℝ)
    (hconst : ∀ j, ∀ᵐ w ∂((κ j).restrict
        (populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j)),
      rootedScenePalmReadout Q
        (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
          ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
          (t * populationAtlasTheta Seed a κ lambda j
            (a ((Seed j).seed.curve w 0)) ^ (2 / q))) = Ψ) :
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ := by
  haveI : SFinite (rootedScenePalmMeasure Q) := by
    rw [rootedScenePalmMeasure_eq_rootedScenePhysicalPalm (ι := ι)]
    infer_instance
  have hsec : ∀ z : Z, Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
      ((z, p) : Z × (MarkedCloudPoint × MarkedCloudPoint))) :=
    fun z ↦ Measurable.prodMk measurable_const measurable_id
  refine campbellAveragedFrozenCost_eq_palmReadout_of_unitDensity_assembled
    ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
    ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
    Seed a κ lambda Acoef fprobe (rootedSceneRootCarrier Q hforward) hq
    hF hcomplete hu ha hinj
    (rootedSceneAtlasTransport_rootCarrier Seed a κ lambda Acoef fprobe Q hforward
      (fun f' t' j z ↦ (hAjoint f' t' j).comp (hsec z))
      (fun f' t' j z ↦ (hfpjoint f' t' j).comp (hsec z))
      hG
      (fun f' t' j z ↦ integrable_rootedSceneFrozenKinetic Q hforward (hMK f' t' j z)))
    f t g hglue (fun j ↦ hAjoint f t j) (fun j ↦ hfpjoint f t j)
    (fun j z x y ↦ hG f t j z x y)
    (fun j z ↦ hMK f t j z) (fun j ↦ hEdge f t j) (fun j z ↦ hint f t j z)
    hcover hunithaar Ψ hconst

end OTSelector.Reconstruction