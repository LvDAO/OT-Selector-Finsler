import OTSelector.Reconstruction.FinslerOriginalRootedEdgeMeasurability

/-!
# Root-variable measurability of the frozen data: one statement suffices

FinslerOriginalRootedEdgeMeasurability.lean reduced the final assembled scene
collapse to four joint-measurability hypotheses on the frozen coefficient Acoef
and the frozen probe fprobe:

* hAjoint and hfpjoint on MarkedCloudPoint pairs (needed by the atlas frozen
  integrand);
* hAphys and hFpphys on PhysicalPairPalmMark pairs (needed by the frozen physical
  edge functional).

All four follow from one paper-level statement: the frozen data
(z, x, y) |-> ((Acoef f t) j z x y, (fprobe f t) j z x y) is jointly measurable in
the root and the marked pair.  The two MarkedCloudPoint hypotheses are its first
and second coordinates; the two physical hypotheses are its pullbacks along the
coordinate map (z, m) |-> (z, rootedScenePairRecode m), which replaces the two
heights of a physical Palm pair by zero-marked carrier points.

## Contents

* measurable_rootedCoefficient_joint_of_frozenData / measurable_rootedProbe_joint_of_frozenData:
  the two MarkedCloudPoint pair hypotheses as coordinates of the single frozen
  data statement;
* measurable_rootedCoefficient_physical_of_frozenData / measurable_rootedProbe_physical_of_frozenData:
  the two physical Palm pair hypotheses, pulled back through rootedScenePairRecode;
* campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_data: the final
  assembled scene collapse with the four measurability hypotheses replaced by the
  single frozen-data statement.

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

/-- **The paper-level frozen data measurability statement.**

The frozen coefficient and probe, read at the root and at a pair of marked cloud
points, are jointly measurable as a pair-valued function. -/
theorem measurable_rootedCoefficient_joint_of_frozenData
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hData : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        ((Acoef f t) j q.1 q.2.1.1 q.2.2.1,
          (fprobe f t) j q.1 q.2.1 q.2.2)))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) :
    Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (Acoef f t) j q.1 q.2.1.1 q.2.2.1) :=
  measurable_fst.comp (hData f t j)

/-- **The paper-level frozen data measurability statement** (probe coordinate). -/
theorem measurable_rootedProbe_joint_of_frozenData
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hData : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        ((Acoef f t) j q.1 q.2.1.1 q.2.2.1,
          (fprobe f t) j q.1 q.2.1 q.2.2)))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) :
    Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (fprobe f t) j q.1 q.2.1 q.2.2) :=
  measurable_snd.comp (hData f t j)

/-- The coordinate map from a root together with a physical Palm pair to a root
together with a pair of zero-marked carrier points. -/
def rootedDataPhysicalMap
    (p : Z × PhysicalPairPalmMark ι) :
    Z × (MarkedCloudPoint × MarkedCloudPoint) :=
  (p.1, rootedScenePairRecode (ι := ι) p.2)

/-- The physical recoding map is measurable. -/
theorem measurable_rootedDataPhysicalMap :
    Measurable (rootedDataPhysicalMap (Z := Z) (ι := ι)) :=
  Measurable.prodMk measurable_fst
    ((measurable_rootedScenePairRecode (ι := ι)).comp measurable_snd)

/-- **Physical Palm pair measurability of the frozen coefficient**, pulled back
from the paper-level frozen data statement along rootedScenePairRecode. -/
theorem measurable_rootedCoefficient_physical_of_frozenData
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hData : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        ((Acoef f t) j q.1 q.2.1.1 q.2.2.1,
          (fprobe f t) j q.1 q.2.1 q.2.2)))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) :
    Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (Acoef f t) j p.1 p.2.1.1 p.2.1.2) := by
  have h := (measurable_rootedCoefficient_joint_of_frozenData Acoef fprobe hData f t j).comp
    (measurable_rootedDataPhysicalMap (Z := Z) (ι := ι))
  have hfun : (fun p : Z × PhysicalPairPalmMark ι ↦
      (Acoef f t) j p.1 p.2.1.1 p.2.1.2) =
      ((fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        (Acoef f t) j q.1 q.2.1.1 q.2.2.1) ∘ rootedDataPhysicalMap (Z := Z) (ι := ι)) := by
    funext p
    simp only [Function.comp_apply, rootedDataPhysicalMap, rootedScenePairRecode]
  rw [hfun]
  exact h

/-- **Physical Palm pair measurability of the frozen probe**, pulled back from the
paper-level frozen data statement along rootedScenePairRecode. -/
theorem measurable_rootedProbe_physical_of_frozenData
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hData : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        ((Acoef f t) j q.1 q.2.1.1 q.2.2.1,
          (fprobe f t) j q.1 q.2.1 q.2.2)))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) :
    Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (fprobe f t) j p.1 (p.2.1.1, bridgeUnitMarkZero)
        (p.2.1.2, bridgeUnitMarkZero)) := by
  have h := (measurable_rootedProbe_joint_of_frozenData Acoef fprobe hData f t j).comp
    (measurable_rootedDataPhysicalMap (Z := Z) (ι := ι))
  have hfun : (fun p : Z × PhysicalPairPalmMark ι ↦
      (fprobe f t) j p.1 (p.2.1.1, bridgeUnitMarkZero) (p.2.1.2, bridgeUnitMarkZero)) =
      ((fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        (fprobe f t) j q.1 q.2.1 q.2.2) ∘ rootedDataPhysicalMap (Z := Z) (ι := ι)) := by
    funext p
    simp only [Function.comp_apply, rootedDataPhysicalMap, rootedScenePairRecode,
      bridgeUnitMarkZero_eq_carrierUnitMarkZero]
  rw [hfun]
  exact h

/-- **The final assembled scene collapse from one paper-level measurability
statement.**

This is the final form of the assembled scene collapse of
FinslerOriginalRootedEdgeMeasurability.lean with hAjoint, hfpjoint, hAphys and
hFpphys replaced by the single frozen-data joint measurability hypothesis hData.
All analytic side conditions (measurability transfer, Palm integrability, mass
normalisation, transport) are derived; the remaining inputs are the frozen data
measurability hData, the uniform probe bound G, the finite weighted kinetic class
of the rooted scene carrier, a.e. coverage and unit density of the root
partition, and the Palm readout constancy. -/
theorem campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_data
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsProbabilityMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instDataMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hData : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        ((Acoef f t) j q.1 q.2.1.1 q.2.2.1,
          (fprobe f t) j q.1 q.2.1 q.2.2)))
    {G : ℝ} (hG : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hMK : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z)
        (rootedSceneRootCarrier Q hforward))
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
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ :=
  campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_final
    Seed a κ lambda Acoef fprobe hq hF hcomplete hu ha hinj Q hforward
    (fun f' t' j ↦ measurable_rootedCoefficient_joint_of_frozenData Acoef fprobe
      hData f' t' j)
    (fun f' t' j ↦ measurable_rootedProbe_joint_of_frozenData Acoef fprobe
      hData f' t' j)
    (fun f' t' j ↦ measurable_rootedCoefficient_physical_of_frozenData Acoef fprobe
      hData f' t' j)
    (fun f' t' j ↦ measurable_rootedProbe_physical_of_frozenData Acoef fprobe
      hData f' t' j)
    hG hMK f t g hglue hcover hunithaar Ψ hconst

end OTSelector.Reconstruction