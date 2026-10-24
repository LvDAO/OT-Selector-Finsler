import OTSelector.Reconstruction.FinslerOriginalAtlasTransportAssembled

/-!
# Measurability and integrability of the frozen physical edge functional

FinslerOriginalAtlasTransportAssembled.lean reduced the assembled transport theorem
to two hypotheses on the frozen physical edge functional rootedSceneFrozenEdge,
namely joint measurability in (root, physical Palm pair) and pointwise
integrability.  This module derives both from the frozen coefficient and probe
data, stated directly on PhysicalPairPalmMark pairs, and then plugs them into the
assembled scene form.

The physical frozen edge is

  rootedSceneFrozenEdge A f v m
    = (1/2) * A m.1.1 m.1.2 * (m.1.2 - m.1.1)^2
      + v * f (m.1.1, bridgeUnitMarkZero) (m.1.2, bridgeUnitMarkZero),

so its joint measurability follows from joint measurability of the frozen
coefficient and probe data and measurability of the atlas pressure weight, while
its pointwise integrability follows from the finite weighted kinetic class (via
the kinetic integrability of the rooted scene carrier) and the uniform probe
bound.

## Contents

* measurable_rootedSceneFrozenEdge_root: joint measurability of the frozen
  physical edge functional in (root, Palm pair);
* integrable_rootedSceneFrozenEdge_root: pointwise integrability of the frozen
  physical edge functional, from the kinetic integrability and the uniform probe
  bound;
* campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_final: the assembled
  scene collapse with hEdge and hint discharged, whose only remaining data
  hypotheses are joint measurability of the coefficient and probe families on
  physical Palm pairs, their per-root kinetic integrability class and the uniform
  probe bound.

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

/-- **Joint measurability of the frozen physical edge functional.**

If the frozen coefficient A = Acoef f t j and the frozen probe f = fprobe f t j
are jointly measurable in (root, physical Palm pair), then the frozen physical
edge functional, including its tilt factor t * theta_j(z)^(2/q), is measurable in
(root, physical Palm pair). -/
theorem measurable_rootedSceneFrozenEdge_root
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instEdgeMeasMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℝ} (hq : 0 < q) (t : ℝ) (f : (K × K) →ᵇ ℝ)
    (hA : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (Acoef f t) j p.1 p.2.1.1 p.2.1.2))
    (hfp : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (fprobe f t) j p.1 (p.2.1.1, bridgeUnitMarkZero)
        (p.2.1.2, bridgeUnitMarkZero))) :
    Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j p.1) ((fprobe f t) j p.1)
        (t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) p.2) := by
  have hθ : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      populationAtlasTheta Seed a κ lambda j p.1) :=
    (measurable_populationAtlasTheta_root Seed a κ lambda hF hcomplete hu ha hinj j).comp
      measurable_fst
  have hθpow : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) :=
    measurable_const.mul
      ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 2 / q)).measurable.comp hθ)
  have h21 : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦ p.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have h22 : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦ p.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hdisp : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (p.2.1.2 - p.2.1.1) ^ 2) :=
    ((continuous_pow 2).measurable).comp (h22.sub h21)
  have hkin : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (1 / 2 : ℝ) * (Acoef f t) j p.1 p.2.1.1 p.2.1.2 *
        (p.2.1.2 - p.2.1.1) ^ 2) :=
    (measurable_const.mul hA).mul hdisp
  have hprobe : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) *
        (fprobe f t) j p.1 (p.2.1.1, bridgeUnitMarkZero)
          (p.2.1.2, bridgeUnitMarkZero)) :=
    hθpow.mul hfp
  unfold rootedSceneFrozenEdge
  exact hkin.add hprobe

/-- **Pointwise integrability of the frozen physical edge functional.**

For every root, the frozen physical edge is integrable against the rooted scene
Palm law as soon as its frozen kinetic part is integrable at every root (the
finite weighted kinetic class of the carrier) and the frozen probe is uniformly
bounded. -/
theorem integrable_rootedSceneFrozenEdge_root
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (j : ℕ) {q : ℝ} (t : ℝ) (f : (K × K) →ᵇ ℝ)
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    [IsProbabilityMeasure (rootedScenePalmMeasure Q)]
    (hKin : ∀ z, Integrable (fun m : PhysicalPairPalmMark ι ↦
      (1 / 2 : ℝ) * (Acoef f t) j z m.1.1 m.1.2 * (m.1.2 - m.1.1) ^ 2)
      (rootedScenePalmMeasure Q))
    (hfp : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      (fprobe f t) j p.1 (p.2.1.1, bridgeUnitMarkZero)
        (p.2.1.2, bridgeUnitMarkZero)))
    {G : ℝ} (hG : ∀ z (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G) :
    ∀ z, Integrable (fun m : PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) m)
      (rootedScenePalmMeasure Q) := by
  intro z
  have hsec : Measurable (fun m : PhysicalPairPalmMark ι ↦
      (fprobe f t) j z (m.1.1, bridgeUnitMarkZero) (m.1.2, bridgeUnitMarkZero)) :=
    hfp.comp (Measurable.prodMk measurable_const measurable_id)
  have hbdd : ∀ᵐ m ∂(rootedScenePalmMeasure Q),
      ‖(fprobe f t) j z (m.1.1, bridgeUnitMarkZero)
        (m.1.2, bridgeUnitMarkZero)‖ ≤ G :=
    Filter.Eventually.of_forall (fun m => by
      simpa only [Real.norm_eq_abs] using hG z _ _)
  have hInt : Integrable (fun m : PhysicalPairPalmMark ι ↦
      (fprobe f t) j z (m.1.1, bridgeUnitMarkZero) (m.1.2, bridgeUnitMarkZero))
      (rootedScenePalmMeasure Q) :=
    Integrable.of_bound hsec.aestronglyMeasurable G hbdd
  have hprobe : Integrable (fun m : PhysicalPairPalmMark ι ↦
      (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
        (fprobe f t) j z (m.1.1, bridgeUnitMarkZero) (m.1.2, bridgeUnitMarkZero))
      (rootedScenePalmMeasure Q) :=
    hInt.const_mul (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))
  unfold rootedSceneFrozenEdge
  exact (hKin z).add hprobe

/-- **The assembled scene collapse with the frozen edge data discharged.**

This is the final assembled scene form of FinslerOriginalAtlasTransportAssembled.lean
with the two frozen-edge hypotheses hEdge and hint derived from the frozen
coefficient and probe data.  Its remaining data hypotheses are: joint
measurability of Acoef and fprobe on physical Palm pairs, the uniform probe bound,
and the finite weighted kinetic class of the rooted scene carrier. -/
theorem campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_final
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsProbabilityMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instEdgeFinalMetric : MetricSpace M := F.metricSpace;
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
    (hAphys : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
        (Acoef f t) j p.1 p.2.1.1 p.2.1.2))
    (hFpphys : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
        (fprobe f t) j p.1 (p.2.1.1, bridgeUnitMarkZero)
          (p.2.1.2, bridgeUnitMarkZero)))
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
    campbellAveragedFrozenCost Seed a κ lambda g q = Ψ := by
  haveI : IsProbabilityMeasure (rootedScenePalmMeasure Q) := by
    rw [rootedScenePalmMeasure_eq_rootedScenePhysicalPalm (ι := ι)]
    infer_instance
  refine campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_assembled
    Seed a κ lambda Acoef fprobe hq hF hcomplete hu ha hinj Q hforward
    hAjoint hfpjoint hG hMK
    (fun f' t' j ↦ measurable_rootedSceneFrozenEdge_root Seed a κ lambda Acoef fprobe
      hF hcomplete hu ha hinj j (by linarith) t' f'
      (hAphys f' t' j) (hFpphys f' t' j))
    (fun f' t' j z ↦ integrable_rootedSceneFrozenEdge_root Seed a κ lambda Acoef fprobe
      j (q := q) t' f'
      (fun z ↦ integrable_rootedSceneFrozenKinetic Q hforward (hMK f' t' j z))
      (hFpphys f' t' j) (fun z x y ↦ hG f' t' j z x y) z)
    f t g hglue hcover hunithaar Ψ hconst

end OTSelector.Reconstruction