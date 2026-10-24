import OTSelector.Reconstruction.FinslerOriginalRootMeasurability

/-!
# Root-variable measurability of the frozen atlas data

The atlas transport consumes, through FinslerOriginalRootMeasurability.lean, only
the root-variable measurability of the two frozen functionals:

  z |-> atlasRootFrozenIntegrand ... j z,
  z |-> rootedScenePalmReadout Q (rootedSceneFrozenEdge ((Acoef f t) j z)
                                   ((fprobe f t) j z) (t * theta_j(z)^(2/q))).

This module proves both from joint measurability of the frozen coefficient, probe
and matching data at the root.

## 1. Parametric integral measurability

* measurable_integral_of_uncurry_measurable: a real-valued integral depending on a
  parameter is measurable as soon as the joint integrand is measurable and the
  integral is finite at every parameter.  The proof splits the Bochner integral
  into its positive and negative lintegrals and applies Tonelli measurability.

## 2. The Palm kinetic and probe moments

* measurable_palmKinetic_of_root and measurable_palmProbe_of_root: for a fixed
  stationary matching the Palm kinetic moment and the Palm probe moment are
  measurable functions of the root parameter, from joint measurability of the
  coefficient and probe families (and the paper's finite weighted kinetic class
  for finiteness of the kinetic integral).

## 3. The two frozen functionals

* measurable_atlasRootFrozenIntegrand_constMatching: the atlas frozen root
  integrand is measurable in the root variable;
* measurable_rootedScenePalmReadout_root: the physical Palm readout of the frozen
  edge functional is measurable in the root variable.

Both statements are exactly the hypotheses of the discharge lemmas
hAmeas_of_measurable_root and hRmeas_of_measurable_root of
FinslerOriginalRootMeasurability.lean, so the bridge side conditions hAmeas/hRmeas
are met once an olean of that module is available.

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

/-! ## 1. Parametric integral measurability -/

/-- **Parametric real-valued integral measurability.**

If the joint integrand phi : a x b -> R is measurable and every section is
integrable, then the integral over the second variable is a measurable function
of the parameter.  The proof writes the Bochner integral as the difference of the
two lintegrals of its positive and negative parts and applies Tonelli
measurability to each. -/
theorem measurable_integral_of_uncurry_measurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {φ : α → β → ℝ}
    (hφ : Measurable (Function.uncurry φ)) (hint : ∀ x, Integrable (φ x) ν) :
    Measurable (fun x ↦ ∫ y, φ x y ∂ν) := by
  have hpos : Measurable (fun x ↦ ∫⁻ y, ENNReal.ofReal (φ x y) ∂ν) :=
    Measurable.lintegral_prod_right (f := fun x y ↦ ENNReal.ofReal (φ x y))
      hφ.ennreal_ofReal
  have hneg : Measurable (fun x ↦ ∫⁻ y, ENNReal.ofReal (-(φ x y)) ∂ν) :=
    Measurable.lintegral_prod_right (f := fun x y ↦ ENNReal.ofReal (-(φ x y)))
      hφ.neg.ennreal_ofReal
  have hEq : (fun x ↦ ∫ y, φ x y ∂ν) =
      fun x ↦ (∫⁻ y, ENNReal.ofReal (φ x y) ∂ν).toReal -
        (∫⁻ y, ENNReal.ofReal (-(φ x y)) ∂ν).toReal := by
    funext x
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint x)
  rw [hEq]
  exact (ENNReal.measurable_toReal.comp hpos).sub
    (ENNReal.measurable_toReal.comp hneg)

/-! ## 2. The Palm kinetic and probe moments -/

/-- **Root-variable measurability of the Palm kinetic moment.**

For a fixed stationary matching M and a family of coefficients A z jointly
measurable in (root, matched pair), if every member lies in the paper's finite
weighted kinetic class for M, then z |-> palmKinetic (A z) M is measurable. -/
theorem measurable_palmKinetic_of_root
    {α β : Measure UnitMark}
    {A : Z → ℝ → ℝ → ℝ}
    (hA : Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      A q.1 q.2.1.1 q.2.2.1))
    (M : StationaryForwardMatching α β)
    (hMK : ∀ z, StationaryForwardMatching.FiniteWeightedKinetic (A z) M) :
    Measurable (fun z ↦ StationaryForwardMatching.palmKinetic (A z) M) := by
  haveI : IsProbabilityMeasure M.palm := M.palm_isProbability
  haveI : SFinite M.palm := inferInstance
  have h2 : Measurable (fun a : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦ a.2) :=
    measurable_snd
  have hdisp : Measurable (fun a : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      a.2.2.1 - a.2.1.1) :=
    (measurable_fst.comp (measurable_snd.comp h2)).sub
      (measurable_fst.comp (measurable_fst.comp h2))
  have hpow2 : Measurable (fun a : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (a.2.2.1 - a.2.1.1) ^ 2) :=
    ((continuous_pow 2).measurable).comp hdisp
  have hfin : Measurable (fun a : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (1 / 2 : ℝ) * A a.1 a.2.1.1 a.2.2.1 * (a.2.2.1 - a.2.1.1) ^ 2) :=
    (measurable_const.mul hA).mul hpow2
  have hjoint : Measurable (Function.uncurry
      (fun z : Z ↦ fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        StationaryForwardMatching.kineticIntegrand (A z) p)) := by
    unfold Function.uncurry
    simpa only [StationaryForwardMatching.kineticIntegrand,
      StationaryForwardMatching.edgeDisplacement] using hfin
  have hint : ∀ z, Integrable
      (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
        StationaryForwardMatching.kineticIntegrand (A z) p) M.palm :=
    fun z ↦ hMK z
  exact measurable_integral_of_uncurry_measurable hjoint hint

/-- **Root-variable measurability of the Palm probe moment.**

For a fixed stationary matching M and a bounded family of probes jointly
measurable in (root, matched pair), z |-> palmProbe (f z) M is measurable. -/
theorem measurable_palmProbe_of_root
    {α β : Measure UnitMark}
    {fp : Z → MarkedCloudPoint → MarkedCloudPoint → ℝ}
    (hfp : Measurable (fun q : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      fp q.1 q.2.1 q.2.2))
    (M : StationaryForwardMatching α β) {G : ℝ}
    (hG : ∀ z (x y : MarkedCloudPoint), |fp z x y| ≤ G) :
    Measurable (fun z ↦ StationaryForwardMatching.palmProbe (fp z) M) := by
  have hjoint : Measurable (Function.uncurry
      (fun z : Z ↦ fun p : MarkedCloudPoint × MarkedCloudPoint ↦ fp z p.1 p.2)) := by
    unfold Function.uncurry
    exact hfp
  haveI : IsProbabilityMeasure M.palm := M.palm_isProbability
  haveI : SFinite M.palm := inferInstance
  have hint : ∀ z, Integrable
      (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ fp z p.1 p.2) M.palm := by
    intro z
    have hsection : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ fp z p.1 p.2) := by
      have hzk : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ (z, p)) :=
        Measurable.prodMk measurable_const measurable_id
      exact hfp.comp hzk
    have hmeas : AEStronglyMeasurable
        (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ fp z p.1 p.2) M.palm :=
      hsection.aestronglyMeasurable
    refine Integrable.of_bound hmeas G ?_
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using hG z p.1 p.2
  exact measurable_integral_of_uncurry_measurable hjoint hint

/-! ## 3. The frozen functionals -/

/-- The population atlas pressure weight is measurable in the root. -/
theorem measurable_populationAtlasTheta_root
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootThetaMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) :
    Measurable (populationAtlasTheta Seed a κ lambda j) :=
  ENNReal.measurable_toReal.comp
    ((measurable_populationSeedPieceHaarDensity Seed a κ lambda hF hcomplete hu ha hinj j).comp
      (measurable_populationSeedRootLabelValue (Seed j).seed hF hcomplete hu ha hinj))

/-- **Root-variable measurability of the atlas frozen root integrand** (for a
matching that does not depend on the root).

The atlas frozen integrand is the Palm kinetic moment plus the tilt times the Palm
probe moment.  The first factor is measurable by
measurable_palmKinetic_of_root, the second by measurable_palmProbe_of_root and the
measurability of the theta weight. -/
theorem measurable_atlasRootFrozenIntegrand_constMatching
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mm : StationaryForwardMatching α β)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRootFrozenMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) (q : ℝ) (hq : 0 < q) (t : ℝ) (f : (K × K) →ᵇ ℝ)
    (hA : Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (Acoef f t) j q'.1 q'.2.1.1 q'.2.2.1))
    (hfp : Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (fprobe f t) j q'.1 q'.2.1 q'.2.2))
    (hMK : ∀ z, StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) Mm)
    {G : ℝ} (hG : ∀ z (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G) :
    Measurable (atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe
      (fun _ _ _ _ ↦ Mm) q t f j) := by
  have hkin := measurable_palmKinetic_of_root
    (A := fun z ↦ (Acoef f t) j z) hA Mm hMK
  have hprobe := measurable_palmProbe_of_root
    (fp := fun z ↦ (fprobe f t) j z) hfp Mm hG
  have htheta := measurable_populationAtlasTheta_root Seed a κ lambda
    hF hcomplete hu ha hinj j
  have hpow : Measurable (fun z ↦ populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) :=
    (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 2 / q)).measurable.comp htheta
  change Measurable (fun z ↦
    StationaryForwardMatching.palmKinetic ((Acoef f t) j z) Mm +
      (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) *
        StationaryForwardMatching.palmProbe ((fprobe f t) j z) Mm)
  exact hkin.add ((measurable_const.mul hpow).mul hprobe)

/-- **Root-variable measurability of the frozen Palm readout.**

For the fixed Palm law of the limiting rooted scene, the physical Palm readout of
the frozen edge functional is a measurable function of the root as soon as the
joint edge functional is measurable in (root, Palm pair) and is integrable at
every root. -/
theorem measurable_rootedScenePalmReadout_root
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [SFinite (rootedScenePalmMeasure Q)]
    (j : ℕ) (q : ℝ) (t : ℝ) (f : (K × K) →ᵇ ℝ) :
    (Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j p.1) ((fprobe f t) j p.1)
        (t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) p.2)) →
    (∀ z, Integrable (fun m : PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) m)
      (rootedScenePalmMeasure Q)) →
    Measurable (fun z : Z ↦ rootedScenePalmReadout Q
      (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)))) := by
  intro hEdge hint
  have hjoint : Measurable (Function.uncurry (fun z : Z ↦
      fun m : PhysicalPairPalmMark ι ↦
        rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) m)) := by
    unfold Function.uncurry
    exact hEdge
  have := measurable_integral_of_uncurry_measurable
    (ν := rootedScenePalmMeasure Q) hjoint hint
  simpa only [rootedScenePalmReadout] using this


/-! ## 4. The bridge side conditions hAmeas and hRmeas, discharged -/

/-- **hAmeas of the atlas bridge, discharged for a root-independent matching.**

The bridge side condition hAmeas holds with the frozen atlas root integrand as the
root functional, by root-variable measurability of the frozen atlas integrand and
the ambient-kernel transfer of FinslerOriginalRootMeasurability.lean. -/
theorem hAmeas_bridge_discharged
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mm : StationaryForwardMatching α β)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instBridgeAmeasMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℝ} (hq : 2 < q) (t : ℝ) (f : (K × K) →ᵇ ℝ)
    (hA : Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (Acoef f t) j q'.1 q'.2.1.1 q'.2.2.1))
    (hfp : Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
      (fprobe f t) j q'.1 q'.2.1 q'.2.2))
    (hMK : ∀ z, StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z) Mm)
    {G : ℝ} (hG : ∀ z (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G) :
    AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe (fun _ _ _ _ ↦ Mm)
          q t f j (a ((Seed j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)) :=
  hAmeas_of_measurable_root α β Seed a κ lambda Acoef fprobe (fun _ _ _ _ ↦ Mm)
    hF hcomplete hu ha hinj j hq t f
    (measurable_atlasRootFrozenIntegrand_constMatching α β Seed a κ lambda Acoef fprobe Mm
      hF hcomplete hu ha hinj j q (by linarith) t f hA hfp hMK hG)

/-- **hRmeas of the atlas bridge, discharged for a root-independent matching.**

The bridge side condition hRmeas holds with the physical Palm readout of the frozen
edge functional as the root functional, by root-variable measurability of that
readout and the ambient-kernel transfer of FinslerOriginalRootMeasurability.lean. -/
theorem hRmeas_bridge_discharged
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instBridgeRmeasMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℝ} (hq : 2 < q) (t : ℝ) (f : (K × K) →ᵇ ℝ)
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    [SFinite (rootedScenePalmMeasure Q)]
    (hEdge : Measurable (fun p : Z × PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j p.1) ((fprobe f t) j p.1)
        (t * populationAtlasTheta Seed a κ lambda j p.1 ^ (2 / q)) p.2))
    (hint : ∀ z, Integrable (fun m : PhysicalPairPalmMark ι ↦
      rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) m)
      (rootedScenePalmMeasure Q)) :
    AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        rootedScenePalmReadout Q
          (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
            ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
            (t * populationAtlasTheta Seed a κ lambda j
              (a ((Seed j).seed.curve w 0)) ^ (2 / q))))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)) :=
  hRmeas_of_measurable_root Seed a κ lambda Acoef fprobe hF hcomplete hu ha hinj j hq t f
    (measurable_rootedScenePalmReadout_root Acoef fprobe Seed a κ lambda Q j q t f hEdge hint)

end OTSelector.Reconstruction