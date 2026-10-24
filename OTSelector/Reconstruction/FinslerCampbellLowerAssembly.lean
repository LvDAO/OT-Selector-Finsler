import OTSelector.PointProcess.StationaryForwardMatching
import OTSelector.Reconstruction.FinslerStationaryPressureContinuity
import OTSelector.Reconstruction.FinslerPopulationAtlasPressure

/-!
# Campbell lower comparison at the atlas level

The stationary pressure is integrated against the population root measure
`lambda`. Its weight is `θ^(-2/q)`; after changing to the coordinate Haar
measure the weight becomes `θ^(1-2/q)`.

Pointwise domination by a frozen matching cost gives the comparison on every
piece and then on the full atlas. Integrability and summability use actual
integrand bounds or piecewise L1 majorants. An upper bound for `θ` alone does
not give a uniform bound for an integrand weighted by its negative power.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Filter
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

open OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The Campbell-averaged frozen cost -/

/-- The Campbell-averaged frozen cost
`∑_j ∫_{piece_j} θ_j(z)^(-2/q) g z ∂lambda`.

This is the right-hand side of the atlas-level Campbell lower comparison: the
weighted stationary value `I_{j,w}(z, t θ^(2/q))` is replaced by the frozen cost
`g z` produced by the Campbell formula on the limiting rooted scene. -/
noncomputable def campbellAveragedFrozenCost
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (g : Z → ℝ) (q : ℝ) : ℝ :=
  ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
    populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z ∂lambda

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
@[simp]
theorem campbellAveragedFrozenCost_def
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (g : Z → ℝ) (q : ℝ) :
    campbellAveragedFrozenCost P a κ lambda g q =
      ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z ∂lambda := rfl

/-! ## Eta lemmas for the root families -/

/-- The root kinetic family at a fixed root is the Palm kinetic energy. -/
@[simp]
theorem stationaryForwardKineticFamily_apply
    (α β : Measure UnitMark) (A : ℕ → Z → ℝ → ℝ → ℝ) (j : ℕ) (z : Z) :
    stationaryForwardKineticFamily α β A j z = palmKinetic (A j z) := by
  funext M
  rfl

/-- The root probe family at a fixed root is the Palm probe. -/
@[simp]
theorem stationaryForwardProbeFamily_apply
    (α β : Measure UnitMark)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) (j : ℕ) (z : Z) :
    stationaryForwardProbeFamily α β f j z = palmProbe (f j z) := by
  funext M
  rfl

/-! ## The tsum comparison -/

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Atlas-level Campbell lower comparison, abstract form.

If the weighted stationary value is dominated by a frozen cost `g` almost
everywhere on each selected root piece, and the corresponding piece integrals
are integrable and summable, then the Campbell-averaged stationary infimum is at
most the Campbell-averaged frozen cost.

The pointwise domination hypothesis `hdom` is the remaining geometric input
(Campbell's formula applied to the limiting rooted scene).  All measure-theoretic
steps are proved here. -/
theorem campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost
    (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : Z → ℝ) {q t : ℝ}
    (hdom : ∀ j, ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece P a κ lambda j)),
      weightedStationaryPressure α β (A j z) (f j z)
        (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ≤ g z)
    (hintI : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)))
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hintg : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z)
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hsumI : Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ∂lambda))
    (hsumg : Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z ∂lambda)) :
    campbellAveragedStationaryPressure α β P a κ lambda A f q t ≤
      campbellAveragedFrozenCost P a κ lambda g q := by
  rw [campbellAveragedStationaryPressure_def, campbellAveragedFrozenCost_def]
  refine hsumI.tsum_le_tsum (fun j ↦ ?_) hsumg
  refine integral_mono_ae (hintI j) (hintg j) ?_
  filter_upwards [hdom j] with z hz
  exact mul_le_mul_of_nonneg_left hz
    (Real.rpow_nonneg (populationAtlasTheta_nonneg P a κ lambda j z) _)

/-! ## Summability from uniform bounds -/

/-- Summability of the Campbell-averaged frozen cost from a uniform bound on the
theta-weighted frozen integrand, via `summable_populationAtlasIntegral`. -/
theorem summable_campbellAveragedFrozenCost_of_bound
    [MeasurableSpace.CountablySeparated Z]
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenSummableMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (g : Z → ℝ) {q Bg : ℝ} (hBg : 0 ≤ Bg)
    (hbound : ∀ j (z : Z),
      |populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z| ≤ Bg) :
    Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z ∂lambda) := by
  have h := summable_populationAtlasIntegral P a κ lambda hF hcomplete hu ha hinj
    (fun j z _ ↦ g z) (q := q) (t := 0) (B := Bg) hBg (by
      intro j z
      simpa only [populationAtlasIntegrand_def] using hbound j z)
  simpa only [populationAtlasIntegrand_def] using h

/-- Summability of the stationary atlas piece integrals from a uniform bound on the
theta-weighted weighted stationary pressure. -/
theorem summable_campbellAveragedStationaryPressure_of_bound
    [MeasurableSpace.CountablySeparated Z]
    (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instStationarySummableMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q t B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ j (z : Z),
      |populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))| ≤ B) :
    Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ∂lambda) := by
  have h := summable_populationAtlasIntegral P a κ lambda hF hcomplete hu ha hinj
    (fun j z w ↦ weightedStationaryPressure α β (A j z) (f j z) w)
    (q := q) (t := t) (B := B) hB (by
      intro j z
      simpa only [populationAtlasIntegrand_def] using hbound j z)
  simpa only [populationAtlasIntegrand_def] using h

/-- Bounded form of the atlas-level Campbell lower comparison: integrability on
each piece and uniform bounds making both piece-integral families summable are
explicit. -/
theorem campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost_of_bound
    [MeasurableSpace.CountablySeparated Z]
    (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instBoundedAssemblyMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : Z → ℝ) {q t BI Bg : ℝ} (hBI : 0 ≤ BI) (hBg : 0 ≤ Bg)
    (hdom : ∀ j, ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece P a κ lambda j)),
      weightedStationaryPressure α β (A j z) (f j z)
        (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ≤ g z)
    (hintI : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)))
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hintg : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z)
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hI_bound : ∀ j (z : Z),
      |populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))| ≤ BI)
    (hg_bound : ∀ j (z : Z),
      |populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g z| ≤ Bg) :
    campbellAveragedStationaryPressure α β P a κ lambda A f q t ≤
      campbellAveragedFrozenCost P a κ lambda g q :=
  campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost α β P a κ lambda A f g
    hdom hintI hintg
    (summable_campbellAveragedStationaryPressure_of_bound α β P a κ lambda hF hcomplete
      hu ha hinj A f hBI hI_bound)
    (summable_campbellAveragedFrozenCost_of_bound P a κ lambda hF hcomplete hu ha hinj
      g hBg hg_bound)

/-! ## Per-piece frozen costs -/

/-- Per-piece Campbell-averaged frozen cost
`∑_j ∫_{piece_j} θ_j(z)^(-2/q) g_j z ∂lambda`.

This is the natural form when the frozen cost produced by the Campbell argument
depends on the piece, for example when it is the kinetic-plus-probe cost of a
selected stationary matching at the piece-dependent tilt. -/
noncomputable def campbellAveragedFrozenCostFamily
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (g : ℕ → Z → ℝ) (q : ℝ) : ℝ :=
  ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
    populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g j z ∂lambda

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
@[simp]
theorem campbellAveragedFrozenCostFamily_def
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (g : ℕ → Z → ℝ) (q : ℝ) :
    campbellAveragedFrozenCostFamily P a κ lambda g q =
      ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g j z ∂lambda := rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Atlas-level Campbell lower comparison with a piece-dependent frozen cost.

The proof is the same as for a single frozen cost: pointwise a.e. domination on
each piece, monotonicity of the integral, and `Summable.tsum_le_tsum`. -/
theorem campbellAveragedStationaryPressure_le_campbellAveragedFrozenCostFamily
    (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : ℕ → Z → ℝ) {q t : ℝ}
    (hdom : ∀ j, ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece P a κ lambda j)),
      weightedStationaryPressure α β (A j z) (f j z)
        (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ≤ g j z)
    (hintI : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)))
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hintg : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g j z)
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hsumI : Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ∂lambda))
    (hsumg : Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g j z ∂lambda)) :
    campbellAveragedStationaryPressure α β P a κ lambda A f q t ≤
      campbellAveragedFrozenCostFamily P a κ lambda g q := by
  rw [campbellAveragedStationaryPressure_def, campbellAveragedFrozenCostFamily_def]
  refine hsumI.tsum_le_tsum (fun j ↦ ?_) hsumg
  refine integral_mono_ae (hintI j) (hintg j) ?_
  filter_upwards [hdom j] with z hz
  exact mul_le_mul_of_nonneg_left hz
    (Real.rpow_nonneg (populationAtlasTheta_nonneg P a κ lambda j z) _)

/-- Summability of a piece-dependent Campbell-averaged frozen cost from a uniform
bound on its theta-weighted integrand. -/
theorem summable_campbellAveragedFrozenCostFamily_of_bound
    [MeasurableSpace.CountablySeparated Z]
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFamilySummableMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (g : ℕ → Z → ℝ) {q Bg : ℝ} (hBg : 0 ≤ Bg)
    (hbound : ∀ j (z : Z),
      |populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g j z| ≤ Bg) :
    Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) * g j z ∂lambda) := by
  have h := summable_populationAtlasIntegral P a κ lambda hF hcomplete hu ha hinj
    (fun j z _ ↦ g j z) (q := q) (t := 0) (B := Bg) hBg (by
      intro j z
      simpa only [populationAtlasIntegrand_def] using hbound j z)
  simpa only [populationAtlasIntegrand_def] using h

/-! ## Discharging the pointwise domination by the matching-family cost -/

/-- The weighted stationary value is at most the kinetic-plus-probe cost of any
admissible matching.  This is the infimum inequality behind the pointwise
domination hypothesis `hdom`: choosing the frozen cost at the root `z` to be the
cost of the selected stationary matching discharges the pointwise comparison.

Only the nonnegativity of `A` and the measurability and bound of the probe are
needed; the matching supplies membership in the weighted class. -/
theorem weightedStationaryPressure_le_matchingCost
    (α β : Measure UnitMark) {A : ℝ → ℝ → ℝ}
    {f : MarkedCloudPoint → MarkedCloudPoint → ℝ} {G : ℝ}
    (hA_nonneg : ∀ a b, 0 ≤ A a b)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    {M : StationaryForwardMatching α β} (hM : FiniteWeightedKinetic A M) (v : ℝ) :
    weightedStationaryPressure α β A f v ≤ palmKinetic A M + v * palmProbe f M := by
  unfold weightedStationaryPressure
  exact stationaryValue_le
    (bddBelow_stationaryValue (G := G) (v := v)
      (fun c _ ↦ palmKinetic_nonneg hA_nonneg c)
      (fun c _ ↦ abs_palmProbe_le hf hfG c)) hM

/-- Nonnegativity of the root kinetic family on the weighted class. -/
theorem stationaryForwardKineticFamily_nonneg
    (α β : Measure UnitMark) (A : ℕ → Z → ℝ → ℝ → ℝ)
    (hA_nonneg : ∀ j z a b, 0 ≤ A j z a b) :
    ∀ j z w, w ∈ stationaryForwardWeightedClass α β A j z →
      0 ≤ stationaryForwardKineticFamily α β A j z w := by
  intro j z w _
  simpa only [stationaryForwardKineticFamily] using palmKinetic_nonneg (hA_nonneg j z) w

/-- Uniform probe bound on the root weighted class. -/
theorem stationaryForwardProbeFamily_bound
    (α β : Measure UnitMark) (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) {G : ℝ}
    (hf_meas : ∀ j z,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f j z p.1 p.2))
    (hfG : ∀ j z x y, |f j z x y| ≤ G) :
    ∀ j z w, w ∈ stationaryForwardWeightedClass α β A j z →
      |stationaryForwardProbeFamily α β f j z w| ≤ G := by
  intro j z w _
  simpa only [stationaryForwardProbeFamily] using abs_palmProbe_le (hf_meas j z) (hfG j z) w

/-- A root family of finite-weighted-kinetic matchings with kinetic energy at most
`Cb` supplies the competitor required by the uniform stationary integrand bound. -/
theorem stationaryForwardWeightedClass_competitor
    (α β : Measure UnitMark) (A : ℕ → Z → ℝ → ℝ → ℝ)
    (M : Z → StationaryForwardMatching α β) {Cb : ℝ}
    (hM : ∀ j z, FiniteWeightedKinetic (A j z) (M z))
    (hMK : ∀ j z, palmKinetic (A j z) (M z) ≤ Cb) :
    ∀ j z, ∃ w ∈ stationaryForwardWeightedClass α β A j z,
      stationaryForwardKineticFamily α β A j z w ≤ Cb := by
  intro j z
  exact ⟨M z,
    by simpa only [stationaryForwardWeightedClass, weightedClass, Set.mem_ofPred_eq]
      using hM j z,
    by simpa only [stationaryForwardKineticFamily] using hMK j z⟩

/-- The matching cost dominates the stationary infimum on the same population
root measure. Actual integrability and summability are explicit; an upper
density bound alone does not control the inverse-density factor. -/
theorem campbellAveragedStationaryPressure_le_campbellAveragedMatchingCost
    (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) {q t G : ℝ}
    (hA_nonneg : ∀ j z a b, 0 ≤ A j z a b)
    (hf_meas : ∀ j z,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f j z p.1 p.2))
    (hfG : ∀ j z x y, |f j z x y| ≤ G)
    (M : Z → StationaryForwardMatching α β)
    (hM : ∀ j z, FiniteWeightedKinetic (A j z) (M z))
    (hintI : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)))
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hintg : ∀ j, IntegrableOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        (palmKinetic (A j z) (M z) +
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) *
            palmProbe (f j z) (M z)))
      (populationSeedRootPiece P a κ lambda j) lambda)
    (hsumI : Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        weightedStationaryPressure α β (A j z) (f j z)
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ∂lambda))
    (hsumg : Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        (palmKinetic (A j z) (M z) +
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) *
            palmProbe (f j z) (M z)) ∂lambda)) :
    campbellAveragedStationaryPressure α β P a κ lambda A f q t ≤
      campbellAveragedFrozenCostFamily P a κ lambda
        (fun j z ↦ palmKinetic (A j z) (M z) +
          (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) *
            palmProbe (f j z) (M z)) q := by
  refine campbellAveragedStationaryPressure_le_campbellAveragedFrozenCostFamily
    α β P a κ lambda A f
    (fun j z ↦ palmKinetic (A j z) (M z) +
      (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) *
        palmProbe (f j z) (M z)) ?_ hintI hintg hsumI hsumg
  intro j
  filter_upwards with z
  exact weightedStationaryPressure_le_matchingCost α β
    (hA_nonneg j z) (hf_meas j z) (hfG j z) (hM j z)
    (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))

end OTSelector.Reconstruction
