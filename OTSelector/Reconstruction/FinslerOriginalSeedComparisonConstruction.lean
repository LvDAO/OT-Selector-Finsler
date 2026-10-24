import OTSelector.Reconstruction.FinslerOriginalConditionalMomentsAssembly
import OTSelector.Reconstruction.FinslerPopulationComparisonSelection
import OTSelector.Reconstruction.FinslerPopulationSupportedComparison
import OTSelector.Reconstruction.FinslerPopulationConditionalSupport

/-!
# Construction of the seed comparison and clock data from the raw geometry

The conditional-moments assembly file took the smooth phase-jet comparison
(HasActiveSeedComparison), the physical clock density (PopulationSeedClockDensity)
and the atomlessness of the conditional clock laws as hypotheses.  The library
constructs them from the raw Finsler seed geometry and normalized population law,
almost everywhere:

* PopulationConditionalWindowLaw.ae_exists_active_seed_comparison: one complete
  comparison with the actual phase derivatives and positive physical Jacobian;
* PopulationConditionalWindowLaw.ae_compact_atomless_clock: atomless conditional
  clock laws with compact support carried by an explicit compact physical set;
* PopulationSeedChartDensityLaw.ae_seedClockDensity: the physical clock density
  formula on every active chart.

This file extracts those almost-everywhere constructions at a single label and
packages the seed-curve continuity coming from the C1,1 presentation and the
Euler-Lagrange regularity.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology Manifold Metric
  OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unnecessarySimpa false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]
  [MeasurableEq Z] in
/-- The complete seed curve of a retained seed is continuous, from the C1,1
presentation and the Euler-Lagrange regularity of the calibrated level seed. -/
theorem continuous_curve_of_seed (S : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) :
    Continuous (S.curve w) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w hw t (mem_univ _))).continuousAt

omit [MeasurableEq Z] in
/-- An almost-everywhere property is nonempty for a probability label law. -/
theorem exists_of_eventually_of_isProbabilityMeasure {lambda : Measure Z}
    [IsProbabilityMeasure lambda] {p : Z → Prop}
    (h : ∀ᵐ z ∂lambda, p z) : ∃ z, p z := by
  by_contra hnot
  simp only [not_exists] at hnot
  have hnever : ∀ᵐ z ∂lambda, False := h.mono (fun z hz => hnot z hz)
  have huniv : lambda univ = 0 := by
    have := (ae_iff (μ := lambda) (p := fun _ => False)).mp hnever
    simpa using this
  rw [measure_univ] at huniv
  exact one_ne_zero huniv

omit [StandardBorelSpace M] [Nonempty M] [MeasurableEq Z] in
/-- One actual seed with a complete phase-jet comparison, constructed from the raw
normalized population window law. -/
theorem exists_activeSeedComparison_of_windowLaw
    [MeasurableSpace.CountablySeparated Z]
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta : Measure M} [IsFiniteMeasure eta] {rho : M → ℝ} {v : ℕ → E → ℝ}
    [IsProbabilityMeasure lambda]
    (hlaw : PopulationConditionalWindowLaw P a kappa lambda eta rho v)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instActiveConstructionMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u => (a x.val, u x.val)))
    (horder : let _instActiveConstructionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hkappa : ∀ j, (kappa j).IsAddHaarMeasure) :
    ∃ (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ HasActiveSeedComparison (P j).seed w := by
  obtain ⟨z, j, w, hw, _hz, _hne, _htop, hactive⟩ :=
    exists_of_eventually_of_isProbabilityMeasure
      (hlaw.ae_exists_active_seed_comparison hF hcomplete hu ha hinj horder hkappa)
  exact ⟨j, w, hw, hactive⟩

omit [BorelSpace E] in
/-- One actual label whose conditional clock law is atomless with compact support
carried by an explicit compact physical set. -/
theorem exists_compact_atomless_clock_of_windowLaw
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta : Measure M} [IsFiniteMeasure eta] {rho : M → ℝ} {v : ℕ → E → ℝ}
    [IsProbabilityMeasure lambda]
    (hlaw : PopulationConditionalWindowLaw P a kappa lambda eta rho v)
    (ha : Measurable a)
    (hu : let _instClockConstructionMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {A : Set M} (hA : IsCompact A) (hEtaA : ∀ᵐ x ∂eta, x ∈ A) :
    ∃ z : Z, NullSingletonClass (condDistrib u a eta z) ∧
      IsCompact (condDistrib u a eta z).support ∧
      (condDistrib u a eta z).support ⊆ u '' A := by
  obtain ⟨z, hnull, hcompact, hsub, _hshift⟩ :=
    exists_of_eventually_of_isProbabilityMeasure
      (hlaw.ae_compact_atomless_clock ha hu hA hEtaA)
  exact ⟨z, hnull, hcompact, hsub⟩

end OTSelector.Reconstruction

end
