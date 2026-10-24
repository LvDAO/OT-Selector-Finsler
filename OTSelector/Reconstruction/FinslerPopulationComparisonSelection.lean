import OTSelector.Reconstruction.FinslerPopulationSeedSelection
import OTSelector.Geometry.FinslerSeedActiveJacobian

/-!
# An actual comparison selected by the original common label law

Normalization selects an original seed with nonzero label density. Its retained
C1,1 presentation then constructs one complete comparison with the same actual
phase derivatives and positive physical Jacobian throughout the active interval.
The comparison is selected before either endpoint graph chart or basis.
-/

open Set MeasureTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- One complete comparison from the retained original presentation, valid at
all active times and in every actual manifold chart. No graph space is chosen. -/
def HasActiveSeedComparison (S : F.CalibratedLevelSeedPatch u) (w : S.covector.ker) : Prop :=
  let D := Classical.choice S.c11_presentation
  let R := fderiv ℝ D.position w
  let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
  let p := (D.position w, fderiv ℝ D.potential (D.position w))
  ∃ C : F.SmoothPhaseJetComparison D.initialChart 0 w p R Q,
    C.labels ⊆ S.openLabels ∧ S.curve w = C.curve w ∧
      (∀ (old : M) (t : ℝ), S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        HasFDerivAt (F.chartMomentumFamily old S.curve)
          (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t) ∧
        HasFDerivAt (F.chartMomentumFamily old C.curve)
          (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t)) ∧
      ∀ (old : M) (t : ℝ), t ∈ interior (S.calibrationTimes w) →
        S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        0 < parameterizedJacobian
          (fun q : ℝ × S.covector.ker ↦ extChartAt 𝓘(ℝ, E) old (S.curve q.2 q.1))
          S.normalization (t, w)

/-- The normalized original population selects one actual seed and its complete
comparison for almost every common label, with a finite nonzero reference factor. -/
theorem PopulationConditionalWindowLaw.ae_exists_active_seed_comparison
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instActiveSelectionMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instActiveSelectionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) :
    ∀ᵐ z ∂lambda, ∃ (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z ≠ 0 ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
        HasActiveSeedComparison (P j).seed w := by
  apply hlaw.ae_exists_good_seed hF hcomplete hu ha hinj horder
    (fun j ↦ by let _instActiveSelectionHaar : (κ j).IsAddHaarMeasure := hκ j; infer_instance)
    (fun j ↦ HasActiveSeedComparison (P j).seed)
  intro j
  let _instActiveComparisonHaar : (κ j).IsAddHaarMeasure := hκ j
  filter_upwards [(P j).seed.ae_exists_comparison_active_jacobian
    (Classical.choice (P j).seed.c11_presentation) hF hcomplete hu (κ j)] with w hw
  exact hw.2

end OTSelector.Reconstruction
