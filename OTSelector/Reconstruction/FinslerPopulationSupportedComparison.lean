import OTSelector.Reconstruction.FinslerPopulationCommonSupport
import OTSelector.Reconstruction.FinslerPopulationComparisonSelection
import OTSelector.Reconstruction.FinslerPopulationSeedDensity

/-!
# One supported comparison for both original conditional populations

All seed charts and measurable time restrictions are retained inside one common
almost-everywhere set. The normalized original law selects an actual seed with a
finite nonzero label factor; both colors then use its same comparison and true span.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- A fixed original conditional law, in the actual seed clock, has the physical
density on every measurable subset of every active chart of that same seed. -/
def PopulationSeedClockDensity (S : F.CalibratedLevelSeedPatch u) (w : S.covector.ker)
    (μ : Measure ℝ) (ρ : M → ℝ) (v : M → E → ℝ) (c : ℝ) : Prop :=
  ∀ center : S.centers, w ∈ ball center.val.2 (S.radius center) →
    ∀ K : Set ℝ, MeasurableSet K →
      K ⊆ interior (S.calibrationTimes w) ∩ ball center.val.1 (S.radius center) →
      μ.restrict K = (volume.restrict K).withDensity
        (fun t ↦ ENNReal.ofReal (c * populationSeedChartDensity S ρ v center w t))

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [BorelSpace M] [StandardBorelSpace M] [Nonempty M] [MeasurableEq Z]
  [MeasurableSpace.CountablySeparated Z] in
/-- The whole active conditional law supplies simultaneous pointwise seed-clock
density formulas before any label-dependent endpoint frame is chosen. -/
theorem PopulationSeedChartDensityLaw.ae_seedClockDensity
    {S : F.CalibratedLevelSeedPatch u} {a : M → Z} {κ : Measure S.covector.ker}
    {lambda : Measure Z} {η : Measure M} [IsFiniteMeasure η]
    {ρ : M → ℝ} {v : M → E → ℝ}
    (hlaw : PopulationSeedChartDensityLaw S a κ lambda η ρ v S.level) :
    ∀ᵐ z ∂lambda, ∀ w : S.covector.ker, w ∈ S.labels → a (S.curve w 0) = z →
      PopulationSeedClockDensity S w
        ((condDistrib u a η z).map (fun s : ℝ ↦ s - S.level)) ρ v
        ((populationSeedLabelReference S a κ).rnDeriv lambda z).toReal := by
  filter_upwards [hlaw.restrict] with z hz
  intro w hw hwz center hwball K hK hsub
  simpa only [add_sub_cancel_right] using hz.2 center w hw hwz hwball K hK
    (fun t ht ↦ by simpa only [add_sub_cancel_right] using hsub ht)

/-- The common label law retains one actual comparison, both original conditional
densities and their shared attained physical support span. -/
def PopulationSupportedComparisonLaw (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (ρ₀ ρ₁ : M → ℝ) (v : M → E → ℝ) : Prop :=
  ∀ᵐ z ∂lambda, ∃ (j : ℕ) (w : (P j).seed.covector.ker) (lo hi : ℝ),
    w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
    (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z ≠ 0 ∧
    (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
    HasActiveSeedComparison (P j).seed w ∧
    CommonSeedSupportSpan (P j).seed w (condDistrib u a η₀ z) (condDistrib u a η₁ z) lo hi ∧
    PopulationSeedClockDensity (P j).seed w
      ((condDistrib u a η₀ z).map (fun s : ℝ ↦ s - (P j).seed.level)) ρ₀ v
      ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z).toReal ∧
    PopulationSeedClockDensity (P j).seed w
      ((condDistrib u a η₁ z).map (fun s : ℝ ↦ s - (P j).seed.level)) ρ₁ v
      ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z).toReal

omit [StandardBorelSpace M] [Nonempty M] [MeasurableEq Z] in
/-- The original source population selects a common actual seed, its complete
comparison, both physical conditional densities and both attained support endpoints. -/
theorem PopulationConditionalWindowLaw.ae_exists_supported_seed_comparison
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : M → E → ℝ} {vP : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η₀ ρ₀ vP)
    (hsupport : PopulationConditionalSupportLaw (F := F) (u := u) a lambda η₀ η₁)
    (hdensity₀ : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (κ j)
      lambda η₀ ρ₀ v (P j).seed.level)
    (hdensity₁ : ∀ j, PopulationSeedChartDensityLaw (P j).seed a (κ j)
      lambda η₁ ρ₁ v (P j).seed.level)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSupportedSelectionMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instSupportedSelectionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) :
    PopulationSupportedComparisonLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v := by
  have h₀ := ae_all_iff.mpr (fun j ↦ (hdensity₀ j).ae_seedClockDensity)
  have h₁ := ae_all_iff.mpr (fun j ↦ (hdensity₁ j).ae_seedClockDensity)
  filter_upwards [hlaw.ae_exists_active_seed_comparison hF hcomplete hu ha hinj horder hκ,
    hsupport, h₀, h₁] with z hz hs h₀ h₁
  obtain ⟨j, w, hw, hwz, hrn, hfinite, hcomparison⟩ := hz
  obtain ⟨lo, hi, hspan⟩ := hs (P j).seed w hw hwz
  exact ⟨j, w, lo, hi, hw, hwz, hrn, hfinite, hcomparison, hspan,
    h₀ j w hw hwz, h₁ j w hw hwz⟩

end OTSelector.Reconstruction
