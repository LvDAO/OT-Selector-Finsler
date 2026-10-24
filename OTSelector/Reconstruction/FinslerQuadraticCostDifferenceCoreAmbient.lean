import OTSelector.Reconstruction.FinslerQuadraticCostDifferenceCore
import OTSelector.Geometry.FinslerQuadraticCostDifferenceAmbient

/-!
# Actual ambient rigidity at a frozen population root

The original frozen coefficient acts on any source law absolutely continuous
with respect to spatial Haar measure times an arbitrary clock law. The occupied
countable target set supplies its indices internally. Any measurable subdomain
of the retained legal window is allowed, including its strict interior.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction.OriginalPopulationCoefficientCore

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}
  (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M]
    [MeasurableSpace.CountablySeparated Z] in
/-- The retained pair region is measurable in both actual marked endpoints. -/
theorem measurableSet_frozenQuadratic_ambientDomain :
    MeasurableSet (C.frozenQuadraticLegalDomain id) :=
  C.window.isCompact_region.measurableSet.preimage
    ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))

/-- Original frozen-root ambient plans agree on any measurable retained legal
subdomain. The source clock reference is independent of the coefficient's
original conditional law; in particular it may be Lebesgue measure. -/
theorem ambient_frozenQuadratic_plans_eq
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCoreQuadraticMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {z : Z} (hz : z ∈ C.roots)
    (m : Measure (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    [m.IsAddHaarMeasure]
    (clock : Measure ℝ) [SFinite clock]
    {ρ : Measure ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)}
    (hρ : ρ ≪ m.prod clock)
    {T : Set ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)}
    (hT : T.Countable) (hTinj : InjOn Prod.fst T)
    (θ : Measure ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ))
    (hθ : ∀ᵐ y ∂θ, y ∈ T)
    (π₀ π₁ : Measure (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)))
    (hsource₀ : π₀.map Prod.fst = ρ) (hsource₁ : π₁.map Prod.fst = ρ)
    (htarget₀ : π₀.map Prod.snd = θ) (htarget₁ : π₁.map Prod.snd = θ)
    (legal : Set (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)))
    (hlegal : MeasurableSet legal) (hsub : legal ⊆ C.frozenQuadraticLegalDomain id)
    (hlegal₀ : ∀ᵐ p ∂π₀, p ∈ legal) (hlegal₁ : ∀ᵐ p ∂π₁, p ∈ legal)
    (hcycle : IsTwoCycleMonotoneOn (C.frozenQuadraticCost z) legal
      ((((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) ∩ legal)) :
    π₀ = π₁ := by
  apply ambient_quadratic_plans_eq_of_countable_spatial_cloud
    m clock hρ
    (fun s t ↦ populationSeedRootCoefficient (P C.seedIndex).seed a
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (z, s, t))
    (fun _ ↦ (measurable_populationSeedRootCoefficient (P C.seedIndex).seed
      hF hcomplete hu ha hinj _).comp
        (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
    hT hTinj θ hθ π₀ π₁ hsource₀ hsource₁ htarget₀ htarget₁
    legal hlegal
    _ hlegal₀ hlegal₁ hcycle
  intro p hp
  exact C.coefficient_posDef z hz _ (hsub hp)

end OTSelector.Reconstruction.OriginalPopulationCoefficientCore
