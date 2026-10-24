import OTSelector.Geometry.Finsler.SlackAtomlessness
import OTSelector.Transport.CyclicMonotonicity.CountableTargetRigidity

/-!
# Countable-target rigidity for the original Finsler distance

The general geometric distance-difference theorem supplies the atomlessness
needed for two-cycle rigidity. Thus two same-source plans whose average has a
common two-cycle monotone support agree, for arbitrary countably many distinct
physical targets. The measure need not be finite and no curvature sign or
extra topological condition is imposed.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {F : ContinuousFinslerNorm E M}

/-- Genuine Finsler distance geometry discharges the pairwise atomlessness
input in countable-target plan rigidity, also after scaling and adding a potential. -/
theorem countable_plans_eq_of_scaledSlack_twoCycle
    (hF : F.IsSmoothStronglyConvex) (m : Measure E) [m.IsAddHaarMeasure]
    (μ : Measure M) (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (φ : M → ℝ) (hφ : Measurable φ) {k : ℝ} (hk : k ≠ 0)
    (y : J → M) (hy : Function.Injective y)
    (π₀ π₁ : Measure (M × J))
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (Γ : Set (M × J)) (hΓ : MeasurableSet Γ)
    {a : ℝ≥0∞} (ha : a ≠ 0) (hcarried : ∀ᵐ z ∂a • (π₀ + π₁), z ∈ Γ) :
    let _instFinslerCountableRigidityMetric : MetricSpace M := F.metricSpace
    Reconstruction.IsTwoCycleMonotone
      (fun x j ↦ k * (dist x (y j) - φ (y j) + φ x)) Γ → π₀ = π₁ := by
  let _instFinslerCountableRigidityProofMetric : MetricSpace M := F.metricSpace
  change Reconstruction.IsTwoCycleMonotone
    (fun x j ↦ k * (dist x (y j) - φ (y j) + φ x)) Γ → π₀ = π₁
  intro hcycle
  apply hcycle.measure_eq_of_smul_add hΓ _ _ hsource₀ hsource₁ ha hcarried
  · intro j
    exact (((continuous_id.dist continuous_const).measurable.sub measurable_const).add
      hφ).const_mul k
  · intro i j hij
    exact hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim hchart
      hcomplete φ hk (fun heq ↦ hij (hy heq))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
