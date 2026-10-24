import OTSelector.Geometry.FinslerSemidiscretePressure
import OTSelector.Limit.SupportedEmpiricalSelector

/-!
# The selector's original supported pressure has the physical coupling formula

The compact carrier probe is extended only by the same measurable retractions
already present in `supportedDistancePressure`. The cost remains the original
ambient Finsler distance. Every analytic and atomlessness prerequisite of the
mean identity is derived from the original geometric and population inputs.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Ω] {F : ContinuousFinslerNorm E M}

/-- The very pressure consumed by the supported whole-face selector equals the
expected full physical semidiscrete coupling minimum, for every carrier probe. -/
theorem integral_supportedDistancePressure_eq_fullSemidiscreteValue
    (hF : F.IsSmoothStronglyConvex) (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : ProbabilityMeasure M) (hdim : 2 ≤ Module.finrank ℝ E)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = (μ : Measure M))
    (hYlaw : ∀ i, P.map (Y i) = (ν : Measure M))
    (hXY : IndepFun (fun sample i ↦ X i sample) (fun sample i ↦ Y i sample) P)
    (φ : M → ℝ) (hφ : Continuous φ) {k : ℝ} (hk : 0 < k) :
    let _instSupportedMeanMetric : MetricSpace M := F.metricSpace
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      let c : M → M → ℝ := fun x y ↦ k * (dist x y - φ y + φ x) +
        t * f (supportProjection μ K hK.measurableSet hμ x,
          supportProjection ν K hK.measurableSet hν y)
      Integrable (fun y : Fin (n + 1) → M ↦
        ∫ p, fullSemidiscreteValue (μ : Measure M) y c p ∂dirichletOne n)
        (Measure.pi fun _ ↦ (ν : Measure M)) ∧
      (∫ sample, Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i ↦ X i sample) (fun i ↦ Y i sample) φ k f t ∂P) =
        ∫ y : Fin (n + 1) → M, ∫ p,
          fullSemidiscreteValue (μ : Measure M) y c p ∂dirichletOne n
            ∂Measure.pi (fun _ ↦ (ν : Measure M)) := by
  let _instSupportedMeanProofMetric : MetricSpace M := F.metricSpace
  let _instSupportedMeanProper : ProperSpace M := F.properSpace_of_complete hcomplete
  dsimp only
  intro f t
  let g : M → M → ℝ := fun x y ↦ f
    (supportProjection μ K hK.measurableSet hμ x, supportProjection ν K hK.measurableSet hν y)
  have hg : Measurable (Function.uncurry g) :=
    f.continuous.measurable.comp ((measurable_supportProjection μ K hK.measurableSet hμ).prodMap
      (measurable_supportProjection ν K hK.measurableSet hν))
  have hbound (x y : M) : |g x y| ≤ (‖f‖₊ : ℝ) := f.norm_coe_le_norm _
  have h := hF.integral_original_scaledSlackPressure_eq_fullSemidiscreteValue m
    (μ : Measure M) (ν : Measure M) hdim hμchart hνchart hcomplete hK hK hμ hν
    P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ hk g hg ‖f‖₊ hbound t
  exact h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
