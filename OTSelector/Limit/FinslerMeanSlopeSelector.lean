import OTSelector.Limit.FinslerSemidiscretePressureData
import OTSelector.Analysis.Calculus.LimitFromSecantSlopes

/-!
# Selector endpoint from mean convergence and finite-level tilt slopes

The differentiability premise of the Finsler pressure producer can be replaced
by the convergence of the one-sided secant slopes of the finite-sample
Dirichlet means.  For each fixed small tilt the right and left slopes converge
to slope functions, and those slope functions tend to the same number at zero.
This is the interface supplied by the cavity/two-cycle analysis; the present
module only converts it into the differentiable pressure triple.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- Pointwise mean convergence plus the finite-level one-sided slope limits
discharge all four pressure premises of the general Finsler selector endpoint. -/
theorem existsUnique_selector_of_finsler_mean_slope_convergence
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instMeanSlopePotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (positiveSlope negativeSlope : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hconv : ∀ f t, |t| < radius f →
      Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
        atTop (𝓝 (pressure f t)))
    (hpositive : ∀ (f : (K × K) →ᵇ ℝ) (h : ℝ), 0 < h → h < radius f →
      Tendsto (fun n ↦
        (finslerSemidiscreteMean F μ ν K hK hμ hν φ f h n -
          finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n) / h)
        atTop (𝓝 (positiveSlope f h)))
    (hnegative : ∀ (f : (K × K) →ᵇ ℝ) (h : ℝ), 0 < h → h < radius f →
      Tendsto (fun n ↦
        (finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n -
          finslerSemidiscreteMean F μ ν K hK hμ hν φ f (-h) n) / h)
        atTop (𝓝 (negativeSlope f h)))
    (hpositiveSlope : ∀ f : (K × K) →ᵇ ℝ,
      Tendsto (positiveSlope f) (𝓝[>] (0 : ℝ)) (𝓝 (derivative f)))
    (hnegativeSlope : ∀ f : (K × K) →ᵇ ℝ,
      Tendsto (negativeSlope f) (𝓝[>] (0 : ℝ)) (𝓝 (derivative f))) :
    let _instMeanSlopeSelectorMetric : MetricSpace M := F.metricSpace
    let _instMeanSlopeSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
      (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
        {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U}) atTop (𝓝 0)) ∧
      IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  have hderiv : ∀ f : (K × K) →ᵇ ℝ, HasDerivAt (pressure f) (derivative f) 0 := by
    intro f
    refine hasDerivAt_of_tendsto_mean_slope
      (J := fun n t ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
      (P := pressure f) (Dpos := positiveSlope f) (Dneg := negativeSlope f)
      (d := derivative f) (ε := radius f) (hradius f) ?_ ?_ ?_
      (hpositiveSlope f) (hnegativeSlope f)
    · intro t ht
      exact hconv f t ht
    · intro h hh hlt
      exact hpositive f h hh hlt
    · intro h hh hlt
      exact hnegative f h hh hlt
  exact existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ pressure radius derivative hradius hconv hderiv

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
