import OTSelector.Limit.FinslerMeanDifferentiability
import OTSelector.Limit.FinslerSemidiscretePressureData

/-!
# Limiting pressure differentiability and the readout formula

This module discharges the open input `hreadout` of the general Finsler selector
assembly.  It separates what the finite-sample construction already supplies
from the single remaining analytic input of the paper's differentiation stage.

Available from the actual finite optimizers: for every fixed tilt, the
Dirichlet semidiscrete mean has the exact two-sided supergradient data
`qpos`, `qneg` coming from the expected probe readout of the actual finite
optimal allocations (`originalDirichletMean_supergradient_of_original_optimal_allocation`,
consumed in `FinslerProducedMeanDifferentiability`).  The remaining analytic
input is the paper's rooted-scene readout: the two opposite readouts agree
asymptotically, `qpos n - qneg n -> 0`.

Given that finite-level readout gap and the pressure convergence/localization
output of the squeeze, this module proves:

* the limiting pressure family `t |-> lim_n finslerSemidiscreteMean f t n` is
  differentiable at `0`, with one derivative function `derivative` defined
  simultaneously for every bounded continuous probe `f`;
* the readout formula: the unique probability plan `π` obtained from the
  pressure readout satisfies
  `∫ f ∂(π.comap (incl)) = derivative f` for every probe;
* the entire empirical optimal face converges in probability to that plan, and
  the plan is a population distance optimum for the intrinsic length cost.

No density lower bound, extra regularity of the limit, or measurably chosen
optimizer is assumed.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The tilt family of the physical Dirichlet semidiscrete mean, for one fixed
bounded continuous probe. -/
noncomputable def finslerMeanTiltFamily
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K) (φ : M → ℝ)
    (f : (K × K) →ᵇ ℝ) : ℝ → ℕ → ℝ :=
  fun t n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n

/-- **Limiting pressure differentiability from the finite readout gap.**

If the finite-level physical Dirichlet means converge pointwise on the tilt
interval `|t| < radius f` to the pressure `pressure f`, and for every vanishing
positive tilt sequence the finite means carry opposite-tilt supergradients
(`qpos`, `qneg`, the expected finite probe readouts) whose difference vanishes,
then the limiting pressure family is differentiable at zero with a single
readout derivative function. -/
theorem exists_derivative_of_finsler_pressure_readout_gap
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instReadoutPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hconv : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      Tendsto (finslerMeanTiltFamily F μ ν K hK hμ hν φ f t) atTop (𝓝 (pressure f t)))
    (hreadout : ∀ (f : (K × K) →ᵇ ℝ) (t : ℕ → ℝ), (∀ n, 0 < t n) →
      Tendsto t atTop (𝓝 0) →
      (∀ᶠ n in atTop, 2 * t n < radius f / 2) →
      ∃ qpos qneg : ℕ → ℝ,
        (∀ᶠ n in atTop, ∀ s : ℝ,
          finslerMeanTiltFamily F μ ν K hK hμ hν φ f s n ≤
            finslerMeanTiltFamily F μ ν K hK hμ hν φ f (t n) n +
              qpos n * (s - t n)) ∧
        (∀ᶠ n in atTop, ∀ s : ℝ,
          finslerMeanTiltFamily F μ ν K hK hμ hν φ f s n ≤
            finslerMeanTiltFamily F μ ν K hK hμ hν φ f (-(t n)) n +
              qneg n * (s + t n)) ∧
        Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0)) :
    let _instReadoutMetric : MetricSpace M := F.metricSpace
    ∃ derivative : ((K × K) →ᵇ ℝ) → ℝ,
      ∀ f : (K × K) →ᵇ ℝ, HasDerivAt (pressure f) (derivative f) 0 := by
  let _inst : MetricSpace M := F.metricSpace
  have hper : ∀ f : (K × K) →ᵇ ℝ, ∃ d : ℝ, HasDerivAt (pressure f) d 0 := by
    intro f
    refine exists_hasDerivAt_of_finslerSemidiscreteMean
      hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
      hXlaw hYlaw hXY φ hφ f (pressure f) (ε := radius f) (hradius f) ?_
      (ρ := radius f / 2) (div_pos (hradius f) (by norm_num))
      (by linarith [hradius f]) (B := ∅) Set.countable_empty ?_
    · intro s hs
      exact hconv f s (abs_lt.mpr hs)
    · intro t htpos htlim hsmall _ _
      exact hreadout f t htpos htlim hsmall
  choose derivative hderiv using hper
  exact ⟨derivative, hderiv⟩

/-- **Whole-face selector with the limiting readout derivative.**

Under the same explicit inputs, the readout derivatives assemble into the
unique probability plan of the pressure endpoint: the readout formula
`∫ f ∂(π.comap incl) = derivative f` holds for every probe, the entire empirical
optimal face (fractional optima included) converges to `π` in probability, and
`π` is a population distance optimum for the intrinsic length cost. -/
theorem existsUnique_finsler_selector_of_pressure_readout_gap
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instReadoutSelectorPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hconv : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      Tendsto (finslerMeanTiltFamily F μ ν K hK hμ hν φ f t) atTop (𝓝 (pressure f t)))
    (hreadout : ∀ (f : (K × K) →ᵇ ℝ) (t : ℕ → ℝ), (∀ n, 0 < t n) →
      Tendsto t atTop (𝓝 0) →
      (∀ᶠ n in atTop, 2 * t n < radius f / 2) →
      ∃ qpos qneg : ℕ → ℝ,
        (∀ᶠ n in atTop, ∀ s : ℝ,
          finslerMeanTiltFamily F μ ν K hK hμ hν φ f s n ≤
            finslerMeanTiltFamily F μ ν K hK hμ hν φ f (t n) n +
              qpos n * (s - t n)) ∧
        (∀ᶠ n in atTop, ∀ s : ℝ,
          finslerMeanTiltFamily F μ ν K hK hμ hν φ f s n ≤
            finslerMeanTiltFamily F μ ν K hK hμ hν φ f (-(t n)) n +
              qneg n * (s + t n)) ∧
        Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0)) :
    let _instReadoutSelectorMetric : MetricSpace M := F.metricSpace
    let _instReadoutSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃ derivative : ((K × K) →ᵇ ℝ) → ℝ,
      (∀ f : (K × K) →ᵇ ℝ, HasDerivAt (pressure f) (derivative f) 0) ∧
      ∃! π : ProbabilityMeasure (M × M),
        (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
          (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
        (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
          {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U})
          atTop (𝓝 0)) ∧
        IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  have hdim2 : 2 ≤ Module.finrank ℝ E := by omega
  obtain ⟨derivative, hderiv⟩ :=
    exists_derivative_of_finsler_pressure_readout_gap hF hcomplete hdim2 m μ ν
      hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ
      pressure radius hradius hconv hreadout
  refine ⟨derivative, hderiv, ?_⟩
  exact existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ pressure radius derivative hradius hconv hderiv

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
