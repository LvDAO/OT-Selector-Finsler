import OTSelector.Limit.FinslerMeanTiltConcavity
import OTSelector.Analysis.Convex.PressureDifferentiabilityAssembly

/-!
# Differentiability of the physical semidiscrete mean from the tilt comparison

This module assembles the deterministic part of the paper's differentiability
proof for the physical Dirichlet semidiscrete mean:

* concavity of every finite-sample mean in the tilt is proved unconditionally
  (`concaveOn_finslerSemidiscreteMean_tilt`);
* local uniform convergence follows from pointwise convergence by concavity;
* the tilt sequence is chosen to make the uniform error `o(t)` and to avoid a
  countable exceptional set of tilts;
* the paper's finite-level supergradient squeeze then gives differentiability.

The single remaining stochastic input is stated explicitly as `hsup`: for tilt
sequences avoiding the exceptional set, opposite-tilt supergradients exist and
their probe costs differ by a vanishing amount.  The existence of the
supergradients themselves is discharged in `FinslerMeanTiltSupergradient`; the
vanishing difference is the paper's two-cycle rigidity and probe readout step.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric Filter
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false

/-- **Differentiability of the physical semidiscrete mean.**  Pointwise
convergence on a neighborhood of zero, together with the cavity input `hsup` on
opposite-tilt supergradients, makes the limit differentiable at zero. -/
theorem exists_hasDerivAt_of_finslerSemidiscreteMean
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
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
    (hφ : let _instFinslerMeanDiffMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ)
    (pressure : ℝ → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hpt : ∀ t ∈ Ioo (-ε) ε,
      Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
        atTop (𝓝 (pressure t)))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ < ε)
    (B : Set ℝ) (hB : B.Countable)
    (hsup : ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) →
      (∀ᶠ n in atTop, 2 * t n < ρ) →
      (∀ n, t n ∉ B) → (∀ n, -t n ∉ B) →
      ∃ qpos qneg : ℕ → ℝ,
        (∀ᶠ n in atTop, ∀ s,
          finslerSemidiscreteMean F μ ν K hK hμ hν φ f s n ≤
            finslerSemidiscreteMean F μ ν K hK hμ hν φ f (t n) n + qpos n * (s - t n)) ∧
        (∀ᶠ n in atTop, ∀ s,
          finslerSemidiscreteMean F μ ν K hK hμ hν φ f s n ≤
            finslerSemidiscreteMean F μ ν K hK hμ hν φ f (-(t n)) n + qneg n * (s + t n)) ∧
        Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0)) :
    let _instFinslerMeanDiffMetric : MetricSpace M := F.metricSpace
    ∃ d : ℝ, HasDerivAt pressure d 0 := by
  let _inst : MetricSpace M := F.metricSpace
  let pn : ℕ → ℝ → ℝ := fun n t ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n
  have hconc : ∀ n, ConcaveOn ℝ (Ioo (-ε) ε) (pn n) := by
    intro n
    change ConcaveOn ℝ (Ioo (-ε) ε)
      (fun t ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
    have h := concaveOn_finslerSemidiscreteMean_tilt hF m μ ν hdim hμchart hνchart hcomplete
      K hK hμ hν (P n) (X n) (Y n) (hX n) (hY n) (hXi n) (hYi n)
      (hXlaw n) (hYlaw n) (hXY n) φ hφ f
    exact h.subset (subset_univ _) (convex_Ioo (-ε) ε)
  have hsup' : ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) →
      (∀ᶠ n in atTop, 2 * t n < ρ) →
      (∀ n, t n ∉ B) → (∀ n, -t n ∉ B) →
      ∃ qpos qneg : ℕ → ℝ,
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (t n) + qpos n * (s - t n)) ∧
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (-(t n)) + qneg n * (s + t n)) ∧
        Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0) := hsup
  exact hasDerivAt_of_concave_pointwise_tendsto_of_supergradient_diff_avoiding
    hε hconc hpt hρ0 hρε B hB hsup'

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
