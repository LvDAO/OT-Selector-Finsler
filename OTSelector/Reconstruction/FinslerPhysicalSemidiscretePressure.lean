import OTSelector.Geometry.FinslerSemidiscretePressure
import OTSelector.Geometry.Manifold.ChartPopulationAbsoluteContinuity

/-!
# The physical Finsler input produces the original semidiscrete pressure identity

The original physical densities and actual chart-volume formula supply both
chartwise absolute continuity hypotheses. The original compact supports supply
cost integrability. Thus the full physical coupling formula needs no independent
atomlessness, target-distinctness or chart-density probability oracle.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Ω] {F : ContinuousFinslerNorm E M}

/-- Original continuous physical probability densities yield the exact iid mean formula.
In particular, this applies to the manuscript's arbitrary nonnegative Lipschitz densities. -/
theorem integral_physical_scaledSlackPressure_eq_fullSemidiscreteValue
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    (hρ₀ : Continuous ρ₀) (hρ₁ : Continuous ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), x ∈ B)
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))
    (hYlaw : ∀ i, P.map (Y i) = ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))
    (hXY : IndepFun (fun sample i ↦ X i sample) (fun sample i ↦ Y i sample) P)
    (φ : M → ℝ) (hφ : Continuous φ) {k : ℝ} (hk : 0 < k)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let _instPhysicalMeanPressureMetric : MetricSpace M := F.metricSpace
    Integrable (fun y : Fin (n + 1) → M ↦ ∫ p,
      fullSemidiscreteValue μ y
        (fun x y ↦ k * (dist x y - φ y + φ x) + t * g x y) p ∂dirichletOne n)
      (Measure.pi fun _ ↦ ν) ∧
    (∫ sample, perturbedAssignmentValue
      (fun i j ↦ k * (dist (X i sample) (Y j sample) - φ (Y j sample) + φ (X i sample)))
      (fun i j ↦ g (X i sample) (Y j sample)) t / (n + 1 : ℕ) ∂P) =
      ∫ y : Fin (n + 1) → M, ∫ p,
        fullSemidiscreteValue μ y
          (fun x y ↦ k * (dist x y - φ y + φ x) + t * g x y) p
          ∂dirichletOne n ∂Measure.pi (fun _ ↦ ν) := by
  exact hF.integral_original_scaledSlackPressure_eq_fullSemidiscreteValue m
    (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))
    (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))) hdim
    (chartwise_ac_withDensity_of_volume_density ωM m hρ₀.measurable hρ₀nonneg v hv hvolume)
    (chartwise_ac_withDensity_of_volume_density ωM m hρ₁.measurable hρ₁nonneg v hv hvolume)
    hcomplete hA hB hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ hk g hg G hbound t

end OTSelector.Reconstruction
