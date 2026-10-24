import OTSelector.Geometry.Finsler.SlackAtomlessness
import OTSelector.Probability.CavitySemidiscretePressurePhysical
import OTSelector.MeasureTheory.CompactSupportedIntegrability

/-!
# Original Finsler distance pressures equal physical semidiscrete mean values

Completeness and smooth strong convexity supply the original length metric and
atomless distinct-target distance differences. Chartwise absolute continuity
supplies diffuse targets. Compact original supports supply cost integrability.
The finite iid identity therefore applies to every positive distance-slack scale
and every bounded measurable paired perturbation, without extra probability
or geometric regularity assumptions.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Ω] {F : ContinuousFinslerNorm E M}

/-- The actual original two-color pressure has the full physical coupling formula.
Atomlessness, distinct targets and cost integrability are derived internally. -/
theorem integral_original_scaledSlackPressure_eq_fullSemidiscreteValue
    (hF : F.IsSmoothStronglyConvex) (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ i, P.map (Y i) = ν)
    (hXY : IndepFun (fun sample i ↦ X i sample) (fun sample i ↦ Y i sample) P)
    (φ : M → ℝ) (hφ : Continuous φ) {k : ℝ} (hk : 0 < k)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    let _instOriginalMeanPressureMetric : MetricSpace M := F.metricSpace
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
  let _instOriginalMeanPressureProofMetric : MetricSpace M := F.metricSpace
  let _instOriginalMeanPressureProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instOriginalMeanPressureBorel : StandardBorelSpace M := inferInstance
  let _instOriginalMeanPressureDiffuse : NullSingletonClass ν :=
    nullSingletonClass_of_chartwise_ac m ν hdim hνchart
  let c : M → M → ℝ := fun x y ↦ k * (dist x y - φ y + φ x)
  have hc : Continuous (Function.uncurry c) :=
    (((continuous_fst.dist continuous_snd).sub (hφ.comp continuous_snd)).add
      (hφ.comp continuous_fst)).const_mul k
  have hci : Integrable (Function.uncurry c) (μ.prod ν) :=
    integrable_continuous_of_compact_carriers μ ν hA hB hμ hν hc
  exact integral_original_bipartite_pressure_eq_fullSemidiscreteValue P μ ν X Y
    hX hY hXi hYi hXlaw hYlaw hXY c g hc.measurable hci hg
    (fun y z hyz ↦ hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim hμchart
      hcomplete φ hk.ne' hyz) G hbound t

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
