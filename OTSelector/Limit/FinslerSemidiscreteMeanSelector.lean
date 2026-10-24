import OTSelector.Geometry.FinslerSupportedSemidiscretePressure
import OTSelector.Limit.SupportedMeanPressureSelector

/-!
# General Finsler whole-face selection from physical semidiscrete mean limits

For dimension at least six, the original iid pressure is both the full physical
semidiscrete mean value and concentrated about that value. The remaining analytic
input is exactly the central and one-sided tilted limit of these actual coupling
primal means, together with differentiability. No separate atomlessness,
concentration or compactness of the ambient manifold is assumed.
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

/-- Physical semidiscrete mean limits select the entire original empirical optimal face.
The dimension is the actual manifold model dimension, and the cost is its original length. -/
theorem existsUnique_selector_of_physical_semidiscrete_means
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
    (hφ : let _instMeanSelectorPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ) :
    let _instFinslerMeanSelectorMetric : MetricSpace M := F.metricSpace
    let _instFinslerMeanSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let q : ℝ := (Module.finrank ℝ E : ℝ) - 1
    let J : ((K × K) →ᵇ ℝ) → ℝ → ℕ → ℝ := fun f t n ↦
      ∫ y : Fin (n + 1) → M, ∫ p,
        fullSemidiscreteValue (μ : Measure M) y (fun x y ↦
          ((n + 1 : ℕ) : ℝ) ^ (2 / q) * (dist x y - φ y + φ x) +
            t * f (supportProjection μ K hK.measurableSet hμ x,
              supportProjection ν K hK.measurableSet hν y)) p
          ∂dirichletOne n ∂Measure.pi (fun _ ↦ (ν : Measure M))
    ∀ (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
      (radius derivative : ((K × K) →ᵇ ℝ) → ℝ),
      (∀ f, 0 < radius f) → (∀ f, HasDerivAt (pressure f) (derivative f) 0) →
      (∀ f, Tendsto (J f 0) atTop (𝓝 (pressure f 0))) →
      (∀ f t, |t| < radius f → Tendsto (fun n ↦ max (pressure f t - J f t n) 0)
        atTop (𝓝 0)) →
      ∃! π : ProbabilityMeasure (M × M),
        (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
          (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
        (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
          {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U}) atTop (𝓝 0)) ∧
        IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  let _instFinslerMeanSelectorProofMetric : MetricSpace M := F.metricSpace
  let _instFinslerMeanSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
  dsimp only
  intro pressure radius derivative hradius hderiv hzero hlower
  have hdim2 : 2 ≤ Module.finrank ℝ E := le_trans (by norm_num) hdim
  have hq : (4 : ℝ) < (Module.finrank ℝ E : ℝ) - 1 := by
    have hd : (6 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    linarith
  have heq (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) :=
    (hF.integral_supportedDistancePressure_eq_fullSemidiscreteValue
      (k := ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) m μ ν hdim2
      hμchart hνchart hcomplete K hK hμ hν (P n) (X n) (Y n) (hX n) (hY n)
      (hXi n) (hYi n) (hXlaw n) (hYlaw n) (hXY n) φ hφ.continuous
      (Real.rpow_pos_of_pos (by positivity) (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t).2
  apply Pressure.existsUnique_supported_empirical_selector_of_iid_mean_pressure
    P X Y μ ν K hK hμ hν hX hY hXi hYi hXlaw hYlaw hXY φ hφ
    ((Module.finrank ℝ E : ℝ) - 1) hq pressure radius derivative hradius hderiv
  · intro f
    convert hzero f using 1
    funext n
    exact heq f 0 n
  · intro f t ht
    convert hlower f t ht using 1
    funext n
    rw [heq f t n]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
