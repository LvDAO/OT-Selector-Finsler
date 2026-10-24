import OTSelector.Limit.FinslerSemidiscreteMeanSelector

/-!
# Pressure data supplied by pointwise semidiscrete mean convergence

The conditional selector endpoint takes a limiting pressure, its derivative at
zero, and four analytic premises.  This module shows that two inputs suffice:
pointwise convergence of the physical Dirichlet semidiscrete means on one common
tilt interval and differentiability of the limit at zero.  The one-sided lower
premise then follows from convergence and continuity of `max (·) 0`.

No pressure producer is asserted here; the remaining mathematical work is to
supply `pressure`, `radius`, `derivative` and `hconv`.
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

/-- The physical Dirichlet semidiscrete mean appearing in the selector endpoint. -/
noncomputable def finslerSemidiscreteMean
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (F : ContinuousFinslerNorm E M)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (φ : M → ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  let _instFinslerSemidiscreteMeanMetric : MetricSpace M := F.metricSpace
  let q : ℝ := (Module.finrank ℝ E : ℝ) - 1
  ∫ y : Fin (n + 1) → M, ∫ p,
    fullSemidiscreteValue (μ : Measure M) y (fun x y ↦
      ((n + 1 : ℕ) : ℝ) ^ (2 / q) * (dist x y - φ y + φ x) +
        t * f (supportProjection μ K hK.measurableSet hμ x,
          supportProjection ν K hK.measurableSet hν y)) p
      ∂dirichletOne n ∂Measure.pi (fun _ ↦ (ν : Measure M))

/-- Pointwise convergence of the semidiscrete means on one common interval and
differentiability of the limit at zero discharge all four pressure premises of
the general Finsler selector endpoint. -/
theorem existsUnique_selector_of_finsler_semidiscrete_convergence
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
      LipschitzWith 1 φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hconv : ∀ f t, |t| < radius f →
      Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
        atTop (𝓝 (pressure f t)))
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0) :
    let _instFinslerMeanSelectorMetric : MetricSpace M := F.metricSpace
    let _instFinslerMeanSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
      (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
        {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
          (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U}) atTop (𝓝 0)) ∧
      IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  let _instFinslerMeanSelectorMetric : MetricSpace M := F.metricSpace
  let _instFinslerMeanSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
  have hzero : ∀ f, Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f 0 n)
      atTop (𝓝 (pressure f 0)) := by
    intro f
    exact hconv f 0 (by simpa using hradius f)
  have hlower : ∀ f t, |t| < radius f →
      Tendsto (fun n ↦ max (pressure f t -
        finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) 0) atTop (𝓝 0) := by
    intro f t ht
    have hsub : Tendsto (fun n ↦ pressure f t -
        finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop
        (𝓝 (pressure f t - pressure f t)) :=
      (hconv f t ht).const_sub (pressure f t)
    have hzero0 : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have hmax := hsub.max hzero0
    simpa using hmax
  exact (existsUnique_selector_of_physical_semidiscrete_means
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ) pressure radius derivative hradius hderiv hzero hlower

/-- The single analytic producer sufficient for the general Finsler selector.
It packages a pressure triple, its differentiability, pointwise convergence of
the physical semidiscrete means on one common tilt interval, and the resulting
unique whole-face selector. -/
theorem existsUnique_selector_of_finsler_pressure_producer
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
      LipschitzWith 1 φ)
    (hprod : ∃ (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
        (radius derivative : ((K × K) →ᵇ ℝ) → ℝ),
      (∀ f, 0 < radius f) ∧
      (∀ f, HasDerivAt (pressure f) (derivative f) 0) ∧
      (∀ f t, |t| < radius f →
        Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
          atTop (𝓝 (pressure f t)))) :
    let _instFinslerMeanSelectorMetric : MetricSpace M := F.metricSpace
    let _instFinslerMeanSelectorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃ (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
      (radius derivative : ((K × K) →ᵇ ℝ) → ℝ),
      (∀ f, 0 < radius f) ∧
      (∀ f, HasDerivAt (pressure f) (derivative f) 0) ∧
      (∀ f t, |t| < radius f →
        Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n)
          atTop (𝓝 (pressure f t))) ∧
      ∃! π : ProbabilityMeasure (M × M),
        (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
          (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
        (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
          {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
            (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U}) atTop (𝓝 0)) ∧
        IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  obtain ⟨pressure, radius, derivative, hradius, hderiv, hconv⟩ := hprod
  refine ⟨pressure, radius, derivative, hradius, hderiv, hconv, ?_⟩
  exact existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ pressure radius derivative hradius hconv hderiv

set_option maxHeartbeats 1200000 in
/-- Convergence of the expected empirical supported pressure transfers to the
physical Dirichlet semidiscrete mean through the exact cavity identity. -/
theorem tendsto_finslerSemidiscreteMean_of_supportedPressure
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
    let _instFinslerPressureDataMetric : MetricSpace M := F.metricSpace
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (L : ℝ),
      Tendsto (fun n ↦ ∫ x,
        Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i x) (fun i ↦ Y n i x) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n)
        atTop (𝓝 L) →
      Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop (𝓝 L) := by
  let _inst : MetricSpace M := F.metricSpace
  have hdim2 : 2 ≤ Module.finrank ℝ E := by omega
  refine fun f t L h => ?_
  refine h.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  exact (hF.integral_supportedDistancePressure_eq_fullSemidiscreteValue
    (k := ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) m μ ν hdim2
    hμchart hνchart hcomplete K hK hμ hν (P n) (X n) (Y n) (hX n) (hY n)
    (hXi n) (hYi n) (hXlaw n) (hYlaw n) (hXY n) φ hφ.continuous
    (Real.rpow_pos_of_pos (by positivity) _) f t).2

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
