import OTSelector.Limit.FinslerPhysicalMeanDifferentiability
import OTSelector.Limit.FinslerSemidiscretePressureData

/-!
# Whole original empirical selection from actual local mean-pressure limits

The original physical populations produce one common potential. For every
supported probe, actual finite original allocations prove differentiability
of its limiting mean pressure. The existing whole-face selector then consumes
the actual pressure limits, with derivative and zero/lower premises internal.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Original physical data and actual local mean limits select the entire
original empirical optimal face. The common potential precedes every carrier,
original iid realization, pressure family and probe in the conclusion. -/
theorem exists_original_physical_empirical_selector_of_mean_limits
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), x ∈ B) :
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃ u : M → ℝ, LipschitzWith 1 u ∧
      ∀ (K : Set M) (hK : IsCompact K)
        (hμK : ∀ᵐ x ∂μ, x ∈ K) (hνK : ∀ᵐ y ∂ν, y ∈ K)
        (Renv : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Renv n)]
        (X Y : ∀ n, Fin (n + 1) → Ω n → M)
        (_hX : ∀ n i, Measurable (X n i)) (_hY : ∀ n i, Measurable (Y n i))
        (_hXi : ∀ n, iIndepFun (X n) (Renv n)) (_hYi : ∀ n, iIndepFun (Y n) (Renv n))
        (_hXlaw : ∀ n i, (Renv n).map (X n i) = μ)
        (_hYlaw : ∀ n i, (Renv n).map (Y n i) = ν)
        (_hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
          (fun sample i ↦ Y n i sample) (Renv n))
        (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (radius : ((K × K) →ᵇ ℝ) → ℝ),
        (∀ f, 0 < radius f) →
        (∀ (f : (K × K) →ᵇ ℝ) s, |s| < radius f →
          Tendsto (fun n ↦ finslerSemidiscreteMean F
            (⟨μ, inferInstance⟩ : ProbabilityMeasure M) (⟨ν, inferInstance⟩ : ProbabilityMeasure M)
            K hK hμK hνK u f s n) atTop (𝓝 (pressure f s))) →
        ∃ derivative : ((K × K) →ᵇ ℝ) → ℝ,
          (∀ f, HasDerivAt (pressure f) (derivative f) 0) ∧
          ∃! π : ProbabilityMeasure (M × M),
            (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
              (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
            (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (Renv n).real
              {sample | ∃ γ ∈ Pressure.empiricalOptimalFace
                (fun i ↦ X n i sample) (fun i ↦ Y n i sample), γ ∉ U}) atTop (𝓝 0)) ∧
            IsOptimalCoupling edist μ ν (π : Measure (M × M)) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hdim2 : 2 ≤ finrank ℝ E := by omega
  have hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₀.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₁.continuous.measurable hρ₁nonneg
      v hv hvolume
  obtain ⟨u, hu, hdiff⟩ := exists_original_physical_potential_mean_differentiability
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg
    v hv hvnonneg hvolume hA hB hAB hμ hν
  dsimp only
  refine ⟨u, hu, ?_⟩
  intro K hK hμK hνK Renv _hRenv X Y hX hY hXi hYi hXlaw hYlaw hXY
    pressure radius hradius hconv
  let μp : ProbabilityMeasure M := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure M := ⟨ν, inferInstance⟩
  have hd (f : (K × K) →ᵇ ℝ) : ∃ d : ℝ, HasDerivAt (pressure f) d 0 :=
    hdiff K hK hμK hνK f (pressure f) (hradius f)
      (fun s hs ↦ hconv f s (abs_lt.mpr hs))
  choose derivative hderiv using hd
  refine ⟨derivative, hderiv, ?_⟩
  exact existsUnique_selector_of_finsler_semidiscrete_convergence
    hF hcomplete m hdim μp νp hμchart hνchart K hK hμK hνK
    Renv X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
    pressure radius derivative hradius hconv hderiv

end OTSelector.Reconstruction
