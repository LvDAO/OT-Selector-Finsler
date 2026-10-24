import OTSelector.Limit.FinslerProducedMeanDifferentiability
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalPhysicalProducedReadout

/-!
# Original physical populations have differentiable limiting mean pressures

One common original potential is produced from the original physical densities.
For every supported selector probe, its actual opposite original allocations
and complete gap comparison are internal. The remaining analytic premise is
pointwise convergence of the actual physical semidiscrete means.
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

/-- The same potential works for every supported original selector probe.
Actual finite original allocation families and all readout comparison inputs
are produced internally; only the physical pressure limit remains conditional. -/
theorem exists_original_physical_potential_mean_differentiability
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
    ∃ u : M → ℝ, LipschitzWith 1 u ∧
      ∀ (K : Set M) (hK : IsCompact K)
        (hμK : ∀ᵐ x ∂μ, x ∈ K) (hνK : ∀ᵐ y ∂ν, y ∈ K)
        (f : (K × K) →ᵇ ℝ) (pressure : ℝ → ℝ) {ε : ℝ}, 0 < ε →
        (∀ s ∈ Ioo (-ε) ε,
          Tendsto (fun n ↦ finslerSemidiscreteMean F
            (⟨μ, inferInstance⟩ : ProbabilityMeasure M) (⟨ν, inferInstance⟩ : ProbabilityMeasure M)
            K hK hμK hνK u f s n) atTop (𝓝 (pressure s))) →
        ∃ d : ℝ, HasDerivAt pressure d 0 := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let scale := physicalSceneCanonicalHaarScale (finrank ℝ E - 1)
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  have hdim2 : 2 ≤ finrank ℝ E := by omega
  have hqdim : 0 < finrank ℝ E - 1 := by omega
  have hscalePos := physicalSceneCanonicalHaarScale_pos (finrank ℝ E - 1)
  have hnormalization := physicalSceneCanonicalHaarScale_pow (finrank ℝ E - 1) hqdim
  have hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₀.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₁.continuous.measurable hρ₁nonneg
      v hv hvolume
  obtain ⟨u, hu, hproduced⟩ :=
    exists_original_physical_opposite_families_continuous_probe_gap_curry_zero
      hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg
      v hv hvnonneg hvolume hA hB hAB hμ hν
  dsimp only
  refine ⟨u, hu, ?_⟩
  intro K hK hμK hνK f pressure ε hε hpt
  let μp : ProbabilityMeasure M := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure M := ⟨ν, inferInstance⟩
  let probe : M → M → ℝ := finslerCarrierProbe μp νp K hK.measurableSet hμK hνK f
  have hprobe : Measurable (Function.uncurry probe) :=
    f.continuous.measurable.comp
      (((measurable_supportProjection μp K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection νp K hK.measurableSet hνK).comp measurable_snd))
  have hprobeBound (x y : M) : |probe x y| ≤ (‖f‖₊ : ℝ) := f.norm_coe_le_norm _
  obtain ⟨t, ap, am, _htAnti, htPos, htLim, hpm, hmm, hopt, hgap⟩ :=
    hproduced probe ‖f‖₊ hprobe hprobeBound
  exact exists_hasDerivAt_finslerSemidiscreteMean_of_produced_original_allocations
    hF hcomplete hu hdim2 m hμchart hνchart scale hscalePos hnormalization
    K hK hμK hνK f t htPos htLim ap am hpm hmm hopt hgap pressure hε hpt

end OTSelector.Reconstruction
