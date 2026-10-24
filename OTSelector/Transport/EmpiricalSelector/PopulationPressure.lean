import OTSelector.Reconstruction.OriginalIIDFinalValueFieldChosenClosed
import OTSelector.Reconstruction.FinslerOriginalFinalInputReadoutDerivative
import OTSelector.Probability.CanonicalIidSampling

/-! The population pressure and its derivative are constructed before any external sampling model. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open OTSelector.Geometry OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original geometry and the two populations produce the actual semidiscrete pressure limits,
with a common positive tilt interval for each probe and their derivative at zero.
The canonical iid experiment is internal; no sampling or pressure hypothesis is supplied. -/
theorem exists_original_population_semidiscrete_pressure
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
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    let μp := physicalSourceProbability ωM ρ₀
    let νp := physicalTargetProbability ωM ρ₁
    let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
    (let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u) ∧
    ∃ (pressure : FinalProbeSpace A B → ℝ → ℝ) (radius derivative : FinalProbeSpace A B → ℝ),
      (∀ f, 0 < radius f) ∧
      (∀ f, HasDerivAt (pressure f) (derivative f) 0) ∧
      (∀ f t, |t| < radius f →
        Tendsto (fun n ↦ finslerSemidiscreteMean F μp νp (A ∪ B) (hA.union hB)
          (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy) u f t n)
          atTop (𝓝 (pressure f t))) := by
  let μp := physicalSourceProbability ωM ρ₀
  let νp := physicalTargetProbability ωM ρ₁
  let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
    hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  have hclosed := chosenPopulationPotential_final_inputs_of_original_geometry
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμ hν (canonicalLaw μp νp) canonicalX canonicalY
    measurable_canonicalX measurable_canonicalY (iIndepFun_canonicalX μp νp)
    (iIndepFun_canonicalY μp νp) (canonicalLaw_map_canonicalX μp νp)
    (canonicalLaw_map_canonicalY μp νp) (indepFun_canonicalArrays μp νp)
  obtain ⟨a, Seed, κ, b, vP, gap, diameter, hκ, hu, _ha, _hb, _hbinv, _hhaar,
    _hmoments, _hgap, _hdist, _hsep, inputs, _hlower, _hupper⟩ := hclosed
  have hder := finslerReadoutTiltDerivative_of_finalInputs
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμ hν (canonicalLaw μp νp) canonicalX canonicalY
    measurable_canonicalX measurable_canonicalY (iIndepFun_canonicalX μp νp)
    (iIndepFun_canonicalY μp νp) (canonicalLaw_map_canonicalX μp νp)
    (canonicalLaw_map_canonicalY μp νp) (indepFun_canonicalArrays μp νp) inputs
  obtain ⟨derivative, hderivative⟩ := hder
  refine ⟨hu, inputs.pressureLower, inputs.radius, derivative, inputs.hradius, hderivative, ?_⟩
  have hμchart : ∀ old : M, (((μp : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact chartwise_ac_withDensity_of_volume_density ωM m
      hρ₀.continuous.measurable hρ₀nonneg v hv hvolume old
  have hνchart : ∀ old : M, (((νp : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact chartwise_ac_withDensity_of_volume_density ωM m
      hρ₁.continuous.measurable hρ₁nonneg v hv hvolume old
  intro f t ht
  apply tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
    hF hcomplete m (by omega) μp νp hμchart hνchart (A ∪ B) (hA.union hB)
    (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
    (canonicalLaw μp νp) canonicalX canonicalY
    measurable_canonicalX measurable_canonicalY (iIndepFun_canonicalX μp νp)
    (iIndepFun_canonicalY μp νp) (canonicalLaw_map_canonicalX μp νp)
    (canonicalLaw_map_canonicalY μp νp) (indepFun_canonicalArrays μp νp)
    u hu f t (inputs.pressureLower f t)
  · exact fun ε hε ↦ inputs.hprob f t ε ht hε
  · intro ε hε
    filter_upwards [inputs.hupper f t ε ht hε] with n hn
    rwa [← inputs.hvalue f t] at hn

end OTSelector.Reconstruction
