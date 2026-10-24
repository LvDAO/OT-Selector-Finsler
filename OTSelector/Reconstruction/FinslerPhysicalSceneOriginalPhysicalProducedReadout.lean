import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationProducedReadoutFace
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalCanonicalSceneScale
import OTSelector.Reconstruction.FinslerPopulationMomentAtlas
import OTSelector.Geometry.FinslerPressureAssumptionAdapters

/-!
# Original physical densities produce complete vanishing probe gaps

One original potential is chosen before the tilt probe. Its original measured
atlas supplies all conditional and core data internally, and the canonical
physical scale is fixed by the original dimension and sample size.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
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

/-- Original Lipschitz physical densities produce a common calibrated potential
and actual opposite global optimizers with vanishing complete continuous probe
gaps. No conditional, core, calibration, family, energy or weak-law input is given. -/
theorem exists_original_physical_opposite_families_continuous_probe_gap_curry_zero
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
    let scale := physicalSceneCanonicalHaarScale (finrank ℝ E - 1)
    let _inst : MetricSpace M := F.metricSpace
    ∃ u : M → ℝ, LipschitzWith 1 u ∧
      ∀ (probe : M → M → ℝ) (G : ℝ≥0), Measurable (Function.uncurry probe) →
        (∀ x y, |probe x y| ≤ G) →
    ∃ t : ℕ → ℝ,
    ∃ ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ,
      StrictAnti t ∧ (∀ ℓ, 0 < t ℓ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ ℓ n j, Measurable (fun z :
        ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j)) ∧
      (∀ ℓ n j, Measurable (fun z :
        ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j)) ∧
      (∀ ℓ n,
        ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
            scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
              t ℓ * probe x (w.1 j)) (ap ℓ n w) ∧
          IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
            scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
              (-t ℓ) * probe x (w.1 j)) (am ℓ n w)) ∧
    ∀ f : (M × M) →ᵇ ℝ,
      (∀ ℓ n, Integrable (fun w ↦
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w|)
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ∧
      Tendsto (fun z : ℕ × ℕ ↦ ∫ w,
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap z.1 z.2) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am z.1 z.2) (fun w ↦ w.1) w|
        ∂((Measure.pi (fun _ : Fin (z.2 + 1) ↦ ν)).prod (dirichletOne z.2)))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) ∧
      Tendsto (fun z : ℕ × ℕ ↦ ∫⁻ w, ENNReal.ofReal
        |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (ap z.1 z.2) (fun w ↦ w.1) w) -
          ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ (am z.1 z.2) (fun w ↦ w.1) w|
        ∂((Measure.pi (fun _ : Fin (z.2 + 1) ↦ ν)).prod (dirichletOne z.2)))
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let scale := physicalSceneCanonicalHaarScale (finrank ℝ E - 1)
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  have hqdim : 0 < finrank ℝ E - 1 := by omega
  have hscalePos := physicalSceneCanonicalHaarScale_pos (finrank ℝ E - 1)
  have hscale := tendsto_physicalSceneCanonicalHaarScale (finrank ℝ E - 1) hqdim
  have hnormalization := physicalSceneCanonicalHaarScale_pow (finrank ℝ E - 1) hqdim
  have hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₀.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₁.continuous.measurable hρ₁nonneg
      v hv hvolume
  obtain ⟨u, a, hu, _hN, hμreg, hνreg, ha, hinj, horder, hbalance, hface,
      P, κ, b, _hcover, _hμcover, _hνcover, hκ, _hprod, _hb, _hbinv, _hwindow,
      hμlaw, hνlaw, _hμfull, _hνfull, _hμseed, _hνseed, _hsupport, _hcomparison,
      hrecovery, _hcompact, _hfinite, _hpiece, _hpressure, _hcontinuous,
      hhaar, _hlocal, _hsep, _hmoment⟩ :=
    exists_finsler_lipschitz_population_moment_atlas hF hcomplete m ωM ρ₀ ρ₁ hρ₀ hρ₁
      hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  let _instSigma : ∀ j, SigmaFinite (κ j) := fun j ↦ by
    let _instHaar : (κ j).IsAddHaarMeasure := hκ j
    infer_instance
  dsimp only
  refine ⟨u, hu, ?_⟩
  intro probe G hprobe hprobeBound
  exact exists_originalAllocation_opposite_families_continuous_probe_gap_curry_zero_of_original_face
    (P := P) (a := a) (κ := κ) (b := b) (r := 1)
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart 1
    scale hscalePos hscale hnormalization probe hprobe G hprobeBound
    hμlaw hνlaw hA hB hAB hμreg hνreg hκ hbalance (hhaar 1) hrecovery hface
    (ae_iff.mp hμ) (ae_iff.mp hν) (by norm_num)

end OTSelector.Reconstruction
