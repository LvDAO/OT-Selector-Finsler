import OTSelector.Limit.FinslerPhysicalMeanDifferentiability

/-!
# The vanishing finite readout gap of the original physical Dirichlet means

This module exposes the paper's two-cycle / rooted-scene readout step as an
explicit theorem.  For the original physical populations it produces a common
calibrated potential, one vanishing positive tilt sequence, both actual
jointly measurable opposite-tilt optimal allocation families, and the expected
actual supported-probe readouts

`qpos n`, `qneg n`

of those families.  It proves, internally, that

* `qpos`, `qneg` are the expected actual finite readout integrals of the
  allocation families (expected-readout identification);
* they are opposite-tilt supergradients of the physical Dirichlet semidiscrete
  means (supergradient existence, via the actual finite optimality);
* their difference vanishes: `qpos - qneg -> 0` (curried in the tilt index and
  the sample size).

The first two items are the finite-sample exact readout derivative of the
paper's differentiation stage; the third is the two-cycle rigidity input.  All
of it is derived from the original compactly supported physical data through
the actual original optimal face; the only inputs are the paper's density,
volume and compact-support hypotheses.  The potential is produced before the
probe, so the readouts and the gap are literal.

As a consequence the differentiability premise of the general selector
assembly is discharged at the physical level: pointwise convergence of the
physical semidiscrete means alone yields one derivative function for every
probe.
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
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original Dirichlet environment of sample size `n`: target cloud times
Dirichlet weights. -/
noncomputable def originalReadoutEnvironment (ν : Measure M) (n : ℕ) :
    Measure ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) :=
  (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)

/-- The expected actual supported-probe readout of an allocation family. -/
noncomputable def originalReadoutIntegral (μ ν : Measure M) {n : ℕ}
    (probe : M × M → ℝ)
    (alloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ) : ℝ :=
  ∫ w, ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ alloc Prod.fst w
    ∂originalReadoutEnvironment ν n

variable {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Vanishing finite readout gap.**  Original physical populations produce a
common calibrated potential `u`, a strictly decreasing positive tilt sequence
`t -> 0`, both actual measurable optimal allocation families at `±t`, and the
expected actual readout `qpos`, `qneg` of those families, such that:
the families are optimal at the opposite tilts; `qpos`, `qneg` are the
readout integrals; they are supergradients of the physical Dirichlet means at
`t ℓ` and `-t ℓ`; and `qpos - qneg` vanishes curried in `(ℓ, n)`. -/
theorem exists_vanishing_originalDirichletMean_readout_gap
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [hμprob : IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [hνprob : IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hνB : ∀ᵐ y ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), y ∈ B)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ K)
    (hνK : ∀ᵐ y ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), y ∈ K)
    (f : (K × K) →ᵇ ℝ) :
    let μc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let νc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let μp : ProbabilityMeasure M := ⟨μc, hμprob⟩
    let νp : ProbabilityMeasure M := ⟨νc, hνprob⟩
    let _inst : MetricSpace M := F.metricSpace
    ∃ u : M → ℝ, LipschitzWith 1 u ∧
    ∃ t : ℕ → ℝ, ∃ ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ,
      StrictAnti t ∧ (∀ ℓ, 0 < t ℓ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ ℓ n j, Measurable (fun z :
        ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j)) ∧
      (∀ ℓ n j, Measurable (fun z :
        ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j)) ∧
      (∀ ℓ n,
        ∀ᵐ w ∂originalReadoutEnvironment νc n,
          IsOptimalSemidiscreteAllocation μc w.2 (fun x j ↦
            finslerMeanScale E n * ((F.lengthEDist x (w.1 j)).toReal -
              u (w.1 j) + u x) + t ℓ *
                finslerCarrierProbe μp νp K hK.measurableSet hμK hνK f x (w.1 j))
            (ap ℓ n w) ∧
          IsOptimalSemidiscreteAllocation μc w.2 (fun x j ↦
            finslerMeanScale E n * ((F.lengthEDist x (w.1 j)).toReal -
              u (w.1 j) + u x) + (-t ℓ) *
                finslerCarrierProbe μp νp K hK.measurableSet hμK hνK f x (w.1 j))
            (am ℓ n w)) ∧
    ∃ qpos qneg : ℕ → ℕ → ℝ,
      (∀ ℓ n s, finslerSemidiscreteMean F μp νp K hK hμK hνK u f s n ≤
        finslerSemidiscreteMean F μp νp K hK hμK hνK u f (t ℓ) n +
          qpos ℓ n * (s - t ℓ)) ∧
      (∀ ℓ n s, finslerSemidiscreteMean F μp νp K hK hμK hνK u f s n ≤
        finslerSemidiscreteMean F μp νp K hK hμK hνK u f (-(t ℓ)) n +
          qneg ℓ n * (s + t ℓ)) ∧
      (∀ ℓ n, qpos ℓ n = originalReadoutIntegral μc νc
        (Function.uncurry (finslerCarrierProbe μp νp K hK.measurableSet hμK hνK f))
        (ap ℓ n)) ∧
      (∀ ℓ n, qneg ℓ n = originalReadoutIntegral μc νc
        (Function.uncurry (finslerCarrierProbe μp νp K hK.measurableSet hμK hνK f))
        (am ℓ n)) ∧
      Tendsto (fun z : ℕ × ℕ ↦ qpos z.1 z.2 - qneg z.1 z.2)
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let μc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let νc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let scale := physicalSceneCanonicalHaarScale (finrank ℝ E - 1)
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  have hdim2 : 2 ≤ finrank ℝ E := by omega
  have hqdim : 0 < finrank ℝ E - 1 := by omega
  have hscalePos := physicalSceneCanonicalHaarScale_pos (finrank ℝ E - 1)
  have hnormalization := physicalSceneCanonicalHaarScale_pow (finrank ℝ E - 1) hqdim
  have hμchart : ∀ old : M, (μc.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₀.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, (νc.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₁.continuous.measurable hρ₁nonneg
      v hv hvolume
  obtain ⟨u, hu, hproduced⟩ :=
    exists_original_physical_opposite_families_continuous_probe_gap_curry_zero
      hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
      hA hB hAB hμA hνB
  dsimp only
  let μp : ProbabilityMeasure M := ⟨μc, hμprob⟩
  let νp : ProbabilityMeasure M := ⟨νc, hνprob⟩
  let probe : M → M → ℝ := finslerCarrierProbe μp νp K hK.measurableSet hμK hνK f
  have hprobe : Measurable (Function.uncurry probe) :=
    f.continuous.measurable.comp
      (((measurable_supportProjection μp K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection νp K hK.measurableSet hνK).comp measurable_snd))
  have hprobeBound (x y : M) : |probe x y| ≤ (‖f‖₊ : ℝ) :=
    f.norm_coe_le_norm _
  obtain ⟨t, ap, am, htAnti, htPos, htLim, hpm, hmm, hopt, hgap⟩ :=
    hproduced probe ‖f‖₊ hprobe hprobeBound
  have hscaleMean (n : ℕ) : finslerMeanScale E n = scale n ^ 2 :=
    finslerMeanScale_eq_sq_of_scale_normalization hdim2 n (hscalePos n) (hnormalization n)
  refine ⟨u, hu, t, ap, am, htAnti, htPos, htLim, hpm, hmm, ?_, ?_⟩
  · intro ℓ n
    filter_upwards [hopt ℓ n] with w hw
    constructor
    · simpa only [probe, hscaleMean n] using hw.1
    · simpa only [probe, hscaleMean n] using hw.2
  · let _instDiffuse : NullSingletonClass νc :=
      nullSingletonClass_of_chartwise_ac m νc hdim2 hνchart
    let _instDiffuseProbability : NullSingletonClass (νp : Measure M) := _instDiffuse
    let Renv := fun n : ℕ ↦ originalReadoutEnvironment νc n
    let cost : ℕ → M × M → ℝ := fun n p ↦
      finslerMeanScale E n * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)
    have hcostm (n : ℕ) : Measurable (cost n) :=
      (F.measurable_distance_slack hu).const_mul _
    have hcostint : Integrable (fun p : M × M ↦
        (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) (μc.prod νc) :=
      integrable_continuous_of_compact_carriers μc νc hK hK hμK hνK
        (F.continuous_distance_slack hu)
    have hci (n : ℕ) : Integrable (cost n) (μc.prod νc) := hcostint.const_mul _
    have hatom (n : ℕ) : ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ νc),
        ∀ j l, j ≠ l → NullSingletonClass
          (μc.map (fun x ↦ cost n (x, y j) - cost n (x, y l))) := by
      filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1)) νc]
        with y hy j l hjl
      have hh := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μc hdim2 hμchart
        hcomplete u (show finslerMeanScale E n ≠ 0 from
          (Real.rpow_pos_of_pos (by positivity) _).ne') (hy.ne hjl)
      simpa only [cost, F.metricSpace_dist] using hh
    have hoptP (ℓ n : ℕ) : ∀ᵐ w ∂Renv n, IsOptimalSemidiscreteAllocation μc w.2
        (fun x j ↦ cost n (x, w.1 j) + t ℓ * probe x (w.1 j)) (ap ℓ n w) :=
      (hopt ℓ n).mono fun _ h ↦ by
        have h' := h.1
        simpa only [Renv, originalReadoutEnvironment, cost, probe, hscaleMean n] using h'
    have hoptM (ℓ n : ℕ) : ∀ᵐ w ∂Renv n, IsOptimalSemidiscreteAllocation μc w.2
        (fun x j ↦ cost n (x, w.1 j) + (-t ℓ) * probe x (w.1 j)) (am ℓ n w) :=
      (hopt ℓ n).mono fun _ h ↦ by
        have h' := h.2
        simpa only [Renv, originalReadoutEnvironment, cost, probe, hscaleMean n] using h'
    have hp (ℓ n : ℕ) := originalDirichletMean_supergradient_of_original_optimal_allocation
      μc νc (cost n) (Function.uncurry probe) (hcostm n) (hci n) hprobe (hatom n)
      ‖f‖₊ hprobeBound (ap ℓ n) (hpm ℓ n) (t ℓ) (hoptP ℓ n)
    have hm (ℓ n : ℕ) := originalDirichletMean_supergradient_of_original_optimal_allocation
      μc νc (cost n) (Function.uncurry probe) (hcostm n) (hci n) hprobe (hatom n)
      ‖f‖₊ hprobeBound (am ℓ n) (hmm ℓ n) (-(t ℓ)) (hoptM ℓ n)
    have hmean (n : ℕ) (s : ℝ) :
        finslerSemidiscreteMean F μp νp K hK hμK hνK u f s n =
          ∫ w, semidiscreteValue μc
            (fun x j ↦ cost n (x, w.1 j) + s * probe x (w.1 j)) w.2 ∂Renv n := by
      have hid := finslerSemidiscreteMean_eq_integral_semidiscreteValue
        hF hcomplete m hdim2 μp νp K hK hμK hνK u hu f s n (hcost := hcostint)
      dsimp only at hid
      rw [hid]
      exact (integral_prod _ ((hp 0 n).1 s)).symm
    let qpos : ℕ → ℕ → ℝ := fun ℓ n ↦
      originalReadoutIntegral μc νc (Function.uncurry probe) (ap ℓ n)
    let qneg : ℕ → ℕ → ℝ := fun ℓ n ↦
      originalReadoutIntegral μc νc (Function.uncurry probe) (am ℓ n)
    have hbound (ℓ n : ℕ) : |qpos ℓ n - qneg ℓ n| ≤
        ∫ w, |(∫ e, Function.uncurry probe e
              ∂physicalSceneGlobalAllocationFamily μc (ap ℓ n) Prod.fst w) -
            ∫ e, Function.uncurry probe e
              ∂physicalSceneGlobalAllocationFamily μc (am ℓ n) Prod.fst w| ∂Renv n := by
      haveI hRenvFin : IsFiniteMeasure (Renv n) := by
        dsimp only [Renv, originalReadoutEnvironment]
        infer_instance
      simpa only [qpos, qneg, originalReadoutIntegral, Renv] using
        (abs_originalGlobal_mean_probe_difference_le_expected_gap (Renv n) μc
          (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) Prod.fst
          (fun j ↦ (measurable_pi_apply j).comp measurable_fst) Prod.snd
          ((hoptP ℓ n).mono fun _ h ↦ h.1) ((hoptM ℓ n).mono fun _ h ↦ h.1)
          (Function.uncurry probe) hprobe ‖f‖₊ hprobeBound)
    have hgapSupported := tendsto_originalAllocation_supported_probe_gap_of_continuous
      ((atTop : Filter ℕ).curry atTop) (fun z : ℕ × ℕ ↦ z.2)
      (fun z : ℕ × ℕ ↦ Renv z.2) μp νp K hK hμK hνK
      (fun z ↦ ap z.1 z.2) (fun z ↦ am z.1 z.2) (fun _ ↦ Prod.fst) (fun _ ↦ Prod.snd)
      (fun z ↦ (hoptP z.1 z.2).mono fun _ h ↦ h.1)
      (fun z ↦ (hoptM z.1 z.2).mono fun _ h ↦ h.1)
      (fun z ↦ ae_originalTargets_mem_carrier z.2 νc K hνK)
      (fun g ↦ ⟨fun z ↦ (hgap g).1 z.1 z.2, (hgap g).2.1, (hgap g).2.2⟩) f
    have hgapTendsto : Tendsto (fun z : ℕ × ℕ ↦ qpos z.1 z.2 - qneg z.1 z.2)
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
      refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
      filter_upwards [hgapSupported.2.1.eventually (Iio_mem_nhds hε)]
        with z hz
      rw [Real.dist_eq, sub_zero]
      exact lt_of_le_of_lt (hbound z.1 z.2) hz
    refine ⟨qpos, qneg, ?_, ?_, ?_, ?_, hgapTendsto⟩
    · intro ℓ n s
      rw [hmean n s, hmean n (t ℓ)]
      exact (hp ℓ n).2 s
    · intro ℓ n s
      rw [hmean n s, hmean n (-(t ℓ))]
      have hh := (hm ℓ n).2 s
      rwa [sub_neg_eq_add] at hh
    · intro ℓ n
      rfl
    · intro ℓ n
      rfl

/-- **Differentiability of the original physical limiting pressure.**

Original physical populations produce one common potential `u`; for every
compact carrier and every pressure family whose physical Dirichlet means
converge pointwise on the tilt interval `|t| < radius f`, the limiting pressure
is differentiable at `0` with a single derivative function for all probes.
This is exactly the `hreadout` shape of the general selector assembly, with
the vanishing finite readout gap derived internally by the previous theorem. -/
theorem exists_potential_and_derivative_of_original_physical_pressure
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [hμprob : IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [hνprob : IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hνB : ∀ᵐ y ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    let μc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let νc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let μp : ProbabilityMeasure M := ⟨μc, hμprob⟩
    let νp : ProbabilityMeasure M := ⟨νc, hνprob⟩
    let _inst : MetricSpace M := F.metricSpace
    ∃ u : M → ℝ, LipschitzWith 1 u ∧
      ∀ (K : Set M) (hK : IsCompact K)
        (hμK : ∀ᵐ x ∂μc, x ∈ K) (hνK : ∀ᵐ y ∂νc, y ∈ K)
        (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
        (radius : ((K × K) →ᵇ ℝ) → ℝ)
        (_hradius : ∀ f, 0 < radius f)
        (hconv : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
          Tendsto (fun n ↦ finslerSemidiscreteMean F μp νp K hK hμK hνK u f t n)
            atTop (𝓝 (pressure f t))),
        ∃ derivative : ((K × K) →ᵇ ℝ) → ℝ,
          ∀ f : (K × K) →ᵇ ℝ, HasDerivAt (pressure f) (derivative f) 0 := by
  let μc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let νc := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨u, hu, hdiff⟩ :=
    exists_original_physical_potential_mean_differentiability
      hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
      hA hB hAB hμA hνB
  refine ⟨u, hu, ?_⟩
  intro K hK hμK hνK pressure radius hradius hconv
  have hex : ∀ f : (K × K) →ᵇ ℝ, ∃ d : ℝ, HasDerivAt (pressure f) d 0 := by
    intro f
    exact hdiff K hK hμK hνK f (pressure f) (hradius f)
      (fun s hs ↦ hconv f s (abs_lt.mpr hs))
  choose derivative hderiv using hex
  exact ⟨derivative, hderiv⟩

end OTSelector.Reconstruction
