import OTSelector.Reconstruction.FinslerOriginalPaperEndgameDataActualAssembly
import OTSelector.Reconstruction.FinslerOriginalFrozenCampbellReadoutReduction
import OTSelector.Reconstruction.FinslerOriginalActualUpperReadoutProducer
import OTSelector.Reconstruction.FinslerOriginalIIDPressureLowerLocalization
import OTSelector.Reconstruction.FinslerOriginalEndgameValueFieldActual
import OTSelector.Limit.FinslerPhysicalMeanDifferentiability
import OTSelector.Reconstruction.FinslerOriginalChosenPopulationAtlas
/-!
# Wired actual endgame data and the selector at the derived calibrated potential

This module closes the composition gap left by
`FinslerOriginalPaperEndgameDataActualAssembly`.  There the paper endgame data at
a GIVEN calibrated potential kept the frozen Campbell readout (F15), the upper
stationary readout (F18), the screening data and the unshifted lower probability
(F12) as explicit binders.  Here those four fields are DERIVED from the paper's
remaining identities and the proven lane producers:

* `hC` from N1 `AtlasStationaryPressureIdentification` and N2
  `FrozenStationaryPressureIdentification` via
  `frozenCampbellReadout_of_identifications` (the Campbell integration step);
* `hU` from `UpperPoolEnvelope` via `actualUpperReadout_of_envelope` (a lower
  bound of the second-moment class that is attained is its infimum);
* `hscreen` from the uniform-elliptic screening producer
  `stationaryScreening_originalLaneDatumFamily_of_uniform_elliptic` at the actual
  original-lane datum family `originalLaneDatumFamily`;
* `hprob` at the UNSHIFTED frozen pressure from the frozen lower model
  (integrability, the paper support bound and the single remaining mean input
  `hfrozen_mean_shifted`) via
  `physical_finsler_probability_lower_of_frozen_mean_lower`, i.e. exactly the
  body of the F12 repair `finalProbLowerData_unshifted` with its unused tile-lane
  parameters eliminated.

Contents:

1. `paperCalibratedPotential` -- the paper's calibrated potential as a named
   noncomputable definition produced from the population data, with
   `paperCalibratedPotential_spec` (the pair of properties returned by
   `exists_original_physical_potential_mean_differentiability`),
   `paperCalibratedPotential_lipschitz` (the potential is 1-Lipschitz, i.e. a
   feasible Kantorovich dual potential) and `paperCalibratedPotential_slack_nonneg`
   (nonnegative Kantorovich slack `u x - u y <= dist x y`).
2. `paperEndgameData_actual_wired` -- the paper endgame data
   `FinslerPaperEndgameData` with the four fields above derived.
3. `existsUnique_general_finsler_selector_at_derivedPotential` -- the paper
   selector theorem at the DERIVED potential: no `u` or `hu` binder occurs; the
   potential is `paperCalibratedPotential` and its one-Lipschitz property is
   supplied by `paperCalibratedPotential_lipschitz`.

Remaining named inputs: the two population readout identities N1 and N2, the
upper-envelope identity `UpperPoolEnvelope`, the frozen lower mean
`hfrozen_mean_shifted` (with the frozen integrability and the paper support
bound), the readout tilt derivative `FinslerReadoutTiltDerivative` (dischargeable
by the audited kinetic-squeeze reduction), the F13 `PopData` telescope, the
geometric seed datum and the geometric lane data of the original lane.

No `sorry`, `admit` or added axiom occurs.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability
  TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
  BigOperators

noncomputable section

namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The calibrated potential produced by the paper population data. -/
noncomputable def paperCalibratedPotential
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    M → ℝ := by
  exact chosenPopulationPotential
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμ hν

/-- **The sampled specification of the calibrated potential.**  The produced
potential is 1-Lipschitz for the intrinsic Finsler metric and every pressure that
is the pointwise limit of its physical semidiscrete means on a neighbourhood of
zero is differentiable at zero. -/
theorem paperCalibratedPotential_spec
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    letI : MetricSpace M := F.metricSpace
    LipschitzWith 1 (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν) ∧
      (∀ (K : Set M) (hK : IsCompact K)
        (hμK : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ K)
        (hνK : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ K)
        (f : (K × K) →ᵇ ℝ) (pressure : ℝ → ℝ) {ε : ℝ}, 0 < ε →
        (∀ s ∈ Ioo (-ε) ε,
          Tendsto (fun n => finslerSemidiscreteMean F
            (⟨ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), inferInstance⟩ :
              ProbabilityMeasure M)
            (⟨ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), inferInstance⟩ :
              ProbabilityMeasure M)
            K hK hμK hνK
            (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
              hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν)
            f s n) atTop (𝓝 (pressure s))) →
        ∃ d : ℝ, HasDerivAt pressure d 0) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  let scale := physicalSceneCanonicalHaarScale (finrank ℝ E - 1)
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : StandardBorelSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  have hatlas := chosenPopulationPotential_atlas
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg
    v hv hvnonneg hvolume hA hB hAB hμ hν
  dsimp only [ChosenWitnessSpec] at hatlas
  obtain ⟨a, hu, _hN, hμreg, hνreg, ha, hinj, horder, hbalance, hface,
      P, κ, b, _hcover, _hμcover, _hνcover, hκ, _hprod, _hb, _hbinv, _hwindow,
      hμlaw, hνlaw, _hμfull, _hνfull, _hμseed, _hνseed, _hsupport, _hcomparison,
      hrecovery, _hcompact, _hfinite, _hpiece, _hpressure, _hcontinuous,
      hhaar, _hlocal, _hsep, _hmoment⟩ := hatlas
  have hu : LipschitzWith 1 u := hu
  letI : ∀ j, SigmaFinite (κ j) := fun j ↦ by
    letI : (κ j).IsAddHaarMeasure := hκ j
    infer_instance
  have hdim2 : 2 ≤ finrank ℝ E := by omega
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
  refine ⟨hu, ?_⟩
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
    exists_originalAllocation_opposite_families_continuous_probe_gap_curry_zero_of_original_face
      (P := P) (a := a) (κ := κ) (b := b) (r := 1)
      hF hcomplete hu ha hinj horder hdim m hμchart hνchart 1
      scale hscalePos hscale hnormalization probe hprobe ‖f‖₊ hprobeBound
      hμlaw hνlaw hA hB hAB hμreg hνreg hκ hbalance (hhaar 1) hrecovery hface
      (ae_iff.mp hμ) (ae_iff.mp hν) (by norm_num)
  exact exists_hasDerivAt_finslerSemidiscreteMean_of_produced_original_allocations
    hF hcomplete hu hdim2 m hμchart hνchart scale hscalePos hnormalization
    K hK hμK hνK f t htPos htLim ap am hpm hmm hopt hgap pressure hε hpt

/-- The calibrated potential is 1-Lipschitz for the intrinsic Finsler metric. -/
theorem paperCalibratedPotential_lipschitz
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    letI : MetricSpace M := F.metricSpace
    LipschitzWith 1 (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν) := by
  letI : MetricSpace M := F.metricSpace
  exact (paperCalibratedPotential_spec hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν).1

/-- **Dual feasibility (zero-slack calibration) of the calibrated potential.**
Against the intrinsic Finsler cost the potential has nonnegative Kantorovich
slack: `u x - u y ≤ dist x y` for all points, i.e. `0 ≤ dist x y - (u y - u x)`. -/
theorem paperCalibratedPotential_slack_nonneg
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    letI : MetricSpace M := F.metricSpace
    ∀ x y : M, paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν x -
      paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν y ≤ dist x y := by
  letI : MetricSpace M := F.metricSpace
  intro x y
  have h := paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  have hd := h.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul] at hd
  rw [Real.dist_eq] at hd
  exact (abs_le.mp hd).2

/-! ## 2. The fully wired actual endgame data -/

/-- **The paper endgame data at a calibrated potential with the three remaining
readout/mean identities supplied as their proven reductions.**

Compared with `paperEndgameData_actual`, the endgame fields are DERIVED:

* `hC` (F15, `FrozenCampbellReadout`) from the population readout identity
  (N1, `AtlasStationaryPressureIdentification`) and the per-root frozen readout
  identity (N2, `FrozenStationaryPressureIdentification`) via
  `frozenCampbellReadout_of_identifications` (the Campbell integration step);
* `hU` (F18, `UpperStationaryReadout` of the actual block weighted upper pool)
  from the upper-envelope identity `UpperPoolEnvelope` via
  `actualUpperReadout_of_envelope`;
* `hscreen` from the proven uniform-elliptic screening producer
  `stationaryScreening_originalLaneDatumFamily_of_uniform_elliptic`, applied to
  the actual original-lane datum family `originalLaneDatumFamily`;
* `hprob` (F12, lower probability at the UNSHIFTED frozen pressure) from the
  frozen lower model (integrability, the paper support bound and the single
  remaining mean input `hfrozen_mean_shifted`) via
  `physical_finsler_probability_lower_of_frozen_mean_lower`.  This is exactly
  the body of the F12 repair `finalProbLowerData_unshifted`; the tile-lane
  parameters of that wrapper (`PopulationLocalPressureCore`, `TaylorTiles`, the
  tile Campbell identification) are not consumed by its proof and are therefore
  eliminated here.

Because the screening producer is stated for the original-lane datum family, the
stationary datum is `originalLaneDatumFamily` at the same frozen readout family.
Its geometric lane data (conditional moments, clock support bounds, ordered
coupling, lane probe and kinetic domination) are explicit binders.

No `sorry`, `admit` or added axiom occurs. -/
noncomputable def paperEndgameData_actual_wired
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (P n).map (X n i) =
      ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (P n).map (Y n j) =
      ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (u : M → ℝ)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (seedDatum : PaperGeometricSeedDatum F u
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {g : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    -- F12 repair: the frozen lower model at the unshifted frozen pressure
    (frozenCost : (f : FinalProbeSpace A B) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx => Or.inl hx) (hνB.mono fun _ hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_mean_shifted : ∀ (f : FinalProbeSpace A B) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f t +
            |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n)
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (data f t hpert).p c t = pc f t c)
    -- geometric lane data of the actual original lane (screening producer)
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μc νc : Measure ℝ}
    (Dp : OriginalSeedConditionalMoments S w μc νc)
    (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μc νc gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μc νc) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {Glane : ℝ} {glane : ℝ → ℝ → ℝ}
    (hglane : Measurable (Function.uncurry glane))
    (hgblane : ∀ a b, |glane a b| ≤ Glane)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ Dp.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ Dp.originalFocalKinetic gap a b v)
    -- N1 and N2 about the original-lane stationary datum
    (α β : Measure UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z → PointProcess.MarkedCloudPoint → PointProcess.MarkedCloudPoint → ℝ)
    (hAtlas : AtlasStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) α β
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg) coef probeFam q)
    (hFrozenN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) g α β coef probeFam q)
    -- upper-envelope identity of the actual block weighted pool
    (hEnv : UpperPoolEnvelope qU mU pc
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg)) :
    FinslerPaperEndgameData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u := by
  classical
  have hprob : FinalProbLowerData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) (fun _ => 1) := by
    intro f t ε ht hε
    exact physical_finsler_probability_lower_of_frozen_mean_lower hcomplete hdim
      ωM ρ₀ ρ₁ hA hB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) (fun _ => 1)
      frozenCost hfrozen_int hfrozen_dom hfrozen_mean_shifted f t ε ht hε
  let datum := originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
    hglane hgblane hkin_nonneg
  have hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum :=
    frozenCampbellReadout_of_identifications g q datum α β coef probeFam hAtlas
      hFrozenN2
  have hU : UpperStationaryReadout
      (endgameUpperPressure_actual (A := A) (B := B) qU mU pc) datum :=
    actualUpperReadout_of_envelope qU mU pc datum hEnv
  have hscreen : StationaryScreening datum :=
    stationaryScreening_originalLaneDatumFamily_of_uniform_elliptic A B Dp hF hw hq
      hgap hbounds pi hpi horder hglane hgblane hkin_nonneg hc hkin
  exact paperEndgameData_actual (F := F) hF hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB
    hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu seedDatum hprob qU mU hmU pc
    data hpc (datum := datum) hC hU hscreen

/-! ## 3. The selector theorem at the derived calibrated potential -/

/-- **The general Finsler selector at the DERIVED calibrated potential.**

The potential `u` is no longer a binder: it is the named definition
`paperCalibratedPotential` produced from the paper population data, and its
one-Lipschitz property is the proven `paperCalibratedPotential_lipschitz`.
Consequently the endgame data at this potential are produced by
`paperEndgameData_actual_wired`, whose readout/mean fields are the derived ones
(N1+N2, `UpperPoolEnvelope`, the uniform-elliptic screening producer and the
unshifted F12 frozen lower model).  The only remaining named inputs are the two
paper readout identities N1 and N2, the upper-envelope identity, the frozen
lower mean `hfrozen_mean_shifted` (plus its integrability and paper support
bound), the readout tilt derivative at the frozen pressure, the F13 `PopData`
telescope, the geometric seed datum and the geometric lane data of the original
lane. -/
theorem existsUnique_general_finsler_selector_at_derivedPotential
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (P n).map (X n i) =
      ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (P n).map (Y n j) =
      ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (seedDatum : PaperGeometricSeedDatum F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {Seed : ℕ → F.CalibratedSeedWindow
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)} {a : M → Z}
    {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {g : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (frozenCost : (f : FinalProbeSpace A B) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx => Or.inl hx) (hνB.mono fun _ hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s)
          (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
            hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_mean_shifted : ∀ (f : FinalProbeSpace A B) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f t +
            |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n)
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (data f t hpert).p c t = pc f t c)
    {S : CalibratedLevelSeedPatch F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)} {w : S.covector.ker}
    {μc νc : Measure ℝ}
    (Dp : OriginalSeedConditionalMoments S w μc νc)
    (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μc νc gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μc νc) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {Glane : ℝ} {glane : ℝ → ℝ → ℝ}
    (hglane : Measurable (Function.uncurry glane))
    (hgblane : ∀ a b, |glane a b| ≤ Glane)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ Dp.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ Dp.originalFocalKinetic gap a b v)
    (α β : Measure UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      PointProcess.MarkedCloudPoint → PointProcess.MarkedCloudPoint → ℝ)
    (hAtlas : AtlasStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) α β
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg) coef probeFam q)
    (hFrozenN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) g α β coef probeFam q)
    (hEnv : UpperPoolEnvelope qU mU pc
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg))
    (hderiv : FinslerReadoutTiltDerivative
      (paperEndgameData_actual_wired hF hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB hμA hνB
        P X Y hX hY hXi hYi hXlaw hYlaw hXY
        (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
          hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        (paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
          hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        seedDatum frozenCost hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU
        hmU pc data hpc Dp hw hq hgap hbounds pi hpi horder hglane hgblane
        hkin_nonneg hc hkin α β coef probeFam hAtlas hFrozenN2 hEnv).pressureLower) :
    let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
    let hu : (letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :=
      paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
    let D := paperEndgameData_actual_wired hF hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB
      hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu seedDatum frozenCost
      hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU hmU pc data hpc Dp hw hq
      hgap hbounds pi hpi horder hglane hgblane hkin_nonneg hc hkin α β coef probeFam
      hAtlas hFrozenN2 hEnv
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    Nonempty (FinslerSelectorFinalInputs F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u) ∧
        Tendsto (fun n => D.geometric.palm_sample_law.normalization n *
          D.geometric.palm_sample_law.maskedMean n -
          D.geometric.palm_sample_law.populationValue n) atTop (𝓝 0) ∧
        ∃ derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ,
          (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
            HasDerivAt (fun t => D.pressureLower f t) (derivative f) 0) ∧
          ∃! π : ProbabilityMeasure (M × M),
            (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
              ∫ z, f z ∂((π : Measure (M × M)).comap
                (Prod.map ((↑) : ↥(A ∪ B) → M) ((↑) : ↥(A ∪ B) → M))) = derivative f) ∧
            (∀ U ∈ 𝓝 π, Tendsto (fun n => (P n).real
              {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                (fun i => X n i s) (fun i => Y n i s), γ ∉ U}) atTop (𝓝 0)) ∧
            (∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
              d π π = 0 →
              (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (M × M) | d γ π < ε}) →
              ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (P n).real
                {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                  (fun i => X n i s) (fun i => Y n i s), ε ≤ d γ π}) atTop (𝓝 0)) ∧
            IsOptimalCoupling edist
              (physicalSourceProbability ωM ρ₀ : Measure M)
              (physicalTargetProbability ωM ρ₁ : Measure M) (π : Measure (M × M)) := by
  classical
  let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
    hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  let hu : (letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :=
    paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
      hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  let D := paperEndgameData_actual_wired hF hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB
    hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu seedDatum frozenCost
    hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU hmU pc data hpc Dp hw hq
    hgap hbounds pi hpi horder hglane hgblane hkin_nonneg hc hkin α β coef probeFam
    hAtlas hFrozenN2 hEnv
  have hd : FinslerReadoutTiltDerivative D.pressureLower := hderiv
  exact existsUnique_general_finsler_selector_at_potential_paperData hF hcomplete
    hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB
    hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu D hd

end OTSelector.Reconstruction
