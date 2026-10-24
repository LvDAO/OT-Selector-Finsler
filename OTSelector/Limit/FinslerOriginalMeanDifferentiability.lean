import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationProducedReadoutFace
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationMeanSlope
import OTSelector.Analysis.Convex.CurriedMeanDifferentiability
import OTSelector.Limit.FinslerMeanTiltConcavity
import OTSelector.Limit.FinslerMeanTiltSupergradient
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSupportedProbeGap
import OTSelector.Probability.IIDTargetCarrier

/-!
# Actual original mean differentiability from the original whole face

Original chart densities and the original optimal face produce opposite actual
allocations and vanishing raw supported-probe gaps. Their expected objectives
are the finite mean supergradients. The sample-before-tilt secant-width squeeze
then gives differentiability of the limiting physical mean pressure.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

/-- The original spatial normalization makes its square exactly the
microscopic multiplier in the actual physical semidiscrete mean. -/
theorem finslerMeanScale_eq_sq_of_scale_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 ≤ finrank ℝ E) (n : ℕ) {scale : ℝ} (hpos : 0 < scale)
    (hnorm : scale ^ (finrank ℝ E - 1) = (n : ℝ) + 1) :
    finslerMeanScale E n = scale ^ 2 := by
  unfold finslerMeanScale
  rw [Nat.cast_add, Nat.cast_one, ← hnorm,
    ← Real.rpow_natCast scale (finrank ℝ E - 1), ← Real.rpow_mul hpos.le]
  have hq : ((finrank ℝ E - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : finrank ℝ E - 1 ≠ 0)
  have heq : ((finrank ℝ E - 1 : ℕ) : ℝ) *
      (2 / ((finrank ℝ E - 1 : ℕ) : ℝ)) = 2 := by field_simp
  rw [heq, Real.rpow_two]


variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


/-- Actual original geometric inputs and the original pointwise physical mean
limit imply pressure differentiability, with the tilt, both optimizer families,
and the raw expected probe-gap comparison produced internally. -/
theorem exists_hasDerivAt_finslerSemidiscreteMean_of_original_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 6 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M}
    (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ (finrank ℝ E - 1) = (n : ℝ) + 1)
    (hμlaw : PopulationConditionalWindowLaw P a κ (μ.map a) μ ρ₀ v)
    (hνlaw : PopulationConditionalWindowLaw P a κ (μ.map a) ν ρ₁ v)
    (hAsupport : IsCompact A) (hBsupport : IsCompact B) (hAB : Disjoint A B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hbalance : μ.map a = ν.map a)
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hnearRadius : 0 < nearRadius)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂μ, x ∈ K) (hνK : ∀ᵐ y ∂ν, y ∈ K)
    (f : (K × K) →ᵇ ℝ) (pressure : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hpt : ∀ s ∈ Ioo (-ε) ε,
      Tendsto (fun n ↦ finslerSemidiscreteMean F (⟨μ, inferInstance⟩ : ProbabilityMeasure M)
        (⟨ν, inferInstance⟩ : ProbabilityMeasure M) K hK hμK hνK u f s n)
        atTop (𝓝 (pressure s))) :
    let _inst : MetricSpace M := F.metricSpace
    ∃ d : ℝ, HasDerivAt pressure d 0 := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  have hdim2 : 2 ≤ finrank ℝ E := by omega
  let _instDiffuse : NullSingletonClass ν := nullSingletonClass_of_chartwise_ac m ν hdim2 hνchart
  let μp : ProbabilityMeasure M := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure M := ⟨ν, inferInstance⟩
  let _instDiffuseProbability : NullSingletonClass (νp : Measure M) := _instDiffuse
  let probe : M → M → ℝ := finslerCarrierProbe μp νp K hK.measurableSet hμK hνK f
  have hprobe : Measurable (Function.uncurry probe) := by
    exact f.continuous.measurable.comp
      (((measurable_supportProjection μp K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection νp K hK.measurableSet hνK).comp measurable_snd))
  have hprobeBound (x y : M) : |probe x y| ≤ (‖f‖₊ : ℝ) :=
    f.norm_coe_le_norm _
  obtain ⟨t, ap, am, htAnti, htPos, htLim, hpm, hmm, hopt, hgapAmbient⟩ :=
    exists_originalAllocation_opposite_families_continuous_probe_gap_curry_zero_of_original_face
      hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
      scale hscalePos hscale hnormalization probe hprobe ‖f‖₊ hprobeBound
      hμlaw hνlaw hAsupport hBsupport hAB hμreg hνreg hκ hbalance hcore hrecovery hface
      hμA hνB hnearRadius
  let Renv := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  have hfp (ℓ n : ℕ) : ∀ᵐ w ∂Renv n, IsSemidiscreteAllocation μ w.2 (ap ℓ n w) :=
    (hopt ℓ n).mono fun _ h ↦ h.1.1
  have hfm (ℓ n : ℕ) : ∀ᵐ w ∂Renv n, IsSemidiscreteAllocation μ w.2 (am ℓ n w) :=
    (hopt ℓ n).mono fun _ h ↦ h.2.1
  have hgapSupported := tendsto_originalAllocation_supported_probe_gap_of_continuous
    ((atTop : Filter ℕ).curry atTop) (fun z : ℕ × ℕ ↦ z.2)
    (fun z : ℕ × ℕ ↦ Renv z.2) μp νp K hK hμK hνK
    (fun z ↦ ap z.1 z.2) (fun z ↦ am z.1 z.2) (fun _ ↦ Prod.fst) (fun _ ↦ Prod.snd)
    (fun z ↦ hfp z.1 z.2) (fun z ↦ hfm z.1 z.2)
    (fun z ↦ ae_originalTargets_mem_carrier z.2 ν K hνK)
    (fun g ↦ ⟨fun z ↦ (hgapAmbient g).1 z.1 z.2,
      (hgapAmbient g).2.1, (hgapAmbient g).2.2⟩) f
  let cost := fun n (p : M × M) ↦ finslerMeanScale E n *
    ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)
  have hcostm (n : ℕ) : Measurable (cost n) :=
    (F.measurable_distance_slack hu).const_mul _
  have hcostint : Integrable (fun p : M × M ↦
      (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) (μ.prod ν) :=
    integrable_continuous_of_compact_carriers μ ν hK hK hμK hνK
      (F.continuous_distance_slack hu)
  have hci (n : ℕ) : Integrable (cost n) (μ.prod ν) := hcostint.const_mul _
  have hscaleMean (n : ℕ) : finslerMeanScale E n = scale n ^ 2 :=
    finslerMeanScale_eq_sq_of_scale_normalization hdim2 n (hscalePos n) (hnormalization n)
  have hatom (n : ℕ) : ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
      ∀ j l, j ≠ l → NullSingletonClass
        (μ.map (fun x ↦ cost n (x, y j) - cost n (x, y l))) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1)) ν]
      with y hy j l hjl
    have hh := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim2 hμchart
      hcomplete u (show finslerMeanScale E n ≠ 0 from
        (Real.rpow_pos_of_pos (by positivity) _).ne') (hy.ne hjl)
    simpa only [cost, F.metricSpace_dist] using hh
  have hoptP (ℓ n : ℕ) : ∀ᵐ w ∂Renv n, IsOptimalSemidiscreteAllocation μ w.2
      (fun x j ↦ cost n (x, w.1 j) + t ℓ * probe x (w.1 j)) (ap ℓ n w) := by
    simpa only [cost, hscaleMean] using (hopt ℓ n).mono fun _ h ↦ h.1
  have hoptM (ℓ n : ℕ) : ∀ᵐ w ∂Renv n, IsOptimalSemidiscreteAllocation μ w.2
      (fun x j ↦ cost n (x, w.1 j) + (-t ℓ) * probe x (w.1 j)) (am ℓ n w) := by
    simpa only [cost, hscaleMean] using (hopt ℓ n).mono fun _ h ↦ h.2
  let mean := fun n s ↦ ∫ w, semidiscreteValue μ
    (fun x j ↦ cost n (x, w.1 j) + s * probe x (w.1 j)) w.2 ∂Renv n
  let qp := fun ℓ n ↦ ∫ w, ∫ e, Function.uncurry probe e
    ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) Prod.fst w ∂Renv n
  let qn := fun ℓ n ↦ ∫ w, ∫ e, Function.uncurry probe e
    ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) Prod.fst w ∂Renv n
  let gap := fun ℓ n ↦ ∫ w,
    |(∫ e, Function.uncurry probe e ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) Prod.fst w) -
      ∫ e, Function.uncurry probe e ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) Prod.fst w|
    ∂Renv n
  have hp (ℓ n : ℕ) := originalDirichletMean_supergradient_of_original_optimal_allocation
    μ ν (cost n) (Function.uncurry probe) (hcostm n) (hci n) hprobe (hatom n)
    ‖f‖₊ hprobeBound (ap ℓ n) (hpm ℓ n) (t ℓ) (hoptP ℓ n)
  have hm (ℓ n : ℕ) := originalDirichletMean_supergradient_of_original_optimal_allocation
    μ ν (cost n) (Function.uncurry probe) (hcostm n) (hci n) hprobe (hatom n)
    ‖f‖₊ hprobeBound (am ℓ n) (hmm ℓ n) (-t ℓ) (hoptM ℓ n)
  have hmean (n : ℕ) (s : ℝ) :
      finslerSemidiscreteMean F μp νp K hK hμK hνK u f s n = mean n s := by
    have hid := finslerSemidiscreteMean_eq_integral_semidiscreteValue
      hF hcomplete m hdim2 μp νp K hK hμK hνK u hu f s n (hcost := hcostint)
    dsimp only at hid
    rw [hid]
    exact (integral_prod _ ((hp 0 n).1 s)).symm
  have hconc (n : ℕ) : ConcaveOn ℝ (Ioo (-ε) ε) (mean n) := by
    have hbase : ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
        ∀ j, Integrable (fun x ↦ cost n (x, y j)) μ := by
      apply ae_all_iff.mpr
      intro j
      exact (measurePreserving_eval (fun _ : Fin (n + 1) ↦ ν) j).quasiMeasurePreserving.ae
        (hci n).prod_left_ae
    have hbaseR : ∀ᵐ w ∂Renv n, ∀ j, Integrable (fun x ↦ cost n (x, w.1 j)) μ :=
      measurePreserving_fst.quasiMeasurePreserving.ae hbase
    have hsimplex : ∀ᵐ w ∂Renv n, w.2 ∈ stdSimplex ℝ (Fin (n + 1)) :=
      measurePreserving_snd.quasiMeasurePreserving.ae (ae_mem_stdSimplex_dirichletOne n)
    have hpoint : ∀ᵐ w ∂Renv n, ConcaveOn ℝ univ (fun s ↦
        semidiscreteValue μ (fun x j ↦ cost n (x, w.1 j) + s * probe x (w.1 j)) w.2) := by
      filter_upwards [hbaseR, hsimplex] with w hw hws
      exact concaveOn_semidiscreteValue_tilt μ _ _ hw
        (fun j ↦ Integrable.of_bound
          (hprobe.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
          ‖f‖ (ae_of_all _ fun x ↦ hprobeBound x (w.1 j))) hws
    exact (concaveOn_integral_of_ae (Renv n) convex_univ hpoint
      (fun s _ ↦ (hp 0 n).1 s)).subset (subset_univ _) (convex_Ioo (-ε) ε)
  apply OTSelector.hasDerivAt_of_concave_mean_of_curry_supergradient_gap hε mean pressure
    hconc (fun s hs ↦ (hpt s hs).congr' (Eventually.of_forall fun n ↦ hmean n s))
    t htPos htLim qp qn gap
  · exact fun ℓ n s ↦ (hp ℓ n).2 s
  · intro ℓ n s
    have hh := (hm ℓ n).2 s
    change mean n s ≤ mean n (-t ℓ) + qn ℓ n * (s - -t ℓ) at hh
    rwa [sub_neg_eq_add] at hh
  · exact fun ℓ n ↦ abs_originalGlobal_mean_probe_difference_le_expected_gap
      (Renv n) μ (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) Prod.fst
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst) Prod.snd
      (hfp ℓ n) (hfm ℓ n) (Function.uncurry probe) hprobe ‖f‖₊ hprobeBound
  · exact hgapSupported.2.1

end OTSelector.Reconstruction
