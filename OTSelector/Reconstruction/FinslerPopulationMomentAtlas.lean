import OTSelector.Reconstruction.FinslerPopulationConditionalAtlas
import OTSelector.Geometry.Manifold.ChartVolumeDensityExtension
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation
import OTSelector.Reconstruction.FinslerPopulationCompactCore
import OTSelector.Probability.ConditionalLabelCoreRecovery
import OTSelector.Reconstruction.FinslerOriginalConditionalMoments
import OTSelector.Reconstruction.FinslerPopulationFiniteSeedCore
import OTSelector.Reconstruction.FinslerPopulationSeedPieceMoments
import OTSelector.Reconstruction.FinslerPopulationPressureCore
import OTSelector.Reconstruction.FinslerPopulationContinuousPressureCore
import OTSelector.Reconstruction.FinslerPopulationLocalPressureCore
import OTSelector.Reconstruction.FinslerPopulationSeedPhysicalRecovery
import OTSelector.Reconstruction.FinslerPopulationIIDCoordinateLaws
import OTSelector.Probability.IIDLabelCoreRecovery
import OTSelector.Reconstruction.FinslerPopulationExpectedCoreLoss

/-!
# The original Lipschitz populations produce their common moment atlas

The original physical hypotheses construct the potential, common geometric labels,
the entire optimal face and both original conditional laws. A single actual seed
comparison supplies both colors' compliance moments at every interior root. The
chart volume density is assumed regular only where that original chart is defined.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace OTSelector.Reconstruction

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original nonnegative Lipschitz physical probabilities with compact disjoint carriers
construct the common actual atlas and both full compliance moment laws, preserving every
optimal coupling. All conditional support, endpoint, rank and weight data are produced. -/
theorem exists_finsler_lipschitz_population_moment_atlas (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _instPhysicalSourceMetric : MetricSpace M := F.metricSpace
      LipschitzWith K₀ ρ₀)
    (hρ₁ : let _instPhysicalTargetMetric : MetricSpace M := F.metricSpace
      LipschitzWith K₁ ρ₁)
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
    let vbar := populationChartVolumeExtension v
    let _instPhysicalMomentMetric : MetricSpace M := F.metricSpace
    let _instPhysicalMomentProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPhysicalMomentBorel : StandardBorelSpace M := inferInstance
    let _instPhysicalMomentNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
    ∃ (u : M → ℝ) (a : M → (ℚ → M)), LipschitzWith 1 u ∧
      MeasurableSet (F.potentialRegularDomain u) ∧
      (∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u) ∧
      (∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u) ∧ Measurable a ∧
      Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)) ∧
      (∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) ∧
      μ.map a = ν.map a ∧
      (∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2) ∧
      ∃ (P : ℕ → F.CalibratedSeedWindow u)
        (κ : ∀ j, Measure (P j).seed.covector.ker) (b : (ℚ → M) × ℝ → M),
        (⋃ j, (P j).toManifold '' (P j).domain) = calibratedInterior u ∧
        (∀ᵐ x ∂μ, x ∈ ⋃ j, (P j).toManifold '' (P j).domain) ∧
        (∀ᵐ x ∂ν, x ∈ ⋃ j, (P j).toManifold '' (P j).domain) ∧
        (∀ j, (κ j).IsAddHaarMeasure) ∧
        (∀ j, tubeParameterMeasure (P j).seed.normalization m =
          (volume : Measure ℝ).prod (κ j)) ∧
        Measurable b ∧ (∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x) ∧
        (∀ j,
          (∀ z ∈ (P j).domain,
            a ((P j).toManifold z) = a ((P j).seed.curve z.2 0)) ∧
          MeasurableEmbedding (fun w : (P j).labels ↦ a ((P j).seed.curve w 0))) ∧
        let vP := fun j ↦ vbar ((P j).toManifold (P j).center)
        PopulationConditionalWindowLaw P a κ (μ.map a) μ ρ₀ vP ∧
          PopulationConditionalWindowLaw P a κ (μ.map a) ν ρ₁ vP ∧
          PopulationFullWindowRestrictionLaw P a κ (μ.map a) μ ρ₀ vP b ∧
          PopulationFullWindowRestrictionLaw P a κ (μ.map a) ν ρ₁ vP b ∧
          (∀ j (u₀ : ℝ), PopulationSeedChartDensityLaw (P j).seed a (κ j)
            (μ.map a) μ ρ₀ vbar u₀) ∧
          (∀ j (u₀ : ℝ), PopulationSeedChartDensityLaw (P j).seed a (κ j)
            (μ.map a) ν ρ₁ vbar u₀) ∧
          PopulationConditionalSupportLaw (F := F) (u := u) a (μ.map a) μ ν ∧
          PopulationSupportedComparisonLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vbar ∧
          PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν ∧
          PopulationConditionalCompactCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vP ∧
          PopulationFiniteSeedCompactCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vP ∧
          PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν ∧
          PopulationFinitePressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vP b ∧
          PopulationContinuousPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vP b ∧
          (∀ r : ℝ, PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vP b r) ∧
          (∀ r : ℝ, PopulationLocalPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vP b r) ∧
          (∃ δ : ℝ, 0 < δ ∧ PopulationConditionalSeparationLaw u a
            (μ.map a) μ ν δ (Metric.diam (A ∪ B)) ∧
            PopulationSeedPieceCoefficientLaw P a κ (μ.map a) μ ν ∧
            PopulationSeedPieceBoundedCoefficientLaw P a κ (μ.map a) μ ν) ∧
          PopulationConditionalMomentLaw P a (μ.map a) μ ν := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let vbar := populationChartVolumeExtension v
  let _instPhysicalMomentMetric : MetricSpace M := F.metricSpace
  let _instPhysicalMomentProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPhysicalMomentBorel : StandardBorelSpace M := inferInstance
  let _instPhysicalMomentNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  have hvbar (old : M) : Measurable (vbar old) :=
    measurable_populationChartVolumeExtension (hv old)
  have hvbarCont (old : M) : ContinuousOn (vbar old) (extChartAt 𝓘(ℝ, E) old).target :=
    continuousOn_populationChartVolumeExtension (hv old)
  have hvbar0 (old : M) (y : E) : 0 ≤ vbar old y :=
    nonneg_populationChartVolumeExtension (hvnonneg old) y
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
      P, κ, b, hcover, hμcover, hνcover, hκ, hprod, hb, hbinv, hwindow,
      hμlaw, hνlaw, hμfull, hνfull, hμseed, hνseed, hsupport, hcomparison⟩ :=
    exists_finsler_population_conditional_atlas hF hcomplete m ωM ρ₀ ρ₁
      hρ₀.continuous.measurable hρ₁.continuous.measurable hρ₀nonneg hρ₁nonneg
      vbar hvbar (fun old ↦ map_extChartAt_eq_withDensity_volumeExtension ωM m old (hvolume old))
      hA hB hAB hμ hν
  have hpiece : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν :=
    populationSeedPieceMomentLaw_of_physical_laws hsupport
      (fun j ↦ hμseed j (P j).seed.level) (fun j ↦ hνseed j (P j).seed.level)
      hF hcomplete hu ha hinj hκ hρ₀.continuous hρ₁.continuous hρ₀nonneg hρ₁nonneg
      hvbarCont (fun old y _ ↦ hvbar0 old y)
  obtain ⟨δ, hδ, hsep⟩ := exists_population_conditional_separation μ ν ha hbalance
    hu.continuous hA hB hAB hN hμ hν hμN hνN horder
  have hrecovery := populationLabelCoreRecoveryLaw_of_inverse μ ν ha hu.continuous.measurable
    hb rfl hbalance.symm (hμN.mono fun x hx ↦ hbinv x hx) (hνN.mono fun x hx ↦ hbinv x hx)
  have hfiniteCore := hμlaw.finite_seed_compact_core hνlaw hF hcomplete hu ha hinj horder
    (fun j ↦ by let _instMomentAtlasHaar : (κ j).IsAddHaarMeasure := hκ j; infer_instance)
  have hbounded := hpiece.bounded_coefficient_localization hF hδ hsep
  have hpressure := hfiniteCore.pressure_core hrecovery hpiece hbounded hcomplete ha
    hu.continuous.measurable
  have hrootcover := hμlaw.ae_mem_populationSeedRootPieces P a κ (μ.map a)
    hF hcomplete hu ha hinj horder
      (fun j ↦ by let _instMomentRootHaar : (κ j).IsAddHaarMeasure := hκ j; infer_instance)
  have hcontinuousCore := hpressure.continuous_core hrecovery hpiece hrootcover
    hF hcomplete hu ha hinj hδ hsep
  let _instMomentAtlasHaarSigma : ∀ j, SigmaFinite (κ j) := fun j ↦ by
    let _instMomentAtlasHaar : (κ j).IsAddHaarMeasure := hκ j
    infer_instance
  exact ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
    P, κ, b, hcover, hμcover, hνcover, hκ, hprod, hb, hbinv, hwindow,
    hμlaw, hνlaw, hμfull, hνfull, hμseed, hνseed, hsupport, hcomparison,
    hrecovery, hμlaw.compact_core hνlaw hcomplete, hfiniteCore, hpiece,
    hpressure,
    hcontinuousCore,
    (fun r ↦ hcontinuousCore.haar_core hrecovery hF hcomplete hu ha hinj r),
    (fun r ↦ (hcontinuousCore.haar_core hrecovery hF hcomplete hu ha hinj r).local_core
      hrecovery hF hcomplete hu ha hinj hκ),
    ⟨δ, hδ, hsep, hpiece.coefficient_localization hF hδ hsep, hbounded⟩,
    hcomparison.conditional_moments hF hρ₀.continuous hρ₁.continuous hρ₀nonneg hρ₁nonneg
      hvbarCont (fun old y _ ↦ hvbar0 old y)⟩

end OTSelector.Reconstruction
