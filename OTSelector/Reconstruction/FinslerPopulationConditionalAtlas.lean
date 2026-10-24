import OTSelector.Geometry.Finsler.TubeParameterProduct
import OTSelector.Reconstruction.FinslerMeasuredAtlas
import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Reconstruction.FinslerPopulationWindowRestriction
import OTSelector.Reconstruction.FinslerPopulationSeedDensity
import OTSelector.Reconstruction.FinslerPopulationSupportedComparison
import OTSelector.Transport.Coupling.LabelClockCoordinates

/-!
# An original physical population constructs its common conditional atlas

The two physical densities and the actual coordinate density of volume construct
one optimal potential, geometric labels, calibrated atlas and Haar family. Both
original conditional laws have the explicit physical window formulas on their
shared label marginal. The entire optimal face is retained.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace OTSelector.Reconstruction

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original physical laws with compact disjoint carriers construct a common actual
atlas, shared Haar references and their exact normalized conditional densities.
Chart absolute continuity is derived from the given volume coordinate formula. -/
theorem exists_finsler_population_conditional_atlas (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) (hρ₀ : Measurable ρ₀) (hρ₁ : Measurable ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ) (hv : ∀ old, Measurable (v old))
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), x ∈ B) :
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let _instPhysicalAtlasMetric : MetricSpace M := F.metricSpace
    let _instPhysicalAtlasProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instPhysicalAtlasBorel : StandardBorelSpace M := inferInstance
    let _instPhysicalAtlasNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
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
        let vP := fun j ↦ v ((P j).toManifold (P j).center)
        PopulationConditionalWindowLaw P a κ (μ.map a) μ ρ₀ vP ∧
          PopulationConditionalWindowLaw P a κ (μ.map a) ν ρ₁ vP ∧
          PopulationFullWindowRestrictionLaw P a κ (μ.map a) μ ρ₀ vP b ∧
          PopulationFullWindowRestrictionLaw P a κ (μ.map a) ν ρ₁ vP b ∧
          (∀ j (u₀ : ℝ), PopulationSeedChartDensityLaw (P j).seed a (κ j)
            (μ.map a) μ ρ₀ v u₀) ∧
          (∀ j (u₀ : ℝ), PopulationSeedChartDensityLaw (P j).seed a (κ j)
            (μ.map a) ν ρ₁ v u₀) ∧
          PopulationConditionalSupportLaw (F := F) (u := u) a (μ.map a) μ ν ∧
          PopulationSupportedComparisonLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v := by
  classical
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _instPhysicalAtlasMetric : MetricSpace M := F.metricSpace
  let _instPhysicalAtlasProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPhysicalAtlasBorel : StandardBorelSpace M := inferInstance
  let _instPhysicalAtlasNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  have hchart (ρ : M → ℝ) (hρ : Measurable ρ) (hρnonneg : ∀ x, 0 ≤ ρ x)
      (old : M) :
      ((ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).restrict
        (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m := by
    rw [map_extChartAt_withDensity_of_volume_density old ωM m hρ hρnonneg
      (hv old).aemeasurable (hvolume old)]
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
      _, _, _, _, _, ι, hι, P₀, hcover, hμcover, hνcover, hwindow⟩ :=
    exists_finsler_measured_calibrated_atlas hF hcomplete m μ ν
      (hchart ρ₀ hρ₀ hρ₀nonneg) (hchart ρ₁ hρ₁ hρ₁nonneg) hA hB hAB hμ hν
  let _instPhysicalWindowCountable : Countable ι := hι
  obtain ⟨x, hx⟩ := hμcover.exists
  obtain ⟨i, _⟩ := mem_iUnion.mp hx
  let _instPhysicalWindowNonempty : Nonempty ι := ⟨i⟩
  obtain ⟨r, hr⟩ := exists_surjective_nat ι
  let P : ℕ → F.CalibratedSeedWindow u := fun j ↦ P₀ (r j)
  have hcoverNat : (⋃ j, (P j).toManifold '' (P j).domain) = calibratedInterior u := by
    rw [← hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨r j, hj⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨j, rfl⟩ := hr i
      exact mem_iUnion.mpr ⟨j, hi⟩
  have hμcoverNat : ∀ᵐ x ∂μ, x ∈ ⋃ j, (P j).toManifold '' (P j).domain := by
    simpa only [hcoverNat, hcover] using hμcover
  have hνcoverNat : ∀ᵐ x ∂ν, x ∈ ⋃ j, (P j).toManifold '' (P j).domain := by
    simpa only [hcoverNat, hcover] using hνcover
  choose κ hκ hprod using fun j ↦
    exists_tubeParameterMeasure_eq_volume_prod (P j).seed.normalization m
  obtain ⟨b, hb, hbinv, _⟩ :=
    exists_measurable_labelClock_inverse hN ha hu.continuous.measurable hinj
  have hμlaw := populationConditionalWindowLaw_of_atlas P hF hcomplete hu ha hinj horder m κ hκ
    hprod ωM ρ₀ hρ₀ hρ₀nonneg (fun j ↦ v ((P j).toManifold (P j).center))
    (fun j ↦ hv _) (fun j ↦ hvolume _) hμcoverNat (μ.map a) rfl
  have hνlaw := populationConditionalWindowLaw_of_atlas P hF hcomplete hu ha hinj horder m κ hκ
    hprod ωM ρ₁ hρ₁ hρ₁nonneg (fun j ↦ v ((P j).toManifold (P j).center))
    (fun j ↦ hv _) (fun j ↦ hvolume _) hνcoverNat (μ.map a) hbalance.symm
  have hμseed (j : ℕ) (u₀ : ℝ) : PopulationSeedChartDensityLaw (P j).seed a (κ j)
      (μ.map a) μ ρ₀ v u₀ := by
    let _instSeedSourceHaar : (κ j).IsAddHaarMeasure := hκ j
    exact ae_populationSeedChart_conditional_density (P j).seed hF hcomplete hu ha hinj horder
      m (κ j) (hprod j) ωM ρ₀ hρ₀ hρ₀nonneg v hv hvolume (μ.map a) rfl
      hμlaw.joint_absolutelyContinuous hb hbinv hμN u₀
  have hνseed (j : ℕ) (u₀ : ℝ) : PopulationSeedChartDensityLaw (P j).seed a (κ j)
      (μ.map a) ν ρ₁ v u₀ := by
    let _instSeedTargetHaar : (κ j).IsAddHaarMeasure := hκ j
    exact ae_populationSeedChart_conditional_density (P j).seed hF hcomplete hu ha hinj horder
      m (κ j) (hprod j) ωM ρ₁ hρ₁ hρ₁nonneg v hv hvolume (μ.map a) hbalance.symm
      hνlaw.joint_absolutelyContinuous hb hbinv hνN u₀
  have hsupport := populationConditionalSupportLaw_of_physical_laws hμlaw hνlaw ha hF hcomplete hu
    horder hA hB hμ hν (by simpa only [hcoverNat] using hμcoverNat)
    (by simpa only [hcoverNat] using hνcoverNat)
  have hcomparison := hμlaw.ae_exists_supported_seed_comparison hsupport
    (fun j ↦ hμseed j (P j).seed.level) (fun j ↦ hνseed j (P j).seed.level)
    hF hcomplete hu ha hinj horder hκ
  refine ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
    P, κ, b, hcoverNat, hμcoverNat, hνcoverNat, hκ, hprod, hb, hbinv,
    fun j ↦ ⟨(hwindow (r j)).1, (hwindow (r j)).2.1⟩, hμlaw, hνlaw,
    ?_, ?_, hμseed, hνseed, hsupport, hcomparison⟩
  · exact populationFullWindowRestrictionLaw_of_atlas P hF hcomplete hu ha hinj horder m κ hκ
      hprod ωM ρ₀ hρ₀ hρ₀nonneg (fun j ↦ v ((P j).toManifold (P j).center))
      (fun j ↦ hv _) (fun j ↦ hvolume _) (μ.map a) hμlaw hb
      (hμN.mono fun x hx ↦ hbinv x hx)
  · exact populationFullWindowRestrictionLaw_of_atlas P hF hcomplete hu ha hinj horder m κ hκ
      hprod ωM ρ₁ hρ₁ hρ₁nonneg (fun j ↦ v ((P j).toManifold (P j).center))
      (fun j ↦ hv _) (fun j ↦ hvolume _) (μ.map a) hνlaw hb
      (hνN.mono fun x hx ↦ hbinv x hx)

end OTSelector.Reconstruction
