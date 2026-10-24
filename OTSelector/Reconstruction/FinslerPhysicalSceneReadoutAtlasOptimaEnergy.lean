import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutAtlasUniformEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutFixedOptimaEnergy

/-!
# One original Finsler atlas and all opposite global optimizer energies

Original physical population data construct the entire original MomentAtlas
package, its uniform empirical energy, and its measurable opposite-tilt global
optimizer families for every tilt index and sample size, all with one potential.
Every realized global allocation remains in the original target-times-Dirichlet
experiment with its actual columns.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open Filter OTSelector.Probability
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
theorem exists_finsler_original_atlas_opposite_global_energy (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
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
      (∃ C : ℝ, 0 < C ∧ PopulationUniformEnergyBound μ ν (Module.finrank ℝ E - 1)
        (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x) C) ∧
      (∀ (probe : M → M → ℝ) (G : ℝ≥0),
        Measurable (Function.uncurry probe) → (∀ x y, |probe x y| ≤ G) →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∃ t : ℕ → ℝ,
      ∃ aplus aminus : ∀ (_ℓ n : ℕ), ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
          M → Fin (n + 1) → ℝ,
      ∃ _hplus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
          (Fin (n + 1) → ℝ)) × M) ↦ aplus ℓ n z.1 z.2 j),
      ∃ _hminus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
          (Fin (n + 1) → ℝ)) × M) ↦ aminus ℓ n z.1 z.2 j),
        StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
        (∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist s (z.1 j)).toReal - u (z.1 j) + u s) +
              t ℓ * probe s (z.1 j)) (aplus ℓ n z) ∧
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist s (z.1 j)).toReal - u (z.1 j) + u s) +
              (-t ℓ) * probe s (z.1 j)) (aminus ℓ n z)) ∧
        ∀ ℓ n,
          ((∫⁻ z, ∫⁻ e, ENNReal.ofReal
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist e.1 (z.1 e.2)).toReal - u (z.1 e.2) + u e.1))
              ∂semidiscreteAllocationMeasure μ (aplus ℓ n z)
              ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C) ∧
          ((∫⁻ z, ∫⁻ e, ENNReal.ofReal
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist e.1 (z.1 e.2)).toReal - u (z.1 e.2) + u e.1))
              ∂semidiscreteAllocationMeasure μ (aminus ℓ n z)
              ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)) ∧
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
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨pot, a, hu, ⟨C₀, hC₀, hbound⟩, hN, hμreg, hνreg, ha, hinj, horder, hbalance, hface, hfull⟩ :=
    exists_finsler_original_atlas_uniform_energy hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
      hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₀L.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density ωM m hρ₁L.continuous.measurable hρ₁nonneg
      v hv hvolume
  have hopt := exists_finsler_given_potential_opposite_global_energy hF hcomplete (by omega)
    m μ ν hμchart hνchart hA hB hμ hν pot hu C₀ hbound
  exact ⟨pot, a, hu, ⟨C₀, hC₀, hbound⟩, hopt, hN, hμreg, hνreg, ha, hinj, horder, hbalance, hface, hfull⟩

end OTSelector.Reconstruction
