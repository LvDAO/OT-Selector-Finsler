import OTSelector.Reconstruction.FinslerScalarVolume
import OTSelector.Geometry.Finsler.CalibratedAtlas
import OTSelector.Geometry.Finsler.CalibratedSeedWindowVolume
import OTSelector.Geometry.Finsler.CalibratedSeedWindowLabels

/-!
# Original Finsler populations in actual measured calibrated coordinates

The original probabilities construct one optimal potential, geometric labels and
scalar conditional laws. The exact calibrated atlas covers both full marginals,
respects those same labels and transfers each original law by its actual coordinate
Radon--Nikodym density and normalized Jacobian. The entire original optimal face is
retained. No preassigned labels, coordinate laws or coverage assumptions are inputs.
-/

open Set MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace OTSelector.Reconstruction

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Geometry.ContinuousFinslerNorm E M}

/-- The same constructed optimal potential and geometric labels admit a countable
atlas carrying both full original marginals. Every seed label embeds measurably into
the original label space, and both actual laws have their exact weighted pullback.
The original scalar conditional laws and entire optimal-face representation persist. -/
theorem exists_finsler_measured_calibrated_atlas (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instMeasuredAtlasMetric : MetricSpace M := F.metricSpace
    let _instMeasuredAtlasProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instMeasuredAtlasBorel : StandardBorelSpace M := inferInstance
    let _instMeasuredAtlasNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
    ∃ (u : M → ℝ) (a : M → (ℚ → M)), LipschitzWith 1 u ∧
      MeasurableSet (F.potentialRegularDomain u) ∧
      (∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u) ∧
      (∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u) ∧ Measurable a ∧
      Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)) ∧
      (∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) ∧
      μ.map a = ν.map a ∧
      (∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ κ : Kernel (ℚ → M) (M × M), IsMarkovKernel κ ∧ κ ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂κ z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2) ∧
      (∀ᵐ x ∂μ, x ∈ calibratedInterior u) ∧
      (∀ᵐ y ∂ν, y ∈ calibratedInterior u) ∧
      μ.map (fun x ↦ (a x, u x)) ≪ (μ.map a).prod volume ∧
      ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume ∧
      (∀ᵐ z ∂μ.map a,
        condDistrib u a μ z ≪ volume ∧ condDistrib u a ν z ≪ volume ∧
        (condDistrib id a μ z).map u ≪ volume ∧
        (condDistrib id a ν z).map u ≪ volume) ∧
      ∃ ι : Type (max u v), Countable ι ∧
        ∃ P : ι → F.CalibratedSeedWindow u,
          (⋃ i, (P i).toManifold '' (P i).domain) = calibratedInterior u ∧
          (∀ᵐ x ∂μ, x ∈ ⋃ i, (P i).toManifold '' (P i).domain) ∧
          (∀ᵐ y ∂ν, y ∈ ⋃ i, (P i).toManifold '' (P i).domain) ∧
          ∀ i,
            (∀ z ∈ (P i).domain,
              a ((P i).toManifold z) = a ((P i).seed.curve z.2 0)) ∧
            MeasurableEmbedding (fun w : (P i).labels ↦ a ((P i).seed.curve w 0)) ∧
            ∀ η : Measure M, η = μ ∨ η = ν →
              let χ := extChartAt 𝓘(ℝ, E) ((P i).toManifold (P i).center)
              let ρ := ((η.restrict χ.source).map χ).rnDeriv m
              let μpar := tubeParameterMeasure (P i).seed.normalization m
              η.comap (fun z : (P i).domain ↦ (P i).toManifold z) =
                (μpar.comap ((↑) : (P i).domain → ℝ × (P i).seed.covector.ker)).withDensity
                  (fun z ↦ ENNReal.ofReal
                    (parameterizedJacobian (P i).readout (P i).seed.normalization z) *
                    ρ ((P i).readout z)) := by
  let _instMeasuredAtlasMetric : MetricSpace M := F.metricSpace
  let _instMeasuredAtlasProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instMeasuredAtlasBorel : StandardBorelSpace M := inferInstance
  let _instMeasuredAtlasNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
      hμI, hνI, hμjoint, hνjoint, hcond⟩ :=
    exists_finsler_scalar_volume_disintegration hF hcomplete m μ ν
      hμchart hνchart hA hB hAB hμ hν
  obtain ⟨ι, hι, P, hcover⟩ := hF.exists_countable_calibratedWindow_atlas hcomplete hu
  refine ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
    hμI, hνI, hμjoint, hνjoint, hcond, ι, hι, P, hcover, ?_, ?_, ?_⟩
  · simpa only [hcover] using hμI
  · simpa only [hcover] using hνI
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (P i).label_toManifold_eq_initial hF hcomplete hu horder hz
    · exact (P i).measurableEmbedding_seedLabel hF hcomplete hu ha hinj
    · intro η hη
      rcases hη with hη | hη
      · subst η
        exact (P i).comap_toManifold_eq_withDensity_chartDensity hF hcomplete hu m μ
          (hμchart ((P i).toManifold (P i).center))
      · subst η
        exact (P i).comap_toManifold_eq_withDensity_chartDensity hF hcomplete hu m ν
          (hνchart ((P i).toManifold (P i).center))

end OTSelector.Reconstruction
