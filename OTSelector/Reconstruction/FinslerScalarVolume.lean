import OTSelector.Geometry.Finsler.Calibration.GeometricDisintegration
import OTSelector.Geometry.Finsler.FullScalarAbsoluteContinuity

/-!
# Constructed original Finsler scalar volume and the entire optimal face

The original compactly supported probabilities construct their optimal potential and
geometric labels. An actual original optimizer and its conditional representation give
calibration for that same potential. Geometric endpoint nullity then gives full original
interior mass and unrestricted scalar absolute continuity. The same potential, labels,
common label law and entire optimal-face representation are retained throughout.
-/

open Set MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Geometry.ContinuousFinslerNorm E M}

/-- Original chartwise absolutely continuous probabilities on disjoint compact carriers
construct one potential and geometric label system with full interior mass, original
scalar conditional densities, and the exact representation of every distance-optimal
coupling. No labels, calibrated plan, endpoint-nullity or conditional-volume hypothesis
are supplied. Both direct scalar conditionals and clock pushforwards of the original
conditional position laws are absolutely continuous at the same common labels. -/
theorem exists_finsler_scalar_volume_disintegration (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instScalarVolumeStatementMetric : MetricSpace M := F.metricSpace
    let _instScalarVolumeStatementProper : ProperSpace M :=
      F.properSpace_of_complete hcomplete
    let _instScalarVolumeStatementBorel : StandardBorelSpace M := inferInstance
    let _instScalarVolumeStatementNonempty : Nonempty M :=
      nonempty_of_isProbabilityMeasure μ
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
      ∀ᵐ z ∂μ.map a,
        condDistrib u a μ z ≪ volume ∧ condDistrib u a ν z ≪ volume ∧
        (condDistrib id a μ z).map u ≪ volume ∧
        (condDistrib id a ν z).map u ≪ volume := by
  let _instScalarVolumeMetric : MetricSpace M := F.metricSpace
  let _instScalarVolumeProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScalarVolumeBorel : StandardBorelSpace M := inferInstance
  let _instScalarVolumeNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface⟩ :=
    exists_finsler_geometric_disintegration hF hcomplete m μ ν
      hμchart hνchart hA hB hAB hμ hν
  obtain ⟨π₀, hπ₀⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν (hA.union hB)
    (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
  obtain ⟨κ, _, hcomp, hsupp⟩ := (hface π₀).mp hπ₀
  have hcalset : MeasurableSet {p : M × M | u p.2 - u p.1 = dist p.1 p.2} :=
    measurableSet_eq_fun
      ((hu.continuous.measurable.comp measurable_snd).sub
        (hu.continuous.measurable.comp measurable_fst))
      (continuous_fst.dist continuous_snd).measurable
  have hcal : ∀ᵐ p ∂π₀, u p.2 - u p.1 = dist p.1 p.2 := by
    rw [← hcomp]
    apply Measure.ae_comp_of_ae_ae hcalset
    filter_upwards [hsupp] with z hz
    exact hz.2.mono fun p hp ↦
      (horder p.1 hp.1 p.2 hp.2.1).mp ⟨hp.2.2.1, hp.2.2.2⟩
  obtain ⟨hμI, hνI⟩ := hF.ae_calibratedInterior_of_calibrated_coupling
    hcomplete m μ ν hμchart hνchart hu ha horder hπ₀.1 hcal hAB hμ hν
  obtain ⟨hμjoint, hνjoint⟩ :=
    hF.map_label_potential_absolutelyContinuous_of_calibrated_coupling
      hcomplete m μ ν hμchart hνchart hu ha horder hπ₀.1 hcal hAB hμ hν
  obtain ⟨hμcond, hνcond⟩ :=
    hF.ae_scalarConditionals_absolutelyContinuous_of_calibrated_coupling
      hcomplete m μ ν hμchart hνchart hu ha horder hπ₀.1 hcal hAB hμ hν
  rw [← hbalance] at hνcond
  refine ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
    hμI, hνI, hμjoint, hνjoint, ?_⟩
  filter_upwards [hμcond, hνcond] with z hμz hνz
  exact ⟨hμz.1, hνz.1, hμz.2, hνz.2⟩

end OTSelector.Reconstruction
