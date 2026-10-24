import OTSelector.Geometry.FinslerSeedPatchRegularity
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Analysis.Calculus.DensityOneDifferential
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual energy-tangent initial jets on original seed labels

The original unit curves put their actual phase on energy one half in every legal
Legendre inverse branch. At label density-one points the derivative of this energy
constraint vanishes. Together with label Rademacher, this produces the normal,
immersed, isotropic and energy-tangent initial data for smooth comparison families.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

private theorem seed_density_one_inter_open
    {W : Type*} [PseudoMetricSpace W] [MeasurableSpace W]
    (m : Measure W) {K V : Set W} {w : W}
    (hw : Tendsto (fun r ↦ m (K ∩ closedBall w r) / m (closedBall w r))
      (𝓝[>] 0) (𝓝 1)) (hV : IsOpen V) (hwV : w ∈ V) :
    Tendsto (fun r ↦ m ((K ∩ V) ∩ closedBall w r) / m (closedBall w r))
      (𝓝[>] 0) (𝓝 1) := by
  apply hw.congr'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hwV)
  filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hε)] with r hr
  have hclosed : closedBall w r ⊆ V := fun z hz ↦
    hball ((mem_closedBall.mp hz).trans_lt hr)
  have heq : (K ∩ V) ∩ closedBall w r = K ∩ closedBall w r := by
    ext z
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hclosed h.2⟩, h.2⟩⟩
  rw [heq]

namespace ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The retained original curve starts inside the chart used by its C1,1 data. -/
theorem initial_mem_chart_source (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    {w : S.covector.ker} (hw : w ∈ S.openLabels) :
    S.curve w 0 ∈ (extChartAt 𝓘(ℝ, E) D.initialChart).source := by
  have hc : S.curve w 0 = D.ambient (D.position w) 0 :=
    congrFun (congrFun D.curve_eq w) 0
  rw [hc, D.ambient_initial (D.position w) (D.position_domain hw)]
  exact (extChartAt 𝓘(ℝ, E) D.initialChart).map_target
    (D.domain_target (D.position_domain hw))

omit [BorelSpace E] in
/-- Every legal inverse branch reads energy one half on the original seed labels. -/
theorem initial_localHamiltonian_eq_half (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy D.initialChart))
    (hsource : e.source ⊆ chartEnergyDomain D.initialChart)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (hp : (D.position w, fderiv ℝ D.potential (D.position w)) ∈ e.target) :
    localHamiltonian (F.chartEnergy D.initialChart) e
      (D.position w, fderiv ℝ D.potential (D.position w)) = (1 / 2 : ℝ) := by
  let z : E × E := ((extChartAt 𝓘(ℝ, E) D.initialChart ∘ S.curve w) 0,
    deriv (extChartAt 𝓘(ℝ, E) D.initialChart ∘ S.curve w) 0)
  have hs := S.initial_mem_chart_source D (S.labels_subset hw)
  have ht := hF.chartTangent_of_isEulerLagrangeAt
    (S.complete w hw 0 (mem_univ _)) D.initialChart hs
  have hinverse : e.symm (D.position w, fderiv ℝ D.potential (D.position w)) = z := by
    apply hF.injOn_parametricLegendre_chartEnergy D.initialChart
      (hsource (e.map_target hp)) ht.2
    calc
      parametricLegendre (F.chartEnergy D.initialChart)
          (e.symm (D.position w, fderiv ℝ D.potential (D.position w))) =
          (D.position w, fderiv ℝ D.potential (D.position w)) := by
        simpa only [he] using e.right_inv hp
      _ = parametricLegendre (F.chartEnergy D.initialChart) z :=
        (S.initial_phase_eq D (S.labels_subset hw)).symm
  rw [hF.localHamiltonian_chartEnergy_eq D.initialChart he hsource hp, hinverse]
  have henergy : F.chartEnergy D.initialChart z =
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (S.curve w) ⟨0, (1 : ℝ)⟩) := by
    unfold ContinuousFinslerNorm.chartEnergy
    rw [show z = _ from ht.1.symm, (extChartAt _ _).left_inv]
    simpa only [FiberBundle.chartedSpace_chartAt, mfld_simps] using hs
  rw [henergy, ContinuousFinslerNorm.energy, S.unit w hw 0]
  norm_num

/-- At a genuine label density-one point, the actual phase jet is tangent to
energy one half on any smooth legal inverse branch. -/
theorem initial_energy_tangent_of_density_one (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex) (m : Measure S.covector.ker) [m.IsAddHaarMeasure]
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (hdensity : Tendsto
      (fun r ↦ m (S.labels ∩ closedBall w r) / m (closedBall w r))
      (𝓝[>] 0) (𝓝 1))
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy D.initialChart))
    (hsource : e.source ⊆ chartEnergyDomain D.initialChart)
    (hInv : ContDiffOn ℝ ∞ e.symm e.target)
    (hp : (D.position w, fderiv ℝ D.potential (D.position w)) ∈ e.target) :
    (fderiv ℝ (localHamiltonian (F.chartEnergy D.initialChart) e)
      (D.position w, fderiv ℝ D.potential (D.position w))).comp
        ((fderiv ℝ D.position w).prod Q) = 0 := by
  let p := fun z ↦ (D.position z, fderiv ℝ D.potential (D.position z))
  have hs := (D.position_contDiff.contDiffAt
    (S.openLabels_open.mem_nhds (S.labels_subset hw))).differentiableAt one_ne_zero
  have hpd : HasFDerivAt p ((fderiv ℝ D.position w).prod Q) w :=
    hs.hasFDerivAt.prodMk hQ
  let V := S.openLabels ∩ p ⁻¹' e.target
  have hpc : ContinuousOn p S.openLabels := D.position_contDiff.continuousOn.prodMk
    ((D.potential_contDiff.continuous_fderiv one_ne_zero).comp_continuousOn
      D.position_contDiff.continuousOn)
  have hV : IsOpen V := hpc.isOpen_inter_preimage S.openLabels_open e.open_target
  have hwV : w ∈ V := ⟨S.labels_subset hw, hp⟩
  have hH := ((contDiffOn_localHamiltonian
    ((hF.contDiffOn_chartEnergy D.initialChart).mono hsource) hInv).contDiffAt
      (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  apply hasFDerivAt_eq_zero_of_density_one m
    (seed_density_one_inter_open m hdensity hV hwV) (hH.hasFDerivAt.comp w hpd)
  intro z hz
  exact (S.initial_localHamiltonian_eq_half D hF he hsource hz.1 hz.2.2).trans
    (S.initial_localHamiltonian_eq_half D hF he hsource hw hp).symm

/-- Almost every original label supplies its actual normal, immersed, isotropic
phase jet and a constructed smooth inverse branch on which the jet is energy-tangent. -/
theorem ae_initial_phase_regular_energy (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex) (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.labels,
      let R := fderiv ℝ D.position w
      let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
      let p := (D.position w, fderiv ℝ D.potential (D.position w))
      w ∈ S.labels ∧
        Tendsto (fun r ↦ m (S.labels ∩ closedBall w r) / m (closedBall w r))
          (𝓝[>] 0) (𝓝 1) ∧
        Function.Injective R ∧ p.2.comp R = 0 ∧
        HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w ∧
        HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart S.curve (z, 0))
          (R.prod Q) w ∧
        (∀ ξ η, canonicalPhasePairing (R.prod Q ξ) (R.prod Q η) = 0) ∧
        ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
          (e : E × E → E × (E →L[ℝ] ℝ)) =
            parametricLegendre (F.chartEnergy D.initialChart) ∧
          e.source ⊆ chartEnergyDomain D.initialChart ∧
          ContDiffOn ℝ ∞ e.symm e.target ∧ p ∈ e.target ∧
          localHamiltonian (F.chartEnergy D.initialChart) e p = (1 / 2 : ℝ) ∧
          (fderiv ℝ (localHamiltonian (F.chartEnergy D.initialChart) e) p).comp
            (R.prod Q) = 0 := by
  filter_upwards [S.ae_initial_phase_regular D m,
    Besicovitch.ae_tendsto_measure_inter_div m S.labels] with w hregular hdensity
  obtain ⟨hw, hR, hnormal, hQ, hphase, hiso⟩ := hregular
  have hs := S.initial_mem_chart_source D (S.labels_subset hw)
  have ht := hF.chartTangent_of_isEulerLagrangeAt
    (S.complete w hw 0 (mem_univ _)) D.initialChart hs
  obtain ⟨e, he, _, htarget, hsource, _, hInv, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse D.initialChart ht.2
  have hp : (D.position w, fderiv ℝ D.potential (D.position w)) ∈ e.target := by
    rw [← S.initial_phase_eq D (S.labels_subset hw)]
    exact htarget
  exact ⟨hw, hdensity, hR, hnormal, hQ, hphase, hiso,
    e, he, hsource, hInv, hp, S.initial_localHamiltonian_eq_half D hF he hsource hw hp,
    S.initial_energy_tangent_of_density_one D hF m hw hdensity hQ he hsource hInv hp⟩

end ContinuousFinslerNorm.CalibratedLevelSeedPatch
end OTSelector.Geometry
