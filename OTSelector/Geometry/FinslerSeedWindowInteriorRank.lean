import OTSelector.Geometry.FinslerSeedWindowLowerBound
import OTSelector.Analysis.Calculus.ImmersionCenteredLowerBound
import OTSelector.Geometry.FinslerSeedPatchSmoothComparison
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Analysis.Calculus.DensityOneLowerDerivative

/-!
# Interior position rank of the original calibrated seed windows

The actual section immersion and compact screened label neighborhoods supply
centered reverse-flow bounds throughout the original calibrated time interval.
Label density one passes these bounds to the actual position derivatives.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- Screening the original labels by calibration endpoints remains closed inside
any closed label ball contained in the original open section domain. -/
theorem isCompact_closedBall_inter_labels (P : CalibratedSeedWindow F u)
    (D : C11LevelSeedPresentation F u P.seed.covector P.seed.level
      P.seed.openLabels P.seed.labels P.seed.curve)
    (hu : let _instSeedCompactLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : P.seed.covector.ker} {r : ℝ}
    (hball : closedBall w r ⊆ P.seed.openLabels) :
    IsCompact (closedBall w r ∩ P.labels) := by
  let _instSeedCompactMetric : MetricSpace M := F.metricSpace
  have hc : IsClosed (closedBall w r ∩ P.labels) := by
    apply isClosed_closedBall.inter_preimage_val_iff.mp
    have hposition : Continuous (fun z : closedBall w r ↦ D.position z) :=
      continuousOn_iff_continuous_domRestrict.mp (D.position_contDiff.continuousOn.mono hball)
    have htime (t : ℝ) : Continuous (fun z : closedBall w r ↦ u (P.seed.curve z t)) :=
      continuousOn_iff_continuous_domRestrict.mp
        ((hu.continuous.comp_continuousOn (P.seed.continuous_at_time t)).mono hball)
    have heq : (fun z : closedBall w r ↦ (z : P.seed.covector.ker)) ⁻¹' P.labels =
        {z : closedBall w r | D.position z ∈ D.core ∧
          u (P.seed.curve z P.left) = (P.seed.level : ℝ) + P.left ∧
          u (P.seed.curve z P.right) = (P.seed.level : ℝ) + P.right} := by
      ext z
      simp only [labels, mem_preimage, mem_inter_iff, mem_ofPred_eq, D.labels_eq]
      exact and_congr_left (fun _ ↦ and_iff_right (hball z.property))
    rw [heq]
    exact (D.core_compact.isClosed.preimage hposition).inter
      ((isClosed_eq (htime P.left) continuous_const).inter
        (isClosed_eq (htime P.right) continuous_const))
  exact (isCompact_closedBall w r).of_isClosed_subset hc inter_subset_left

omit [BorelSpace E] in
/-- Every original interior time has an actual centered inverse estimate on the
same screened labels, with no supplied target regularity or rank condition. -/
theorem exists_centered_lower_bound (P : CalibratedSeedWindow F u)
    (D : C11LevelSeedPresentation F u P.seed.covector P.seed.level
      P.seed.openLabels P.seed.labels P.seed.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedWindowLowerLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : P.seed.covector.ker} (hw : w ∈ P.labels) (terminal : M)
    {t : ℝ} (ht : t ∈ Ioo (P.left : ℝ) P.right)
    (hlegal : P.seed.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝[P.labels] w,
      c * ‖z - w‖ ≤ ‖extChartAt 𝓘(ℝ, E) terminal (P.seed.curve z t) -
        extChartAt 𝓘(ℝ, E) terminal (P.seed.curve w t)‖ := by
  let _instSeedWindowLowerMetric : MetricSpace M := F.metricSpace
  have hwU : w ∈ P.seed.openLabels := P.seed.labels_subset hw.1
  have hs := (D.position_contDiff.contDiffAt
    (P.seed.openLabels_open.mem_nhds hwU)).differentiableAt one_ne_zero
  obtain ⟨C, hC, hlower⟩ := exists_centered_inverse_bound_of_hasFDerivAt
    hs.hasFDerivAt (D.position_immersion w hwU)
  have hsource : ∀ᶠ z in 𝓝 w,
      P.seed.curve z t ∈ (extChartAt 𝓘(ℝ, E) terminal).source :=
    ((P.seed.continuous_at_time t).continuousAt (P.seed.openLabels_open.mem_nhds hwU))
      ((isOpen_extChartAt_source terminal).mem_nhds hlegal)
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (P.seed.openLabels_open.mem_nhds hwU) (hsource.and hlower))
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hball : closedBall w r ⊆ ball w R :=
    closedBall_subset_ball (half_lt_self hR)
  let K := closedBall w r ∩ P.labels
  have hKU : closedBall w r ⊆ P.seed.openLabels := fun z hz ↦ (hRsub (hball hz)).1
  have hK : IsCompact K := P.isCompact_closedBall_inter_labels D hu hKU
  have hwK : w ∈ K := ⟨mem_closedBall_self hr.le, hw⟩
  have hKsource : ∀ z ∈ K, P.seed.curve z t ∈
      (extChartAt 𝓘(ℝ, E) terminal).source := fun z hz ↦ (hRsub (hball hz.1)).2.1
  have hinit : ∀ z ∈ K, P.seed.curve z 0 =
      (extChartAt 𝓘(ℝ, E) D.initialChart).symm (D.position z) := by
    intro z hz
    exact (congrFun (congrFun D.curve_eq z) 0).trans
      (D.ambient_initial (D.position z) (D.position_domain (hKU hz.1)))
  have hcal (z : P.seed.covector.ker) (hz : z ∈ K) :=
    hF.calibrated_window_of_complete_unit_endpoints hu
      (P.seed.complete z hz.2.1) (P.seed.unit z hz.2.1) hz.2.2.1 hz.2.2.2
  have hT : ContinuousOn
      (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (P.seed.curve z t)) K :=
    (continuousOn_extChartAt terminal).comp
      ((P.seed.continuous_at_time t).mono (fun z hz ↦ hKU hz.1)) hKsource
  obtain ⟨c, hc, hbound⟩ := hF.exists_centered_lower_bound_of_compact_calibrated_window
    hcomplete D.initialChart terminal hu hK hwK
    (fun z hz ↦ D.domain_target (D.position_domain (hKU hz.1))) hC.le
    (fun z hz ↦ (hRsub (hball hz.1)).2.2) ht
    (fun z hz ↦ P.seed.complete z hz.2.1) hinit hKsource
    (fun z hz ↦ P.seed.unit z hz.2.1 t) (fun z hz ↦ (hcal z hz).2.1)
    (fun z hz ↦ (hcal z hz).1) hT
  refine ⟨c, hc, ?_⟩
  have heq : 𝓝[P.labels] w = 𝓝[K] w := by
    change 𝓝[P.labels] w = 𝓝[closedBall w r ∩ P.labels] w
    rw [inter_comm]
    exact (nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds
      (closedBall_mem_nhds w hr))).symm
  rwa [heq]

/-- Density one turns the actual interior reverse estimate into injectivity of
any genuine position derivative on the original screened labels. -/
theorem injective_position_derivative_of_density_one (P : CalibratedSeedWindow F u)
    (D : C11LevelSeedPresentation F u P.seed.covector P.seed.level
      P.seed.openLabels P.seed.labels P.seed.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedRankLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure P.seed.covector.ker) [m.IsAddHaarMeasure]
    {w : P.seed.covector.ker} (hw : w ∈ P.labels)
    (hdensity : Tendsto (fun r ↦ m (P.labels ∩ closedBall w r) / m (closedBall w r))
      (𝓝[>] 0) (𝓝 1)) (terminal : M)
    {t : ℝ} (ht : t ∈ Ioo (P.left : ℝ) P.right)
    (hlegal : P.seed.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    {R : P.seed.covector.ker →L[ℝ] E}
    (hR : HasFDerivWithinAt
      (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (P.seed.curve z t)) R P.labels w) :
    Function.Injective R := by
  obtain ⟨c, hc, hbound⟩ := P.exists_centered_lower_bound D hF hcomplete hu hw terminal ht
    hlegal
  exact injective_of_density_one_lower_bound m hdensity hR hc hbound

/-- One full-measure set of original labels has injective position derivatives at
every interior time, in every chart containing that original point. The same smooth
comparison retains the original central curve and every joint phase first jet. -/
theorem ae_exists_comparison_interior_position_rank (P : CalibratedSeedWindow F u)
    (D : C11LevelSeedPresentation F u P.seed.covector P.seed.level
      P.seed.openLabels P.seed.labels P.seed.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedRankAELip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure P.seed.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict P.labels,
      let R := fderiv ℝ D.position w
      let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
      let p := (D.position w, fderiv ℝ D.potential (D.position w))
      w ∈ P.labels ∧
        ∃ C : F.SmoothPhaseJetComparison D.initialChart 0 w p R Q,
          C.labels ⊆ P.seed.openLabels ∧ P.seed.curve w = C.curve w ∧
          (∀ (terminal : M) (t : ℝ),
            P.seed.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
            HasFDerivAt (F.chartMomentumFamily terminal P.seed.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t) ∧
            HasFDerivAt (F.chartMomentumFamily terminal C.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t)) ∧
          ∀ (terminal : M) (t : ℝ), t ∈ Ioo (P.left : ℝ) P.right →
            P.seed.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
            Function.Injective (fderiv ℝ
              (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (P.seed.curve z t)) w) := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (show P.labels ⊆ P.seed.labels from inter_subset_left)
    (P.seed.ae_exists_smoothPhaseJetComparison D hF hcomplete m),
    Besicovitch.ae_tendsto_measure_inter_div m P.labels,
    ae_restrict_mem (P.measurableSet_labels hu)] with w hcomparison hdensity hw
  obtain ⟨_, C, hsub, hcurve, hjet⟩ := hcomparison
  refine ⟨hw, C, hsub, hcurve, hjet, ?_⟩
  intro terminal t ht hlegal
  have hposition : DifferentiableAt ℝ
      (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (P.seed.curve z t)) w := by
    apply DifferentiableAt.comp w
      (f := fun z : P.seed.covector.ker ↦ (z, t))
      (g := fun q : P.seed.covector.ker × ℝ ↦
        extChartAt 𝓘(ℝ, E) terminal (P.seed.curve q.1 q.2))
    · exact (hjet terminal t hlegal).1.fst.differentiableAt
    · exact differentiableAt_id.prodMk (differentiableAt_const t)
  exact P.injective_position_derivative_of_density_one D hF hcomplete hu m hw hdensity
    terminal ht hlegal hposition.hasFDerivAt.hasFDerivWithinAt

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow
