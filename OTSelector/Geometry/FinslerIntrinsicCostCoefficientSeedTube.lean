import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeedNormal
import OTSelector.Geometry.FinslerSeedActiveJacobian
import OTSelector.Geometry.Finsler.SmoothTubeCalibration
import OTSelector.Geometry.FinslerIntrinsicCostCoefficient

/-!
# True normal tubes from actual seed geometry

The original active-window Jacobian gives the centered comparison's actual position
rank. Its all-label normality constructs a smooth calibrated tube on every compact
inner time interval. Arbitrary calibrated outer endpoints are retained.
-/

open Set Filter Metric MeasureTheory Manifold Bundle Module Asymptotics
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] in
/-- Original physical Jacobian positivity supplies the centered family's actual
position rank in every legal chart. -/
theorem centered_position_rank_of_original_jacobian (S : CalibratedLevelSeedPatch F u)
    {w : S.covector.ker} {Γ : S.covector.ker → ℝ → M} (t : ℝ)
    (hcurve : S.curve w = Γ 0)
    (hjet : ∀ old, Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old (fun z ↦ S.curve (w + z)))
        (fderiv ℝ (F.chartMomentumFamily old Γ) (0, t)) (0, t) ∧
      HasFDerivAt (F.chartMomentumFamily old Γ)
        (fderiv ℝ (F.chartMomentumFamily old Γ) (0, t)) (0, t))
    (hpos : ∀ old, S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      0 < parameterizedJacobian (fun q : ℝ × S.covector.ker ↦
        extChartAt 𝓘(ℝ, E) old (S.curve q.2 q.1)) S.normalization (t, w)) :
    HasInjectiveManifoldPosition (E := E) (fun z ↦ Γ z t) 0 := by
  intro old hx
  obtain ⟨h₁, h₂⟩ := hjet old hx
  have hOriginal := chartMomentum_hasFDerivAt_of_label_add old w t h₁
  let swap := ContinuousLinearEquiv.prodComm ℝ ℝ S.covector.ker
  have htime := hOriginal.fst.comp (t, w) swap.hasFDerivAt
  have hi := injective_fderiv_of_parameterizedJacobian_pos S.normalization
    (hpos old (by rwa [hcurve]))
  have hline : HasFDerivAt (fun z : S.covector.ker ↦ (z, t))
      ((ContinuousLinearMap.id ℝ S.covector.ker).prod
        (0 : S.covector.ker →L[ℝ] ℝ)) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : S.covector.ker)).prodMk (hasFDerivAt_const t 0)
  have hlabel := HasFDerivAt.comp (f := fun z : S.covector.ker ↦ (z, t))
    (g := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)) 0 h₂.fst hline
  have htimeD : fderiv ℝ (fun q : ℝ × S.covector.ker ↦
      extChartAt 𝓘(ℝ, E) old (S.curve q.2 q.1)) (t, w) =
      ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
        (fderiv ℝ (F.chartMomentumFamily old Γ) (0, t))).comp
          swap.toContinuousLinearMap := htime.fderiv
  have hlabelD : fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ fun z ↦ Γ z t) 0 =
      ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
        (fderiv ℝ (F.chartMomentumFamily old Γ) (0, t))).comp
          ((ContinuousLinearMap.id ℝ S.covector.ker).prod
            (0 : S.covector.ker →L[ℝ] ℝ)) := hlabel.fderiv
  intro ξ η hξη
  have heq : ((0 : ℝ), ξ) = (0, η) := hi (by
    rw [htimeD]
    rw [hlabelD] at hξη
    exact hξη)
  exact congrArg Prod.snd heq

omit [BorelSpace E] in
/-- Actual original calibration and Jacobian positivity construct the same normal
family's calibrated tube on every strictly ordered inner active interval. -/
theorem nonempty_calibratedTube_normalPotentialFamily
    (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instNormalTubeLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (N : F.NormalPotentialFamily D.initialChart
      (D.position w, fderiv ℝ D.potential (D.position w)) (fderiv ℝ D.position w) Q S.level)
    (hcurve : S.curve w = N.curve 0)
    (hjet : ∀ old t, N.curve 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old (fun z ↦ S.curve (w + z)))
        (fderiv ℝ (F.chartMomentumFamily old N.curve) (0, t)) (0, t) ∧
      HasFDerivAt (F.chartMomentumFamily old N.curve)
        (fderiv ℝ (F.chartMomentumFamily old N.curve) (0, t)) (0, t))
    (hpos : ∀ old t, t ∈ interior (S.calibrationTimes w) →
      S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      0 < parameterizedJacobian (fun q : ℝ × S.covector.ker ↦
        extChartAt 𝓘(ℝ, E) old (S.curve q.2 q.1)) S.normalization (t, w))
    {a b : ℝ} (hab : a < b)
    (ha : a ∈ interior (S.calibrationTimes w)) (hb : b ∈ interior (S.calibrationTimes w)) :
    Nonempty (F.CalibratedTube N.curve a b u) := by
  let _instNormalTubeMetric : MetricSpace M := F.metricSpace
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hb)
  let l := a - ε / 2
  let r := b + η / 2
  have hl : l ∈ S.calibrationTimes w := hεball (by
    rw [mem_ball, Real.dist_eq]
    have he : l - a = -(ε / 2) := by dsimp only [l]; ring
    rw [he, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  have hr : r ∈ S.calibrationTimes w := hηball (by
    rw [mem_ball, Real.dist_eq]
    have he : r - b = η / 2 := by dsimp only [r]; ring
    rw [he, abs_of_pos (half_pos hη)]
    exact half_lt_self hη)
  have hla : l < a := by dsimp only [l]; linarith
  have hbr : b < r := by dsimp only [r]; linarith
  have houter := hF.calibrated_window_of_complete_unit_endpoints hu
    (S.complete w hw) (S.unit w hw) hl hr
  have hactive : Ioo l r ⊆ interior (S.calibrationTimes w) :=
    interior_maximal (Ioo_subset_Icc_self.trans houter.1) isOpen_Ioo
  have hseg : Icc a b ⊆ Ioo l r :=
    fun _ ht ↦ ⟨hla.trans_le ht.1, ht.2.trans_lt hbr⟩
  have hregular (t : ℝ) (ht : t ∈ Icc a b) :
      HasInjectiveManifoldPosition (E := E) (fun z ↦ N.curve z t) 0 :=
    S.centered_position_rank_of_original_jacobian t hcurve (fun old ↦ hjet old t)
      (fun old ↦ hpos old t (hactive (hseg ht)))
  have hiso : Isometry (fun t : Icc l r ↦ N.curve 0 t) := by
    simpa only [hcurve] using houter.2.1
  have hdim : Module.finrank ℝ S.covector.ker + 1 = Module.finrank ℝ E := by
    have hh := S.normalization.toLinearEquiv.finrank_eq
    simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using hh
  obtain ⟨T, V, Y, _, _, hJT, h0V, hTV, hYeq, hYs, _, hY, hi, _, hbound, _⟩ :=
    hF.exists_smooth_manifoldTube_calibration hdim N.open_labels N.complete N.tangent_smooth
      N.energy_eq (fun z hz t old ↦ N.normal z hz old t) N.anchor_mem hiso isCompact_Icc
        (fun _ ht ↦ ⟨(hseg ht).1.le, (hseg ht).2.le⟩) hregular 0
  have hstay (t : ℝ) (ht : t ∈ Icc a b) : (t, (0 : S.covector.ker)) ∈ Y.source := by
    rw [hYs]
    exact ⟨hJT ht, h0V⟩
  have hca : u (S.curve w a) = (S.level : ℝ) + a :=
    (show a ∈ S.calibrationTimes w from interior_subset ha)
  have hcb : u (S.curve w b) = (S.level : ℝ) + b :=
    (show b ∈ S.calibrationTimes w from interior_subset hb)
  have hinner := hF.calibrated_window_of_complete_unit_endpoints hu
    (S.complete w hw) (S.unit w hw) hca hcb
  have hdist : dist (N.curve 0 a) (N.curve 0 b) = b - a := by
    simpa only [hcurve, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub] using
      hinner.2.1.dist_eq ⟨a, left_mem_Icc.mpr hab.le⟩ ⟨b, right_mem_Icc.mpr hab.le⟩
  refine ⟨{
    toOpenPartialHomeomorph := Y, smooth := hY, smooth_symm := hi, coe_eq := hYeq
    energy_eq := ?_, timeOrigin := 0, covector_le := hbound, ordered := hab
    stay := hstay, minimizing := ?_, saturation := ?_, differentiable := ?_ }⟩
  · intro q hq
    rw [hYs] at hq
    exact N.energy_eq q.2 (hTV hq).2 q.1
  · apply hF.lengthEDist_eq_pathELength_of_isometric_interval hab.le
    simpa only [hcurve] using hinner.2.1
  · rw [← hcurve, hca, hcb, hcurve, hdist]
    ring
  · apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    rw [← hcurve]
    exact houter.2.2 a ⟨hla, hab.trans hbr⟩

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
