import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeedState
import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeedTube
import OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalAction
import OTSelector.Geometry.FinslerIntrinsicCostCoefficientTransfer

/-!
# The actual original seed distance has its intrinsic compliance coefficient

The original endpoints are retained, with their original potential deficit and
original time. Allowed neighboring labels need only carry the two specified clocks.
The coefficient is the inverse integral of the literal original seed kernel.
-/

open Set Filter MeasureTheory Manifold Bundle Module Asymptotics
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Neighboring original labels for which both actual endpoint clocks hold. -/
def distanceExpansionLabels (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (a b : ℝ) : Set S.covector.ker :=
  {z | w + z ∈ S.labels ∧ a ∈ S.calibrationTimes (w + z) ∧ b ∈ S.calibrationTimes (w + z)}

omit [BorelSpace E] in
/-- A true normal comparison transfers its distance expansion back to the actual
original seed and the literal original-time compliance matrix. -/
theorem distance_deficit_intrinsic_quadratic_of_normalPotentialFamily
    (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedDistanceLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (bW : Basis ι ℝ S.covector.ker)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w)
    (N : F.NormalPotentialFamily D.initialChart
      (D.position w, fderiv ℝ D.potential (D.position w)) (fderiv ℝ D.position w) Q S.level)
    (hPG : (fun z ↦ D.potential (D.position z) -
      secondJetPolynomial (D.position w) S.level
        (fderiv ℝ D.potential (D.position w)) N.hessian (D.position z)) =o[𝓝 w]
          (fun z ↦ ‖z - w‖ ^ 2))
    (hH : ∀ t : ℝ,
      F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, t) =
        F.familyLabelHessianMatrix bW (fun q ↦ N.curve q.1 q.2) (0, t))
    {a b : ℝ} (T : F.CalibratedTube N.curve a b u) :
    (fun ξ : S.covector.ker × S.covector.ker ↦
      ((F.lengthEDist (S.curve (w + ξ.1) a) (S.curve (w + ξ.2) b)).toReal -
        u (S.curve (w + ξ.2) b) + u (S.curve (w + ξ.1) a)) -
        F.intrinsicLengthQuadratic bW S.curve w a b ξ)
      =o[𝓝[S.distanceExpansionLabels w a b ×ˢ S.distanceExpansionLabels w a b] (0, 0)]
        (fun ξ ↦ ‖ξ‖ ^ 2) := by
  let P := secondJetPolynomial (D.position w) S.level
    (fderiv ℝ D.potential (D.position w)) N.hessian
  let Y : S.covector.ker → E × E := fun z ↦ (N.position z, N.velocity z)
  let z₀ := Y 0
  let L := S.distanceExpansionLabels w a b
  obtain ⟨X, A, hX0, hX, hY, hdata⟩ := S.exists_state_germ_normalPotentialFamily D hF
    (S.labels_subset hw) hQ N
  obtain ⟨hC3, hstationary⟩ := N.phase_action_data_of_calibratedTube hF hcomplete hu T
  have hC2 : ContDiffAt ℝ 2 (F.phaseLengthAction D.initialChart N.flow P a b) (z₀, z₀) :=
    (hC3.of_le (by norm_num)).comp (z₀, z₀) (contDiffAt_const.prodMk contDiffAt_id)
  have hPG0 : (fun z ↦ P (D.position (w + z)) - D.potential (D.position (w + z)))
      =o[𝓝 (0 : S.covector.ker)] fun z ↦ ‖z‖ ^ 2 := by
    have hh := quadratic_remainder_comp_isLittleO hPG.neg_left
      ((differentiableAt_const w).add differentiableAt_id)
      (show w + (0 : S.covector.ker) = w from add_zero _)
    simpa only [Pi.neg_apply, neg_sub, sub_zero, Pi.add_apply, id_eq, P] using! hh
  have hPGX : (fun z ↦ P (X z).1 - D.potential (X z).1)
      =o[𝓝 (0 : S.covector.ker)] fun z ↦ ‖z‖ ^ 2 := by
    apply hPG0.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hdata] with z hz
    rw [hz.2.1]
  have hXdata : ∀ᶠ z in 𝓝[L] (0 : S.covector.ker),
      (F.chartLength D.initialChart (X z) : ℝ) = 1 ∧
      u (N.flow (X z) a) = D.potential (X z).1 + a ∧
      u (N.flow (X z) b) = D.potential (X z).1 + b := by
    filter_upwards [hdata.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzL
    have hzL' : w + z ∈ S.labels ∧ a ∈ S.calibrationTimes (w + z) ∧
        b ∈ S.calibrationTimes (w + z) := hzL
    refine ⟨hz.2.2.2 hzL'.1, ?_, ?_⟩
    · rw [hz.2.2.1, hz.2.1, D.level_eq _ (S.labels_subset hzL'.1)]
      exact hzL'.2.1
    · rw [hz.2.2.1, hz.2.1, D.level_eq _ (S.labels_subset hzL'.1)]
      exact hzL'.2.2
  have hYdata : ∀ᶠ z in 𝓝[L] (0 : S.covector.ker),
      (F.chartLength D.initialChart (Y z) : ℝ) = 1 ∧ P (Y z).1 = P z₀.1 := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (N.open_labels.mem_nhds N.anchor_mem)]
      with z hz
    have hE : F.chartEnergy D.initialChart (Y z) = 1 / 2 := by
      have hi := N.flow_initial _ (N.initial_legal z hz)
      have hh := congrArg F.energy hi
      have he := N.energy_eq z hz 0
      rw [N.curve_eq] at he
      exact hh.symm.trans he
    refine ⟨?_, (N.level z hz).trans (N.level 0 N.anchor_mem).symm⟩
    rw [F.chartLength_eq_sqrt_energy, hE]
    norm_num
  have htransfer := F.original_deficit_sub_smooth_isLittleO_of_label_phaseAction
    D.initialChart N.flow P D.potential u a b 0
    (by simpa only [sub_zero] using hC2)
    (by simpa only [sub_zero, P, scalarSecondJetPolynomial] using! hstationary)
    hX.hasFDerivWithinAt hY.hasFDerivWithinAt hX0 rfl hPGX
    (by simpa only [sub_zero] using hXdata) (by simpa only [sub_zero] using hYdata)
  have htransfer' : (fun ξ : S.covector.ker × S.covector.ker ↦
      ((F.lengthEDist (S.curve (w + ξ.1) a) (S.curve (w + ξ.2) b)).toReal -
        u (S.curve (w + ξ.2) b) + u (S.curve (w + ξ.1) a)) -
      ((F.lengthEDist (N.curve ξ.1 a) (N.curve ξ.2 b)).toReal - (b - a)))
      =o[𝓝[L ×ˢ L] (0, 0)] fun ξ ↦ ‖ξ‖ ^ 2 := by
    apply htransfer.congr' ?_ Filter.EventuallyEq.rfl
    have hd : ∀ᶠ ξ : S.covector.ker × S.covector.ker in 𝓝[L ×ˢ L] (0, 0),
        N.flow (X ξ.1) = S.curve (w + ξ.1) ∧ N.flow (X ξ.2) = S.curve (w + ξ.2) := by
      rw [nhdsWithin_prod_eq]
      apply (Filter.Eventually.prod_mk (hdata.filter_mono nhdsWithin_le_nhds)
        (hdata.filter_mono nhdsWithin_le_nhds)).mono
      intro ξ hξ
      exact ⟨hξ.1.2.2.1, hξ.2.2.2.1⟩
    filter_upwards [hd] with ξ hξ
    simp only [sub_zero, hξ.1, hξ.2, N.curve_eq]
  have hmodel := (T.distance_sub_intrinsicLengthQuadratic_isLittleO hF hcomplete hu
    (N.complete 0 N.anchor_mem) bW).mono
      (show 𝓝[L ×ˢ L] ((0 : S.covector.ker), 0) ≤ 𝓝 (0 : S.covector.ker × S.covector.ker)
        from nhdsWithin_le_nhds)
  have hcoefficient (ξ : S.covector.ker × S.covector.ker) :
      F.intrinsicLengthQuadratic bW N.curve 0 a b ξ =
        F.intrinsicLengthQuadratic bW S.curve w a b ξ := by
    simp only [ContinuousFinslerNorm.intrinsicLengthQuadratic, hH]
  apply (htransfer'.add hmodel).congr_left
  intro ξ
  rw [hcoefficient]
  ring


/-- The original Finsler seed has its actual intrinsic-compliance distance expansion
at almost every original label and every strictly ordered pair of active times.
All normal families, tube geometry, state jets and stationary actions are produced
from the retained original seed and the original Finsler assumptions. -/
theorem ae_distance_deficit_intrinsic_quadratic
    (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instActualSeedExpansionLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure]
    (bW : Basis ι ℝ S.covector.ker) :
    ∀ᵐ w ∂m.restrict S.labels, ∀ a b : ℝ, a < b →
      a ∈ interior (S.calibrationTimes w) → b ∈ interior (S.calibrationTimes w) →
      (fun ξ : S.covector.ker × S.covector.ker ↦
        ((F.lengthEDist (S.curve (w + ξ.1) a) (S.curve (w + ξ.2) b)).toReal -
          u (S.curve (w + ξ.2) b) + u (S.curve (w + ξ.1) a)) -
          F.intrinsicLengthQuadratic bW S.curve w a b ξ)
        =o[𝓝[S.distanceExpansionLabels w a b ×ˢ S.distanceExpansionLabels w a b] (0, 0)]
          (fun ξ ↦ ‖ξ‖ ^ 2) := by
  let D := S.c11Data
  filter_upwards [S.ae_exists_normalPotentialFamily D hF hcomplete m bW,
    S.ae_initial_phase_regular_energy D hF m,
    S.ae_exists_comparison_active_jacobian D hF hcomplete hu m] with w hnormal hregular hpositive
  obtain ⟨hw, N, hcurve, hjet, hPG, hH⟩ := hnormal
  obtain ⟨_, _, _, _, hQ, _⟩ := hregular
  obtain ⟨_, _, _, _, _, hpos⟩ := hpositive
  intro a b hab ha hb
  obtain ⟨T⟩ := S.nonempty_calibratedTube_normalPotentialFamily D hF hcomplete hu hw
    N hcurve hjet hpos hab ha hb
  exact S.distance_deficit_intrinsic_quadratic_of_normalPotentialFamily D hF hcomplete hu
    bW hw hQ N hPG hH T

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
