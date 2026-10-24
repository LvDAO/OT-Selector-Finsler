import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeedDistance
import OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalUniformAction

/-!
# Uniform actual distance expansions over compact time pairs

The actual original state germ and one retained normal family give a common radius
for every time pair in a compact calibrated region. The original endpoints,
potential clocks, label coordinates and intrinsic compliance coefficient are retained.
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

omit [BorelSpace E] in
/-- The original state germ gives one intrinsic distance remainder radius for
compactly many calibrated time pairs, uniformly on the original allowed labels. -/
theorem uniform_distance_deficit_of_normalPotentialFamily
    (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instUniformSeedDistanceLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
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
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hTube : ∀ t ∈ T, Nonempty (F.CalibratedTube N.curve t.1 t.2 u)) :
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ t ∈ T,
      ∀ ξ : S.covector.ker × S.covector.ker, ‖ξ‖ < r →
        ξ ∈ S.distanceExpansionLabels w t.1 t.2 ×ˢ S.distanceExpansionLabels w t.1 t.2 →
        ‖(F.lengthEDist (S.curve (w + ξ.1) t.1) (S.curve (w + ξ.2) t.2)).toReal -
          u (S.curve (w + ξ.2) t.2) + u (S.curve (w + ξ.1) t.1) -
          F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 ξ‖ ≤ ε * ‖ξ‖ ^ 2 := by
  let P := secondJetPolynomial (D.position w) S.level
    (fderiv ℝ D.potential (D.position w)) N.hessian
  obtain ⟨X, A, hX0, hX, hY, hdata⟩ := S.exists_state_germ_normalPotentialFamily D hF
    (S.labels_subset hw) hQ N
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
  intro ε hε
  obtain ⟨rA, hrA, hA⟩ := N.uniform_phaseAction_intrinsic_quadratic hF hcomplete hu
    bW hT hTube hX hX0 hY (ε / 2) (half_pos hε)
  obtain ⟨rP, hrP, hP⟩ := Metric.mem_nhds_iff.mp (hPGX.def (show 0 < ε / 4 by positivity))
  obtain ⟨rD, hrD, hD⟩ := Metric.mem_nhds_iff.mp hdata
  refine ⟨min rA (min rP rD), lt_min hrA (lt_min hrP hrD), ?_⟩
  intro t ht ξ hξ hallowed
  have hξA := hξ.trans_le (min_le_left _ _)
  have hξP := (hξ.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hξD := (hξ.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hd₁ := hD (show ξ.1 ∈ Metric.ball 0 rD by
    simpa only [Metric.mem_ball, dist_zero_right] using (norm_fst_le ξ).trans_lt hξD)
  have hd₂ := hD (show ξ.2 ∈ Metric.ball 0 rD by
    simpa only [Metric.mem_ball, dist_zero_right] using (norm_snd_le ξ).trans_lt hξD)
  have hp₁ : ‖P (X ξ.1).1 - D.potential (X ξ.1).1‖ ≤ (ε / 4) * ‖ξ‖ ^ 2 := by
    have hh := hP (show ξ.1 ∈ Metric.ball 0 rP by
      simpa only [Metric.mem_ball, dist_zero_right] using (norm_fst_le ξ).trans_lt hξP)
    have hh' : ‖P (X ξ.1).1 - D.potential (X ξ.1).1‖ ≤ (ε / 4) * ‖ξ.1‖ ^ 2 := by
      simpa only [mem_ofPred_eq, Real.norm_of_nonneg (sq_nonneg _)] using! hh
    exact hh'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le ξ) 2) (by positivity))
  have hp₂ : ‖P (X ξ.2).1 - D.potential (X ξ.2).1‖ ≤ (ε / 4) * ‖ξ‖ ^ 2 := by
    have hh := hP (show ξ.2 ∈ Metric.ball 0 rP by
      simpa only [Metric.mem_ball, dist_zero_right] using (norm_snd_le ξ).trans_lt hξP)
    have hh' : ‖P (X ξ.2).1 - D.potential (X ξ.2).1‖ ≤ (ε / 4) * ‖ξ.2‖ ^ 2 := by
      simpa only [mem_ofPred_eq, Real.norm_of_nonneg (sq_nonneg _)] using! hh
    exact hh'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le ξ) 2) (by positivity))
  have hc₁ : u (S.curve (w + ξ.1) t.1) = D.potential (X ξ.1).1 + t.1 := by
    rw [hd₁.2.1, D.level_eq _ (S.labels_subset hallowed.1.1)]
    exact hallowed.1.2.1
  have hc₂ : u (S.curve (w + ξ.2) t.2) = D.potential (X ξ.2).1 + t.2 := by
    rw [hd₂.2.1, D.level_eq _ (S.labels_subset hallowed.2.1)]
    exact hallowed.2.2.2
  have hcoefficient : F.intrinsicLengthQuadratic bW N.curve 0 t.1 t.2 ξ =
      F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 ξ := by
    simp only [intrinsicLengthQuadratic, hH]
  have ha := hA t ht ξ hξA
  rw [hcoefficient] at ha
  have halgebra :
      (F.lengthEDist (S.curve (w + ξ.1) t.1) (S.curve (w + ξ.2) t.2)).toReal -
        u (S.curve (w + ξ.2) t.2) + u (S.curve (w + ξ.1) t.1) -
        F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 ξ =
      (F.phaseLengthAction D.initialChart N.flow P t.1 t.2 (X ξ.1, X ξ.2) -
        F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 ξ) +
        (P (X ξ.2).1 - D.potential (X ξ.2).1) -
        (P (X ξ.1).1 - D.potential (X ξ.1).1) := by
    dsimp only [phaseLengthAction]
    rw [hd₁.2.2.1, hd₂.2.2.1, hd₁.2.2.2 hallowed.1.1,
      hd₂.2.2.2 hallowed.2.1, hc₁, hc₂]
    ring
  rw [halgebra]
  let eA := F.phaseLengthAction D.initialChart N.flow P t.1 t.2 (X ξ.1, X ξ.2) -
    F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 ξ
  let e₁ := P (X ξ.1).1 - D.potential (X ξ.1).1
  let e₂ := P (X ξ.2).1 - D.potential (X ξ.2).1
  change ‖eA + e₂ - e₁‖ ≤ _
  calc
    ‖eA + e₂ - e₁‖ ≤ ‖eA + e₂‖ + ‖e₁‖ := norm_sub_le _ _
    _ ≤ (‖eA‖ + ‖e₂‖) + ‖e₁‖ := add_le_add (norm_add_le eA e₂) (le_refl _)
    _ ≤ ((ε / 2) * ‖ξ‖ ^ 2 + (ε / 4) * ‖ξ‖ ^ 2) + (ε / 4) * ‖ξ‖ ^ 2 :=
      add_le_add (add_le_add ha hp₂) hp₁
    _ = ε * ‖ξ‖ ^ 2 := by ring



/-- At almost every original label, all compact sets of strictly ordered active
pairs have a uniform actual distance expansion with the literal original kernel. -/
theorem ae_uniform_distance_deficit_intrinsic_quadratic
    (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instActualUniformLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure]
    (bW : Basis ι ℝ S.covector.ker) :
    ∀ᵐ w ∂m.restrict S.labels, w ∈ S.labels ∧
      ∀ T : Set (ℝ × ℝ), IsCompact T →
        (∀ t ∈ T, t.1 < t.2 ∧ t.1 ∈ interior (S.calibrationTimes w) ∧
          t.2 ∈ interior (S.calibrationTimes w)) →
        ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ t ∈ T,
          ∀ ξ : S.covector.ker × S.covector.ker, ‖ξ‖ < r →
            ξ ∈ S.distanceExpansionLabels w t.1 t.2 ×ˢ
              S.distanceExpansionLabels w t.1 t.2 →
            ‖(F.lengthEDist (S.curve (w + ξ.1) t.1) (S.curve (w + ξ.2) t.2)).toReal -
              u (S.curve (w + ξ.2) t.2) + u (S.curve (w + ξ.1) t.1) -
              F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 ξ‖ ≤ ε * ‖ξ‖ ^ 2 := by
  let D := S.c11Data
  filter_upwards [S.ae_exists_normalPotentialFamily D hF hcomplete m bW,
    S.ae_initial_phase_regular_energy D hF m,
    S.ae_exists_comparison_active_jacobian D hF hcomplete hu m] with w hnormal hregular hpositive
  obtain ⟨hw, N, hcurve, hjet, hPG, hH⟩ := hnormal
  obtain ⟨_, _, _, _, hQ, _⟩ := hregular
  obtain ⟨_, _, _, _, _, hpos⟩ := hpositive
  refine ⟨hw, ?_⟩
  intro T hT ht
  apply S.uniform_distance_deficit_of_normalPotentialFamily D hF hcomplete hu bW hw
    hQ N hPG hH hT
  intro t hmem
  exact S.nonempty_calibratedTube_normalPotentialFamily D hF hcomplete hu hw N
    hcurve hjet hpos (ht t hmem).1 (ht t hmem).2.1 (ht t hmem).2.2

/-- Fixing the actual source label gives precisely the displacement-squared
remainder required by the coercive pair coefficient in local pressure estimates. -/
theorem ae_uniform_source_distance_deficit_intrinsic_quadratic
    (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSourceUniformLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure]
    (bW : Basis ι ℝ S.covector.ker) :
    ∀ᵐ w ∂m.restrict S.labels, w ∈ S.labels ∧
      ∀ T : Set (ℝ × ℝ), IsCompact T →
        (∀ t ∈ T, t.1 < t.2 ∧ t.1 ∈ interior (S.calibrationTimes w) ∧
          t.2 ∈ interior (S.calibrationTimes w)) →
        ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ t ∈ T,
          ∀ v : S.covector.ker, ‖v‖ < r → v ∈ S.distanceExpansionLabels w t.1 t.2 →
            ‖(F.lengthEDist (S.curve w t.1) (S.curve (w + v) t.2)).toReal -
              u (S.curve (w + v) t.2) + u (S.curve w t.1) -
              F.intrinsicLengthQuadratic bW S.curve w t.1 t.2 (0, v)‖ ≤ ε * ‖v‖ ^ 2 := by
  filter_upwards [S.ae_uniform_distance_deficit_intrinsic_quadratic hF hcomplete hu m bW]
    with w hw
  refine ⟨hw.1, ?_⟩
  intro T hT ht ε hε
  obtain ⟨r, hr, hb⟩ := hw.2 T hT ht ε hε
  refine ⟨r, hr, ?_⟩
  intro t hmem v hv hallowed
  have hzero : (0 : S.covector.ker) ∈ S.distanceExpansionLabels w t.1 t.2 := by
    change w + 0 ∈ S.labels ∧ t.1 ∈ S.calibrationTimes (w + 0) ∧
      t.2 ∈ S.calibrationTimes (w + 0)
    simpa only [add_zero] using
      And.intro hw.1 ⟨interior_subset (ht t hmem).2.1, interior_subset (ht t hmem).2.2⟩
  have hh := hb t hmem (0, v) (by simpa using hv) ⟨hzero, hallowed⟩
  simpa only [add_zero, Prod.fst_zero, Prod.snd_zero, Prod.norm_def,
    norm_zero, max_eq_right (norm_nonneg v)] using hh

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
