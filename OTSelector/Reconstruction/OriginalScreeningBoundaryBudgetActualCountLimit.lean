import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCount

/-! Quadratically weighted actual full-scene count costs vanish in dimensions above four. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
variable {q : ℕ}

/-- The original sqrt-volume count discrepancy is negligible on the physical quadratic
scale in every dimension greater than four, in the same fixed physical orientation. -/
theorem tendsto_originalScreeningPhysicalCube_quadratic_sqrt_volume_zero
    (hq : 4 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    Tendsto (fun R : ℝ ↦ R^2 /
      Real.sqrt (volume.real (originalCenteredPhysicalCubeRegion b (2 * R)))) atTop (𝓝 0) := by
  have hmodel : Tendsto (fun R : ℝ ↦ 1 / Real.sqrt R) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  apply squeeze_zero' (Eventually.of_forall fun R ↦
    div_nonneg (sq_nonneg R) (Real.sqrt_nonneg _)) ?_ hmodel
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hV : volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) = (2 * R)^q := by
    calc
      _ = volume.real (haarRootCube (Fin q) R) := by
        simpa only [measureReal_def] using
          congrArg ENNReal.toReal (volume_originalOrientedTraffic_cube b R)
      _ = _ := by rw [volume_real_haarRootCube (Fin q) hRpos.le, Fintype.card_fin]
  have hVpos : 0 < volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
    rw [hV]
    positivity
  have hpow : R^5 ≤ (2 * R)^q :=
    (pow_le_pow_right₀ hR (show 5 ≤ q by omega)).trans
      (pow_le_pow_left₀ hRpos.le (show R ≤ 2 * R by linarith) q)
  have hroot : R^2 * Real.sqrt R ≤
      Real.sqrt (volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) := by
    apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hRpos.le, Real.sq_sqrt hVpos.le, hV]
    nlinarith [hpow]
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hVpos) (Real.sqrt_pos.mpr hRpos)).mpr
    (by simpa only [one_mul] using hroot)

/-- On the unchanged original matching law, any measurable bad-event family with
R²-probability tending to zero also has vanishing quadratically weighted actual full
two-color count cost per the same chosen physical cube volume. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalScreeningPhysicalCubeActualCount_bad_cost_zero
    {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (bad : ℝ → Set (LegalMarkedOptimalInputScene q)) (hbad : ∀ R, MeasurableSet (bad R))
    (hprob : Tendsto (fun R : ℝ ↦ R^2 *
      (Q.law : Measure (LegalMarkedOptimalInputScene q)).real (bad R)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦ R^2 *
      ((∫ scene, (bad R).indicator (originalScreeningPhysicalCubeActualCount b R) scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) /
        volume.real (originalCenteredPhysicalCubeRegion b (2 * R)))) atTop (𝓝 0) := by
  have hupper := (hprob.const_mul 2).add
    ((tendsto_originalScreeningPhysicalCube_quadratic_sqrt_volume_zero hq b).const_mul 2)
  simp only [mul_zero, zero_add] at hupper
  apply squeeze_zero' (Eventually.of_forall fun R ↦ mul_nonneg (sq_nonneg R)
    (div_nonneg (integral_nonneg fun scene ↦
      indicator_nonneg (fun scene _ ↦ originalScreeningActualCount_nonneg _ scene) _)
      measureReal_nonneg)) ?_ hupper
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  let V := volume.real (originalCenteredPhysicalCubeRegion b (2 * R))
  have hVpos : 0 < V := by
    dsimp [V]
    change 0 < (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toReal
    rw [volume_originalOrientedTraffic_cube]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le]
    positivity
  have hspos := Real.sqrt_pos.mpr hVpos
  have hs := Real.sq_sqrt hVpos.le
  have hcount := Q.integral_indicator_originalScreeningPhysicalCubeActualCount_le b R
    (bad R) (hbad R)
  calc
    _ ≤ R^2 * ((2 * V * (Q.law : Measure (LegalMarkedOptimalInputScene q)).real (bad R) +
        2 * Real.sqrt V) / V) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcount hVpos.le) (sq_nonneg R)
    _ = 2 * (R^2 * (Q.law : Measure (LegalMarkedOptimalInputScene q)).real (bad R)) +
        2 * (R^2 / Real.sqrt V) := by
      field_simp [hVpos.ne', hspos.ne']
      nlinarith [hs]

end OTSelector.Reconstruction
