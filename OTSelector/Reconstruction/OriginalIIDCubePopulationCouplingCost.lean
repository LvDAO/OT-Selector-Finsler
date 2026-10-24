import OTSelector.Reconstruction.OriginalIIDCubePopulationCoupling
import OTSelector.Reconstruction.IIDDyadicCubeMatching

/-! Literal cube square costs of the actual population coupling retain the
complete auxiliary-cloud matching expectation. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {q n : ℕ}

/-- The actual squared coordinate cost on the closed unit cube. -/
def originalCubePopulationSquareCost (p : DyadicUnitCube q × DyadicUnitCube q) : ℝ :=
  ‖dyadicCubePoint p.1 - dyadicCubePoint p.2‖ ^ 2

private theorem measurable_cubePoint : Measurable (dyadicCubePoint (q := q)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_subtype_coe.comp (measurable_pi_apply i)

/-- The literal squared coordinate cost is measurable. -/
theorem measurable_originalCubePopulationSquareCost :
    Measurable (originalCubePopulationSquareCost (q := q)) :=
  ((measurable_cubePoint.comp measurable_fst).sub
    (measurable_cubePoint.comp measurable_snd)).norm.pow_const 2

private theorem cubeSquareCost_nonneg (p : DyadicUnitCube q × DyadicUnitCube q) :
    0 ≤ originalCubePopulationSquareCost p := sq_nonneg _

private theorem cubeSquareCost_le_one (p : DyadicUnitCube q × DyadicUnitCube q) :
    originalCubePopulationSquareCost p ≤ 1 := by
  change ‖dyadicCubePoint p.1 - dyadicCubePoint p.2‖ ^ 2 ≤ 1
  simpa only [one_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (dyadicCube_dist_le_one p.1 p.2) 2

private def cubePopulationValue (x y : Fin n → DyadicUnitCube q) : ℝ :=
  perturbedAssignmentValue (fun i j ↦ originalCubePopulationSquareCost (x i, y j)) 0 0

private theorem measurable_cubePopulationValue :
    Measurable (fun p : (Fin n → DyadicUnitCube q) × (Fin n → DyadicUnitCube q) ↦
      cubePopulationValue p.1 p.2) := by
  apply OTSelector.Probability.measurable_assignmentValue
  intro i j
  exact measurable_originalCubePopulationSquareCost.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))

private theorem cubePopulationValue_nonneg (x y : Fin n → DyadicUnitCube q) :
    0 ≤ cubePopulationValue x y := by
  unfold cubePopulationValue perturbedAssignmentValue
  simp only [perturbedEdgeCost_zero, assignmentCost]
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- The population coupling has the exact auxiliary-cloud nonnegative energy,
without replacing the original source array or conditioning its observations. -/
theorem lintegral_originalIIDCubePopulationCoupling_squareCost
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (x : Fin n → DyadicUnitCube q) :
    (∫⁻ p, ENNReal.ofReal (originalCubePopulationSquareCost p)
      ∂originalIIDPopulationCoupling μ
        (fun u v ↦ originalCubePopulationSquareCost (u, v)) x) =
      ∫⁻ y, ENNReal.ofReal (perturbedAssignmentValue
        (fun i j ↦ originalCubePopulationSquareCost (x i, y j)) 0 0)
        ∂Measure.pi (fun _ : Fin n ↦ μ) := by
  by_cases hn : n = 0
  · subst n
    simp [originalIIDPopulationCoupling, perturbedAssignmentValue, assignmentCost]
  have : NeZero n := ⟨hn⟩
  let cost := fun u v : DyadicUnitCube q ↦ originalCubePopulationSquareCost (u, v)
  have hc : Measurable (Function.uncurry cost) := measurable_originalCubePopulationSquareCost
  rw [lintegral_originalIIDPopulationCoupling μ cost hc x _
    measurable_originalCubePopulationSquareCost.ennreal_ofReal]
  have hm : Measurable (fun y : Fin n → DyadicUnitCube q ↦
      ∫⁻ p, ENNReal.ofReal (originalCubePopulationSquareCost p)
        ∂originalIIDOptimalPhysicalPlan cost 1 (x, y)) :=
    (Measure.measurable_lintegral measurable_originalCubePopulationSquareCost.ennreal_ofReal).comp
      ((measurable_originalIIDOptimalPhysicalPlan cost hc 1).comp
        (measurable_const.prodMk measurable_id))
  rw [← lintegral_const_mul _ hm]
  apply lintegral_congr
  intro y
  have h := lintegral_originalIIDOptimalPhysicalPlan_cost cost hc
    (fun u v ↦ cubeSquareCost_nonneg (u, v)) (by norm_num : (0 : ℝ) ≤ 1) (x, y)
  simp only [one_mul] at h
  rw [h]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  congr 1
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn)

/-- The true real square cost equals the finite matching value integrated over
only the independent auxiliary target cloud. -/
theorem integral_originalIIDCubePopulationCoupling_squareCost
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (x : Fin n → DyadicUnitCube q) :
    (∫ p, originalCubePopulationSquareCost p
      ∂originalIIDPopulationCoupling μ
        (fun u v ↦ originalCubePopulationSquareCost (u, v)) x) =
      ∫ y, perturbedAssignmentValue
        (fun i j ↦ originalCubePopulationSquareCost (x i, y j)) 0 0
        ∂Measure.pi (fun _ : Fin n ↦ μ) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall cubeSquareCost_nonneg)
    measurable_originalCubePopulationSquareCost.aestronglyMeasurable,
    lintegral_originalIIDCubePopulationCoupling_squareCost]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (cubePopulationValue_nonneg x))
    (measurable_cubePopulationValue.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).symm

/-- The actual finite population coupling has integrable squared physical cost. -/
theorem integrable_originalIIDCubePopulationCoupling_squareCost
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (x : Fin n → DyadicUnitCube q) :
    Integrable originalCubePopulationSquareCost
      (originalIIDPopulationCoupling μ
        (fun u v ↦ originalCubePopulationSquareCost (u, v)) x) := by
  have := originalIIDPopulationCoupling_isFiniteMeasure μ
    (fun u v ↦ originalCubePopulationSquareCost (u, v)) measurable_originalCubePopulationSquareCost x
  apply (integrable_const (1 : ℝ)).mono' measurable_originalCubePopulationSquareCost.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (cubeSquareCost_nonneg p)]
    exact cubeSquareCost_le_one p)

/-- The constructed cube plan has both exact counted marginals and finite mass. -/
theorem originalIIDCubePopulationCoupling_marginals
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (x : Fin n → DyadicUnitCube q) :
    let Γ := originalIIDPopulationCoupling μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v)) x
    IsFiniteMeasure Γ ∧ Γ.map Prod.fst = ∑ i, Measure.dirac (x i) ∧
      Γ.map Prod.snd = (n : ℝ≥0∞) • μ :=
  ⟨originalIIDPopulationCoupling_isFiniteMeasure μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v))
      measurable_originalCubePopulationSquareCost x,
    originalIIDPopulationCoupling_counted_source μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v))
      measurable_originalCubePopulationSquareCost x,
    originalIIDPopulationCoupling_target μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v))
      measurable_originalCubePopulationSquareCost x⟩

/-- The actual cube coupling depends measurably on all original observations. -/
theorem measurable_originalIIDCubePopulationCoupling
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ] :
    Measurable (originalIIDPopulationCoupling (n := n) μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v))) :=
  measurable_originalIIDPopulationCoupling μ _ measurable_originalCubePopulationSquareCost

end OTSelector.Reconstruction
