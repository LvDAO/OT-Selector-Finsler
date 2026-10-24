import OTSelector.Reconstruction.OriginalIIDOptimalMeanPlan
import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalMarginalMeans

/-! Integrating only the auxiliary iid target cloud gives an actual coupling
from the unchanged finite source observations to the full population law. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}

/-- The true counted transport plan obtained by integrating out an independent
target cloud. Original source observations and the fixed exact tie rule remain. -/
def originalIIDPopulationCoupling (μ : Measure Y) (cost : X → Y → ℝ)
    (x : Fin n → X) : Measure (X × Y) :=
  (n : ℝ≥0∞) • (Measure.pi (fun _ : Fin n ↦ μ)).bind
    (fun y ↦ originalIIDOptimalPhysicalPlan cost 1 (x, y))

/-- The actual population plan is zero for an empty source array. -/
theorem originalIIDPopulationCoupling_zero (μ : Measure Y) (cost : X → Y → ℝ)
    (x : Fin 0 → X) : originalIIDPopulationCoupling μ cost x = 0 := by
  simp [originalIIDPopulationCoupling]

private theorem measurable_fixedSourcePlan (cost : X → Y → ℝ)
    (hcost : Measurable (Function.uncurry cost)) (x : Fin n → X) :
    Measurable (fun y : Fin n → Y ↦ originalIIDOptimalPhysicalPlan cost 1 (x, y)) :=
  (measurable_originalIIDOptimalPhysicalPlan cost hcost 1).comp
    (measurable_const.prodMk measurable_id)

/-- The integrated target cloud preserves the exact empirical source marginal. -/
theorem originalIIDPopulationCoupling_source (μ : Measure Y) [IsProbabilityMeasure μ]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (x : Fin n → X) :
    (originalIIDPopulationCoupling μ cost x).map Prod.fst =
      (n : ℝ≥0∞) • empiricalMeasure x := by
  rw [originalIIDPopulationCoupling, Measure.map_smul]
  congr 1
  apply Measure.ext
  intro H hH
  rw [Measure.map_apply measurable_fst hH,
    Measure.bind_apply (hH.preimage measurable_fst)
      (measurable_fixedSourcePlan cost hcost x).aemeasurable]
  have hread (y : Fin n → Y) : originalIIDOptimalPhysicalPlan cost 1 (x, y)
      (Prod.fst ⁻¹' H) = empiricalMeasure x H := by
    have h := congrArg (fun σ : Measure X ↦ σ H)
      (originalIIDOptimalPhysicalPlan_source cost 1 (x, y))
    simpa only [Measure.map_apply measurable_fst hH] using h
  simp_rw [hread]
  simp

/-- Averaging the full matched target empirical measure yields exactly n times
the population, even though each chosen target depends on the entire cloud. -/
theorem originalIIDPopulationCoupling_target (μ : Measure Y) [IsProbabilityMeasure μ]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (x : Fin n → X) :
    (originalIIDPopulationCoupling μ cost x).map Prod.snd = (n : ℝ≥0∞) • μ := by
  by_cases hn : n = 0
  · subst n
    simp [originalIIDPopulationCoupling]
  have : NeZero n := ⟨hn⟩
  rw [originalIIDPopulationCoupling, Measure.map_smul]
  congr 1
  apply Measure.ext
  intro H hH
  rw [Measure.map_apply measurable_snd hH,
    Measure.bind_apply (hH.preimage measurable_snd)
      (measurable_fixedSourcePlan cost hcost x).aemeasurable]
  have hread (y : Fin n → Y) : originalIIDOptimalPhysicalPlan cost 1 (x, y)
      (Prod.snd ⁻¹' H) = ∫⁻ z, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) z
        ∂empiricalMeasure y := by
    have h := congrArg (fun σ : Measure Y ↦ σ H)
      (originalIIDOptimalPhysicalPlan_target cost 1 (x, y))
    rw [Measure.map_apply measurable_snd hH] at h
    exact h.trans (lintegral_indicator_one hH).symm
  simp_rw [hread]
  exact (lintegral_originalEmpiricalMeasure_mean (Measure.pi (fun _ : Fin n ↦ μ)) μ
    id (fun i ↦ measurePreserving_eval (fun _ : Fin n ↦ μ) i)
    (H.indicator (fun _ ↦ 1)) (measurable_const.indicator hH)).trans
      (lintegral_indicator_one hH)

/-- Count normalization removes the empirical denominator, including n=0. -/
theorem originalIIDPopulationCoupling_counted_source
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (x : Fin n → X) :
    (originalIIDPopulationCoupling μ cost x).map Prod.fst = ∑ i, Measure.dirac (x i) := by
  rw [originalIIDPopulationCoupling_source μ cost hcost x]
  by_cases hn : n = 0
  · subst n
    simp [empiricalMeasure]
  rw [empiricalMeasure, smul_smul, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n), one_smul]

/-- Every nonnegative physical readout retains its exact one-cloud expectation. -/
theorem lintegral_originalIIDPopulationCoupling (μ : Measure Y) (cost : X → Y → ℝ)
    (hcost : Measurable (Function.uncurry cost)) (x : Fin n → X)
    (f : X × Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂originalIIDPopulationCoupling μ cost x) =
      (n : ℝ≥0∞) * ∫⁻ y, ∫⁻ p, f p ∂originalIIDOptimalPhysicalPlan cost 1 (x, y)
        ∂Measure.pi (fun _ : Fin n ↦ μ) := by
  rw [originalIIDPopulationCoupling, lintegral_smul_measure,
    Measure.lintegral_bind (measurable_fixedSourcePlan cost hcost x).aemeasurable
      hf.aemeasurable, smul_eq_mul]

/-- The genuine population plan depends measurably on every original sample. -/
theorem measurable_originalIIDPopulationCoupling (μ : Measure Y) [IsProbabilityMeasure μ]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost)) :
    Measurable (originalIIDPopulationCoupling (n := n) μ cost) := by
  apply Measure.measurable_of_measurable_coe
  intro H hH
  simp_rw [originalIIDPopulationCoupling, Measure.smul_apply, smul_eq_mul,
    Measure.bind_apply hH (measurable_fixedSourcePlan cost hcost _).aemeasurable]
  exact (((Measure.measurable_coe hH).comp
    (measurable_originalIIDOptimalPhysicalPlan cost hcost 1)).lintegral_prod_right').const_mul _

/-- Every actual counted population plan is finite, also for an empty array. -/
theorem originalIIDPopulationCoupling_isFiniteMeasure
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (x : Fin n → X) : IsFiniteMeasure (originalIIDPopulationCoupling μ cost x) := by
  by_cases hn : n = 0
  · subst n
    rw [originalIIDPopulationCoupling_zero]
    infer_instance
  have : NeZero n := ⟨hn⟩
  have : IsProbabilityMeasure ((Measure.pi (fun _ : Fin n ↦ μ)).bind
      (fun y ↦ originalIIDOptimalPhysicalPlan cost 1 (x, y))) :=
    isProbabilityMeasure_bind (measurable_fixedSourcePlan cost hcost x).aemeasurable
      (Filter.Eventually.of_forall fun _ ↦ inferInstance)
  unfold originalIIDPopulationCoupling
  exact Measure.smul_finite _ (ENNReal.natCast_ne_top n)

end OTSelector.Reconstruction
