import OTSelector.Probability.PoissonRestriction
import OTSelector.Probability.PoissonExponentialMoment

/-! Exact Poisson counts on fixed original measurable point restrictions. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {X : Type*} [MeasurableSpace X]

/-- Literal original prefix count of observations in a fixed measurable point set. -/
def blockSetCount (S : Set X) (b : BlockData X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin b.1 ↦ b.2 i ∈ S)).card

private theorem measurable_blockCount : Measurable (fun b : BlockData X ↦ b.1) := by
  intro U hU
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((fun _ : Fin n → X ↦ n) ⁻¹' U)
  exact measurable_const hU

/-- The original fixed-set count is measurable in the actual finite array. -/
theorem measurable_blockSetCount {S : Set X} (hS : MeasurableSet S) :
    Measurable (blockSetCount S) := by
  classical
  intro U hU
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  apply (show Measurable (fun y : Fin n → X ↦
    (Finset.univ.filter (fun i : Fin n ↦ y i ∈ S)).card) from ?_) hU
  simp only [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hS.preimage (measurable_pi_apply i)) measurable_const measurable_const

private theorem map_blockDataLaw_count (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Measure ℕ) :
    (blockDataLaw ν (fun n ↦ κ {n})).map (fun b ↦ b.1) = κ := by
  rw [blockDataLaw, Measure.map_sum measurable_blockCount.aemeasurable]
  simp_rw [Measure.map_smul]
  have hterm (n : ℕ) : ((Measure.pi (fun _ : Fin n ↦ ν)).map
      (fun y ↦ (⟨n, y⟩ : BlockData X))).map (fun b ↦ b.1) = Measure.dirac n := by
    rw [Measure.map_map measurable_blockCount (measurable_sigma_mk n)]
    change (Measure.pi (fun _ : Fin n ↦ ν)).map (fun _ ↦ n) = _
    simp
  simp_rw [hterm]
  exact Measure.sum_smul_dirac κ

/-- Any fixed original measurable restriction has its exact thinned Poisson
count law. No independent law is attributed to an adaptive selected cloud. -/
theorem hasLaw_blockSetCount_poisson
    (ν : Measure X) [IsProbabilityMeasure ν] (rate : ℝ≥0)
    {S : Set X} (hS : MeasurableSet S) :
    HasLaw (blockSetCount S) (poissonMeasure (rate * restrictionWeight ν S))
      (blockDataLaw ν (fun n ↦ poissonMeasure rate {n})) := by
  classical
  refine ⟨(measurable_blockSetCount hS).aemeasurable, ?_⟩
  let encode : ℕ × (ℕ → X) → BlockData X := fun z ↦ ⟨z.1, fun i ↦ z.2 i⟩
  have hencode : Measurable encode := by
    apply measurable_from_prod_countable_right
    intro n
    exact (measurable_sigma_mk n).comp
      (measurable_pi_lambda _ (fun i : Fin n ↦ measurable_pi_apply (i : ℕ)))
  have h := congrArg (fun R : Measure (BlockData X) ↦ R.map (fun b ↦ b.1))
    (map_restrictedPrefix ν rate hS)
  rw [Measure.map_map measurable_blockCount (measurable_restrictedPrefix hS),
    map_blockDataLaw_count] at h
  rw [blockDataLaw_eq_map_cloud, Measure.map_map (measurable_blockSetCount hS) hencode]
  convert h using 1
  congr 1
  funext z
  simp only [blockSetCount, restrictedPrefix, prefixBlockDataGen, Function.comp_def, encode]
  congr 1
  ext i
  simp [restrictionLabel]

end OTSelector.Probability
