import OTSelector.Probability.CavitySemidiscreteCoupling

/-!
# Every semidiscrete coupling has an allocation representation

Disintegrating an arbitrary coupling over its actual source marginal gives its finite
conditional label masses. These form a feasible allocation and preserve every integrable
paired cost. No optimizer selection or uniqueness hypothesis enters the construction.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Marginal integrability controls every full source-label coupling. -/
theorem integrable_of_isSemidiscreteCoupling
    (μ : Measure S) (p : Fin (m + 1) → ℝ) (γ : Measure (S × Fin (m + 1)))
    (hγ : Vlasov.IsCoupling γ μ (semidiscreteLabelMeasure p))
    (c : S → Fin (m + 1) → ℝ) (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) :
    Integrable (Function.uncurry c) γ := by
  have hd : Integrable (fun s ↦ ∑ j, ‖c s j‖) μ :=
    integrable_finsetSum _ (fun j _ ↦ (hc j).norm)
  have hpres : MeasurePreserving Prod.fst γ μ := ⟨measurable_fst, hγ.1⟩
  apply (hpres.integrable_comp_of_integrable hd).mono' hcm.aestronglyMeasurable
  exact Eventually.of_forall fun z ↦
    Finset.single_le_sum (fun j _ ↦ norm_nonneg (c z.1 j)) (Finset.mem_univ z.2)

/-- Every coupling, including every member of its optimal face, has feasible finite conditional
label masses which preserve all measurable source-integrable paired objectives. -/
theorem exists_semidiscreteAllocation_of_isCoupling
    (μ : Measure S) [IsProbabilityMeasure μ]
    (p : Fin (m + 1) → ℝ) (hp : ∀ j, 0 ≤ p j)
    (γ : Measure (S × Fin (m + 1)))
    (hγ : Vlasov.IsCoupling γ μ (semidiscreteLabelMeasure p)) :
    ∃ a : S → Fin (m + 1) → ℝ, IsSemidiscreteAllocation μ p a ∧
      ∀ c : S → Fin (m + 1) → ℝ, Measurable (Function.uncurry c) →
        (∀ j, Integrable (fun s ↦ c s j) μ) →
        (∫ z, c z.1 z.2 ∂γ) = semidiscreteAllocationCost μ c a := by
  have hγprob : IsProbabilityMeasure γ := by
    constructor
    have hu := congrArg (fun M : Measure S ↦ M univ) hγ.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
      measure_univ] using hu
  let κ := condDistrib (Prod.snd : S × Fin (m + 1) → Fin (m + 1)) Prod.fst γ
  have hdis : μ ⊗ₘ κ = γ := by
    have h := compProd_map_condDistrib (X := Prod.fst)
      (Y := (Prod.snd : S × Fin (m + 1) → Fin (m + 1))) (μ := γ)
      (mβ := ‹MeasurableSpace S›)
      measurable_snd.aemeasurable
    rw [hγ.1] at h
    change μ ⊗ₘ κ = γ.map id at h
    simpa only [Measure.map_id] using h
  let a : S → Fin (m + 1) → ℝ := fun s j ↦ (κ s {j}).toReal
  have ham (j : Fin (m + 1)) : Measurable (fun s ↦ a s j) :=
    (Kernel.measurable_coe κ (measurableSet_singleton j)).ennreal_toReal
  have han (s : S) (j : Fin (m + 1)) : 0 ≤ a s j := ENNReal.toReal_nonneg
  have hab (s : S) (j : Fin (m + 1)) : a s j ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one : κ s {j} ≤ 1))
  have hai (j : Fin (m + 1)) : Integrable (fun s ↦ a s j) μ :=
    (integrable_const (1 : ℝ)).mono' (ham j).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (han s j)] using hab s j)
  have has (s : S) : ∑ j, a s j = 1 := by
    change ∑ j, (κ s {j}).toReal = 1
    rw [← ENNReal.toReal_sum (fun j _ ↦ measure_ne_top (κ s) {j}), sum_measure_singleton]
    simp
  have hap (j : Fin (m + 1)) : ∫ s, a s j ∂μ = p j := by
    apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun s ↦ han s j)) (hp j)).mp
    rw [ofReal_integral_eq_lintegral_ofReal (hai j)
      (Eventually.of_forall fun s ↦ han s j)]
    simp only [a, ENNReal.ofReal_toReal (measure_ne_top (κ _) _)]
    calc
      (∫⁻ s, κ s {j} ∂μ) = γ.map Prod.snd {j} := by
        rw [← hdis, Measure.map_apply measurable_snd (measurableSet_singleton j),
          Measure.compProd_apply (measurable_snd (measurableSet_singleton j))]
        rfl
      _ = ENNReal.ofReal (p j) := by rw [hγ.2, semidiscreteLabelMeasure_singleton]
  refine ⟨a, ⟨hai, Eventually.of_forall han, Eventually.of_forall has, hap⟩, ?_⟩
  intro c hcm hc
  have hci := integrable_of_isSemidiscreteCoupling μ p γ hγ c hcm hc
  rw [← hdis] at hci ⊢
  change (∫ z, Function.uncurry c z ∂μ ⊗ₘ κ) = _
  rw [Measure.integral_compProd hci]
  unfold semidiscreteAllocationCost
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  simpa only [a, smul_eq_mul, measureReal_def, Function.uncurry] using
    (integral_fintype (μ := κ s) (f := fun j ↦ c s j) Integrable.of_finite)

end OTSelector.Probability
