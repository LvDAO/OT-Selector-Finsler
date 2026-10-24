import OTSelector.Probability.CavitySemidiscretePressureValue
import OTSelector.Probability.CavitySemidiscreteJointOptima

/-!
# Integrable joint cost readouts of actual semidiscrete plans

Jointly measurable allocation coefficients give measurable objective readouts.
Original joint cost integrability bounds every feasible plan, so random Dirichlet
optima and their common-environment comparisons can be integrated without any
additional measurability or expected-pressure assumption.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V E : Type*} [MeasurableSpace S] [MeasurableSpace V]
  [MeasurableSpace E]

/-- A complete jointly measurable allocation has a measurable actual cost readout. -/
theorem measurable_parameterized_semidiscreteAllocationCost
    (μ : Measure S) [SFinite μ]
    (c : E → Fin (m + 1) → S → ℝ)
    (A : E × S → Fin (m + 1) → ℝ)
    (hc : ∀ j, Measurable (fun z : E × S ↦ c z.1 j z.2))
    (hA : ∀ j, Measurable (fun z ↦ A z j)) :
    Measurable (fun z ↦ semidiscreteAllocationCost μ (fun s j ↦ c z j s)
      (fun s ↦ A (z, s))) := by
  have h := (Finset.measurable_sum Finset.univ (fun j _ ↦ (hA j).mul (hc j)))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- Jointly integrable original costs bound the readout of every almost surely feasible
allocation on the parameter-times-Dirichlet space. -/
theorem integrable_parameterized_dirichlet_allocationCost
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hci : ∀ j, Integrable (fun z : V × S ↦ c z.1 j z.2) (ρ.prod μ))
    (A : ((V × (Fin (m + 1) → ℝ)) × S) → Fin (m + 1) → ℝ)
    (hA : ∀ j, Measurable (fun z ↦ A z j))
    (ha : ∀ᵐ z ∂ρ.prod (dirichletOne m),
      IsSemidiscreteAllocation μ z.2 (fun s ↦ A (z, s))) :
    Integrable (fun z ↦ semidiscreteAllocationCost μ (fun s j ↦ c z.1 j s)
      (fun s ↦ A (z, s))) (ρ.prod (dirichletOne m)) := by
  have hic : ∀ᵐ z ∂ρ.prod (dirichletOne m), ∀ j, Integrable (c z.1 j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j ↦ (hci j).prod_right_ae))
  have hb : Integrable (fun v ↦ ∑ j, ∫ s, ‖c v j s‖ ∂μ) ρ :=
    integrable_finsetSum _ (fun j _ ↦ (hci j).integral_norm_prod_left)
  apply (hb.comp_fst (dirichletOne m)).mono'
    (measurable_parameterized_semidiscreteAllocationCost μ
      (fun z j s ↦ c z.1 j s) A
      (fun j ↦ (hc j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      hA).aestronglyMeasurable
  filter_upwards [ha, hic] with z hz hcz
  exact hz.norm_cost_le _ hcz

/-- The actual primal value is jointly integrable in the original parameter and masses;
its measurable version is supplied by the actual cavity optimizer. -/
theorem integrable_parameterized_dirichlet_semidiscreteValue
    [StandardBorelSpace S] [StandardBorelSpace V]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c : V → Fin (m + 1) → S → ℝ)
    (hc : ∀ j, Measurable (fun z : V × S ↦ c z.1 j z.2))
    (hci : ∀ j, Integrable (fun z : V × S ↦ c z.1 j z.2) (ρ.prod μ))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c v j s - c v l s))) :
    Integrable (fun z : V × (Fin (m + 1) → ℝ) ↦
      semidiscreteValue μ (fun s j ↦ c z.1 j s) z.2) (ρ.prod (dirichletOne m)) := by
  have hi : ∀ᵐ v ∂ρ, ∀ j, Integrable (c v j) μ :=
    ae_all_iff.mpr (fun j ↦ (hci j).prod_right_ae)
  obtain ⟨A, hA, hopt⟩ :=
    exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation μ ρ c hc hi hatom
  have ha := hopt.mono fun _ h ↦ h.1.1
  apply (integrable_parameterized_dirichlet_allocationCost μ ρ c hc hci A hA ha).congr
  have hic : ∀ᵐ z ∂ρ.prod (dirichletOne m), ∀ j, Integrable (c z.1 j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae hi
  filter_upwards [hopt, hic] with z hz hcz
  exact (semidiscreteValue_eq_cost_of_optimal μ _ hcz z.2
    (fun s ↦ A (z, s)) hz.1.1 hz.1.2).symm

end OTSelector.Probability
