import OTSelector.Probability.CavitySemidiscreteEscapeMass

/-!
# Original source marginal under spatial rooting

The exact allocation marginal survives scaling and rooting. Haar averaging
controls source-window mass without using a target restriction.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S X Y : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]

/-- Every observed allocation retains the exact observed source marginal. -/
theorem IsSemidiscreteAllocation.fst_scaled_observed_plan
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (f : S → X) (hf : Measurable f)
    (y : Fin (m + 1) → Y) (N : ℝ) :
    (ENNReal.ofReal N • (semidiscreteAllocationMeasure μ a).map (Prod.map f y)).fst =
      ENNReal.ofReal N • μ.map f := by
  unfold Measure.fst
  rw [Measure.map_smul, Measure.map_map measurable_fst (hf.prodMap (measurable_of_finite y))]
  congr 1
  change (semidiscreteAllocationMeasure μ a).map (f ∘ Prod.fst) = _
  rw [← Measure.map_map hf measurable_fst, ha.isCoupling.1]

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

omit [Fintype ι] in
/-- The two opposite optimizers have the same original rooted source measure. -/
theorem IsSemidiscreteAllocation.fst_cavitySpatialRootedPlan
    {μ : Measure ((ι → ℝ) × A)} {p : Fin (m + 1) → ℝ}
    {a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ) :
    (cavitySpatialRootedPlan μ a Y N z).fst =
      ENNReal.ofReal N • μ.map (cavitySpatialTranslate z) :=
  ha.fst_scaled_observed_plan (cavitySpatialTranslate z)
    (measurable_cavitySpatialTranslate.comp (measurable_const.prodMk measurable_id)) _ _

omit [Fintype ι] in
/-- A source-window mass is exactly the translated original source readout. -/
theorem cavitySpatialRootedPlan_sourceWindow
    (μ : Measure ((ι → ℝ) × A)) (p : Fin (m + 1) → ℝ)
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    cavitySpatialRootedPlan μ a Y N z {e | e.1.1 ∈ U} =
      ENNReal.ofReal N * cavityRootWindowReadout μ Prod.fst (fun _ ↦ 1) U z := by
  have ht : Measurable (cavitySpatialTranslate z : ((ι → ℝ) × A) → ((ι → ℝ) × A)) :=
    measurable_cavitySpatialTranslate.comp (measurable_const.prodMk measurable_id)
  have hf := ha.fst_cavitySpatialRootedPlan Y N z
  have he := congrArg (fun ν : Measure ((ι → ℝ) × A) ↦ ν (Prod.fst ⁻¹' U)) hf
  rw [Measure.fst, Measure.map_apply measurable_fst (hU.preimage measurable_fst),
    Measure.smul_apply, smul_eq_mul,
    Measure.map_apply ht (hU.preimage measurable_fst)] at he
  change cavitySpatialRootedPlan μ a Y N z (Prod.fst ⁻¹' (Prod.fst ⁻¹' U)) = _
  rw [he]
  congr 1
  rw [← lintegral_indicator_one ((hU.preimage measurable_fst).preimage ht)]
  apply lintegral_congr
  rintro ⟨x, s⟩
  by_cases hx : x - z ∈ U
  · rw [indicator_of_mem (show (x, s) ∈ cavitySpatialTranslate z ⁻¹' Prod.fst ⁻¹' U from hx),
      indicator_of_mem hx]
    rfl
  · rw [indicator_of_notMem (show (x, s) ∉ cavitySpatialTranslate z ⁻¹' Prod.fst ⁻¹' U from hx),
      indicator_of_notMem hx]

/-- Haar root averaging bounds the original source-window mass independently of
sample size or plan choice. For a probability source the bound is just `volume U`. -/
theorem lintegral_cavitySpatialRootedPlan_sourceWindow_le
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ] (p : Fin (m + 1) → ℝ)
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, cavitySpatialRootedPlan μ a Y N z {e | e.1.1 ∈ U}
      ∂cavityRootMeasure volume D N) ≤ volume U := by
  simp_rw [cavitySpatialRootedPlan_sourceWindow μ p a ha Y N _ U hU]
  simpa using lintegral_cavityRoot_scaled_window_le volume μ Prod.fst measurable_fst
    (fun _ ↦ 1) measurable_const U hU D N hN

end OTSelector.Probability
