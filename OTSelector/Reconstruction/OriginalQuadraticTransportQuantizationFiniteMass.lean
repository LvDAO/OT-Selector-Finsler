import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationFinitePlanIntegral
import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationCellLift
import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationError

/-! Quadratic lifting with arbitrary equal finite marginal mass, including zero mass. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The quadratic lifting error scales by the actual common finite mass.
Normalization is internal and the zero-mass case is handled explicitly. -/
theorem quadratic_coupling_lift_cost_bound_finite_mass
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ y ∂ν, y ∈ K)
    {T S : E → E} (hT : Measurable T) (hS : Measurable S)
    {h : ℝ} (hh : 0 ≤ h)
    (hTx : ∀ x ∈ K, ‖T x - x‖ ≤ h) (hSy : ∀ y ∈ K, ‖S y - y‖ ≤ h)
    {π κ : Measure (E × E)} (hπ : Vlasov.IsCoupling π μ ν)
    (hmap : π.map (Prod.map T S) = κ) :
    Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) π ∧
    Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) κ ∧
    (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂π) ≤
      (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂κ) +
        (μ univ).toReal * (2 * Metric.diam K * h) := by
  have hπmass : π univ = μ univ := by
    rw [← hπ.1, Measure.map_apply measurable_fst MeasurableSet.univ]; simp
  have hmass : μ univ = ν univ := by
    rw [← hπmass, ← hπ.2, Measure.map_apply measurable_snd MeasurableSet.univ]; simp
  by_cases hm : μ univ = 0
  · have hπzero : π = 0 := Measure.measure_univ_eq_zero.mp (hπmass.trans hm)
    have hκzero : κ = 0 := by rw [← hmap, hπzero, Measure.map_zero]
    simp [hπzero, hκzero, hm]
  have hmt : μ univ ≠ ∞ := measure_ne_top _ _
  let μ' := (μ univ)⁻¹ • μ
  let ν' := (μ univ)⁻¹ • ν
  let π' := (μ univ)⁻¹ • π
  let κ' := (μ univ)⁻¹ • κ
  have : IsProbabilityMeasure μ' := ⟨by
    dsimp [μ']; exact ENNReal.inv_mul_cancel hm hmt⟩
  have : IsProbabilityMeasure ν' := ⟨by
    dsimp [ν']; rw [← hmass, ENNReal.inv_mul_cancel hm hmt]⟩
  have hπ' : Vlasov.IsCoupling π' μ' ν' := by
    constructor <;> simp only [π', μ', ν', Measure.map_smul, hπ.1, hπ.2]
  have hmap' : π'.map (Prod.map T S) = κ' := by
    simp only [π', κ', Measure.map_smul, hmap]
  obtain ⟨hIπ, hIκ, hbound⟩ := quadratic_coupling_lift_cost_bound μ' ν' hK
    (Measure.ae_smul_measure hμ _) (Measure.ae_smul_measure hν _) hT hS hh hTx hSy hπ' hmap'
  have hπback : μ univ • π' = π := by
    dsimp [π']; rw [smul_smul, ENNReal.mul_inv_cancel hm hmt, one_smul]
  have hκback : μ univ • κ' = κ := by
    dsimp [κ']; rw [smul_smul, ENNReal.mul_inv_cancel hm hmt, one_smul]
  refine ⟨hπback ▸ hIπ.smul_measure hmt, hκback ▸ hIκ.smul_measure hmt, ?_⟩
  have hb := mul_le_mul_of_nonneg_left hbound (ENNReal.toReal_nonneg (a := μ univ))
  have heπ := integral_smul_measure (μ := π')
    (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) (μ univ)
  have heκ := integral_smul_measure (μ := κ')
    (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) (μ univ)
  simp only [hπback, smul_eq_mul] at heπ
  simp only [hκback, smul_eq_mul] at heκ
  rw [heπ, heκ]
  simpa only [mul_add] using hb

variable {I J : Type*} [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J]
  [DiscreteMeasurableSpace I] [DiscreteMeasurableSpace J]

/-- Every finite real plan between finite cell laws lifts with its literal
quadratic cost and a diameter error multiplied by the original total mass. -/
theorem exists_finiteIndex_realPlan_quadratic_coupling_lift_finite_mass
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ z ∂μ, z ∈ K) (hν : ∀ᵐ z ∂ν, z ∈ K)
    {T : E → I} {S : E → J} (hT : Measurable T) (hS : Measurable S)
    (α : I → ℝ) (β : J → ℝ)
    (hμmap : μ.map T = finiteWeightedMeasure α)
    (hνmap : ν.map S = finiteWeightedMeasure β)
    (P : I → J → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = α i) (hcol : ∀ j, ∑ i, P i j = β j)
    (x : I → E) (y : J → E) {h : ℝ} (hh : 0 ≤ h)
    (hTx : ∀ z ∈ K, ‖x (T z) - z‖ ≤ h) (hSy : ∀ z ∈ K, ‖y (S z) - z‖ ≤ h) :
    ∃ π : Measure (E × E), Vlasov.IsCoupling π μ ν ∧
      π.map (Prod.map T S) = finitePlanMeasure P ∧
      Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) π ∧
      (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂π) ≤
        (∑ i, ∑ j, P i j * (‖y j - x i‖ ^ 2 / 2)) +
          (μ univ).toReal * (2 * Metric.diam K * h) := by
  have hκ : Vlasov.IsCoupling (finitePlanMeasure P) (μ.map T) (ν.map S) := by
    constructor
    · rw [finitePlanMeasure_fst P hP, hμmap]
      congr 1; funext i; exact hrow i
    · rw [finitePlanMeasure_snd P hP, hνmap]
      congr 1; funext j; exact hcol j
  obtain ⟨π, hπ, hmap⟩ := exists_finiteCell_coupling_lift μ ν hT hS (finitePlanMeasure P) hκ
  have hx : Measurable x := measurable_of_countable x
  have hy : Measurable y := measurable_of_countable y
  let κ : Measure (E × E) := (finitePlanMeasure P).map (Prod.map x y)
  have hphys : π.map (Prod.map (x ∘ T) (y ∘ S)) = κ := by
    dsimp [κ]
    rw [← hmap, Measure.map_map (hx.prodMap hy) (hT.prodMap hS)]
    rfl
  obtain ⟨hπI, _, hcost⟩ := quadratic_coupling_lift_cost_bound_finite_mass μ ν hK hμ hν
    (hx.comp hT) (hy.comp hS) hh hTx hSy hπ hphys
  have hc : Measurable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) :=
    ((measurable_snd.sub measurable_fst).norm.pow_const 2).div_const 2
  have heq : (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂κ) =
      ∑ i, ∑ j, P i j * (‖y j - x i‖ ^ 2 / 2) := by
    rw [show κ = (finitePlanMeasure P).map (Prod.map x y) from rfl,
      integral_map (hx.prodMap hy).aemeasurable hc.aestronglyMeasurable]
    exact (finitePlanMeasure_integral P hP (fun z ↦ ‖y z.2 - x z.1‖ ^ 2 / 2)).2
  exact ⟨π, hπ, hmap, hπI, heq ▸ hcost⟩

end OTSelector.Reconstruction
