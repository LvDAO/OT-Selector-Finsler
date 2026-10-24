import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationCellLift
import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationError

/-! Genuine compact probability couplings lifted from finite grids with quadratic cost control. -/
open MeasureTheory Set
noncomputable section
namespace OTSelector.Reconstruction
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Every genuine finite grid coupling lifts to the original probabilities,
with the literal quadratic transport cost controlled by a vanishing diameter error. -/
theorem exists_finiteRange_quadratic_coupling_lift
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ y ∂ν, y ∈ K)
    {T S : E → E} (hT : Measurable T) (hS : Measurable S)
    (hTfin : (range T).Finite) (hSfin : (range S).Finite)
    {h : ℝ} (hh : 0 ≤ h)
    (hTx : ∀ x ∈ K, ‖T x - x‖ ≤ h) (hSy : ∀ y ∈ K, ‖S y - y‖ ≤ h)
    (κ : Measure (E × E)) (hκ : Vlasov.IsCoupling κ (μ.map T) (ν.map S)) :
    ∃ π : Measure (E × E), Vlasov.IsCoupling π μ ν ∧
      π.map (Prod.map T S) = κ ∧
      Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) π ∧
      Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) κ ∧
      (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂π) ≤
        (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂κ) + 2 * Metric.diam K * h := by
  obtain ⟨π, hπ, hmap⟩ := exists_finiteRange_coupling_lift μ ν hT hS hTfin hSfin κ hκ
  exact ⟨π, hπ, hmap, quadratic_coupling_lift_cost_bound μ ν hK hμ hν
    hT hS hh hTx hSy hπ hmap⟩

/-- Finite grid cost bounds at arbitrarily small mesh produce genuine continuous
couplings within every positive error. No continuous optimizer is assumed or selected. -/
theorem exists_quadratic_coupling_of_finite_grid_bounds
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ y ∂ν, y ∈ K) (B : ℝ)
    (hgrid : ∀ h : ℝ, 0 < h → ∃ T S : E → E,
      Measurable T ∧ Measurable S ∧ (range T).Finite ∧ (range S).Finite ∧
      (∀ x ∈ K, ‖T x - x‖ ≤ h) ∧ (∀ y ∈ K, ‖S y - y‖ ≤ h) ∧
      ∃ κ : Measure (E × E), Vlasov.IsCoupling κ (μ.map T) (ν.map S) ∧
        (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂κ) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ π : Measure (E × E), Vlasov.IsCoupling π μ ν ∧
      Integrable (fun z : E × E ↦ ‖z.2 - z.1‖ ^ 2 / 2) π ∧
      (∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂π) ≤ B + ε := by
  intro ε hε
  let h := ε / (2 * Metric.diam K + 1)
  have hden : 0 < 2 * Metric.diam K + 1 := by positivity
  have hh : 0 < h := div_pos hε hden
  obtain ⟨T, S, hT, hS, hTf, hSf, hTx, hSy, κ, hκ, hcost⟩ := hgrid h hh
  obtain ⟨π, hπ, _, hπI, _, hbound⟩ := exists_finiteRange_quadratic_coupling_lift
    μ ν hK hμ hν hT hS hTf hSf hh.le hTx hSy κ hκ
  refine ⟨π, hπ, hπI, hbound.trans ?_⟩
  have he : 2 * Metric.diam K * h ≤ ε := by
    dsimp [h]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    nlinarith [Metric.diam_nonneg (s := K)]
  linarith

end OTSelector.Reconstruction
