import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationFiniteMass

/-! Literal real costs of finite transport matrices and their genuine original-space lifts. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
variable {I J : Type*} [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J]
  [DiscreteMeasurableSpace I] [DiscreteMeasurableSpace J]

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A finite real transport matrix lifts to the original compact probabilities
with exact cell readout and its actual quadratic matrix cost plus `2 * diam K * h`. -/
theorem exists_finiteIndex_realPlan_quadratic_coupling_lift
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
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
        (∑ i, ∑ j, P i j * (‖y j - x i‖ ^ 2 / 2)) + 2 * Metric.diam K * h := by
  simpa only [measure_univ, ENNReal.toReal_one, one_mul] using
    exists_finiteIndex_realPlan_quadratic_coupling_lift_finite_mass μ ν hK hμ hν
      hT hS α β hμmap hνmap P hP hrow hcol x y hh hTx hSy

end OTSelector.Reconstruction
