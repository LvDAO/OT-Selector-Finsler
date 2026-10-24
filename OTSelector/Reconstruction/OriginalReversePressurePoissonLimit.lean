import OTSelector.Reconstruction.OriginalReversePressurePoissonReadout
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Genuine full Poisson mean bounds imply the exactly normalized pressure bound. -/
open Set Function MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual count-intensity experiment gives the precise pressure
prefactor and tilt after taking the physical radius to infinity. The only
mean hypothesis is its literal finite Poisson expectation upper bound. -/
theorem originalPressure_le_of_actualPoisson_mean_bound {q : ℕ} (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {ρ τ p bound : ℝ} (hρ : 0 < ρ)
    (hp : Tendsto (fun side : ℝ ↦ legalMarkedScalePressure q id id α β kin g side
        (τ*ρ^(2/(q : ℝ)))) atTop (𝓝 p))
    (hmean : ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      (∫ cloud, legalMarkedTilted q id id ((2*R)^q) kin g τ cloud
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (ρ*(2*R)^q)))/(2*R)^q ≤ bound+ε) :
    p ≤ ρ^(-(1-2/(q : ℝ)))*bound := by
  let factor := ρ^(1-2/(q : ℝ))
  have hfactor : 0 < factor := Real.rpow_pos_of_pos hρ _
  have hscale : Tendsto (fun R : ℝ ↦ (2*R)*ρ^(1/(q : ℝ))) atTop atTop := by
    have hh := tendsto_id.const_mul_atTop (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.rpow_pos_of_pos hρ (1/(q : ℝ))))
    simpa only [id_eq,mul_assoc,mul_comm,mul_left_comm] using hh
  have hlim : Tendsto (fun R : ℝ ↦
      (∫ cloud, legalMarkedTilted q id id ((2*R)^q) kin g τ cloud
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (ρ*(2*R)^q)))/(2*R)^q)
      atTop (𝓝 (factor*p)) := by
    apply ((hp.comp hscale).const_mul factor).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (originalRawScaleTilted_normalized_mean_eq_pressure hq α β kin g hρ
      (mul_pos (by norm_num : (0 : ℝ) < 2) hR) τ).symm
  have hle : factor*p ≤ bound := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds (hmean ε hε)
  calc
    p ≤ bound/factor := (le_div_iff₀ hfactor).mpr (by simpa only [mul_comm] using hle)
    _ = ρ^(-(1-2/(q : ℝ)))*bound := by
      rw [Real.rpow_neg hρ.le]
      simp only [factor,div_eq_mul_inv,mul_comm]

end OTSelector.Reconstruction
