import OTSelector.Probability.CavitySemidiscretePlanMeasurable

/-!
# Averaging entire actual semidiscrete coupling measures
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Averaging actual allocation coefficients averages their entire coupling measures. -/
theorem semidiscreteAllocationMeasure_average
    (μ : Measure S) (p : Fin (m + 1) → ℝ)
    (a b : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) (hb : IsSemidiscreteAllocation μ p b)
    (ham : ∀ j, Measurable (fun s ↦ a s j))
    (hbm : ∀ j, Measurable (fun s ↦ b s j)) :
    semidiscreteAllocationMeasure μ (fun s j ↦ (a s j + b s j) / 2) =
      (2 : ℝ≥0∞)⁻¹ • (semidiscreteAllocationMeasure μ a + semidiscreteAllocationMeasure μ b) := by
  have hd (j : Fin (m + 1)) :
      μ.withDensity (fun s ↦ ENNReal.ofReal ((a s j + b s j) / 2)) =
        (2 : ℝ≥0∞)⁻¹ • (μ.withDensity (fun s ↦ ENNReal.ofReal (a s j)) +
          μ.withDensity (fun s ↦ ENNReal.ofReal (b s j))) := by
    calc
      _ = μ.withDensity (fun s ↦ (2 : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (a s j) + ENNReal.ofReal (b s j))) := by
        apply withDensity_congr_ae
        filter_upwards [ha.nonneg, hb.nonneg] with s has hbs
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (add_nonneg (has j) (hbs j)),
          ENNReal.ofReal_add (has j) (hbs j), ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num [mul_comm]
      _ = _ := by
        change μ.withDensity ((2 : ℝ≥0∞)⁻¹ •
          ((fun s ↦ ENNReal.ofReal (a s j)) + (fun s ↦ ENNReal.ofReal (b s j)))) = _
        rw [withDensity_smul _ ((ham j).ennreal_ofReal.add (hbm j).ennreal_ofReal),
          withDensity_add_left (ham j).ennreal_ofReal]
  simp only [semidiscreteAllocationMeasure, hd, Measure.map_smul,
    Measure.map_add _ _ (show Measurable (fun s : S ↦ (s, _)) from
      measurable_id.prodMk measurable_const)]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]

end OTSelector.Probability
