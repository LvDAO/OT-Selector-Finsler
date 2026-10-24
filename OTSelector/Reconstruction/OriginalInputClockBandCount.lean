import OTSelector.Reconstruction.OriginalInputFiniteCountMean
import OTSelector.MeasureTheory.ClockShiftBandMass

/-! Birth-band counts are literal counts of the full unchanged original colored
input. Their expectation uses the original physical Haar factor. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The original source count in a physical window times a clock band has
mean bounded by the literal Haar volume times its original band mass bound. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_clockBand_count_mean_le
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A : Set (Fin q → ℝ)} (hA : MeasurableSet A) (hAfinite : volume A ≠ ∞)
    {level a b B : ℝ} (hB : 0 ≤ B)
    (hband : (α.map (fun x : ℝ ↦ x - level)) (Ioc a b) ≤ ENNReal.ofReal B) :
    let W := A ×ˢ Ioc (level + a) (level + b)
    Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal)
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ (volume A).toReal * B := by
  dsimp only
  have hclock : α (Ioc (level + a) (level + b)) ≤ ENNReal.ofReal B := by
    rwa [map_clock_sub_Ioc] at hband
  have hclockfin : α (Ioc (level + a) (level + b)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hclock
  have hfin : ((volume : Measure (Fin q → ℝ)).prod α)
      (A ×ˢ Ioc (level + a) (level + b)) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hAfinite hclockfin
  obtain ⟨hi, heq⟩ := M.original_source_count_integrable_and_integral
    (hA.prod measurableSet_Ioc) hfin
  refine ⟨hi, ?_⟩
  rw [heq, Measure.prod_prod, ENNReal.toReal_mul]
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_le_of_le_ofReal hB hclock) ENNReal.toReal_nonneg

/-- The original target count in a physical window times a clock band has
mean bounded by the literal Haar volume times its original band mass bound. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_clockBand_count_mean_le
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A : Set (Fin q → ℝ)} (hA : MeasurableSet A) (hAfinite : volume A ≠ ∞)
    {level a b B : ℝ} (hB : 0 ≤ B)
    (hband : (β.map (fun x : ℝ ↦ x - level)) (Ioc a b) ≤ ENNReal.ofReal B) :
    let W := A ×ˢ Ioc (level + a) (level + b)
    Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal)
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ (volume A).toReal * B := by
  dsimp only
  have hclock : β (Ioc (level + a) (level + b)) ≤ ENNReal.ofReal B := by
    rwa [map_clock_sub_Ioc] at hband
  have hclockfin : β (Ioc (level + a) (level + b)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hclock
  have hfin : ((volume : Measure (Fin q → ℝ)).prod β)
      (A ×ˢ Ioc (level + a) (level + b)) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hAfinite hclockfin
  obtain ⟨hi, heq⟩ := M.original_target_count_integrable_and_integral
    (hA.prod measurableSet_Ioc) hfin
  refine ⟨hi, ?_⟩
  rw [heq, Measure.prod_prod, ENNReal.toReal_mul]
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_le_of_le_ofReal hB hclock) ENNReal.toReal_nonneg

end OTSelector.Reconstruction
