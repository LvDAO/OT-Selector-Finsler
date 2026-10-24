import OTSelector.Probability.BadEventSecondMoment
import OTSelector.Reconstruction.OriginalStationaryFourthMoments

/-! # Actual original Poisson count errors on dependent geometric bad events -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The complete original source count has a quantitatively small actual
mean-square contribution on any measurable bad event, even when that event
is defined from the same original cloud. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_badEvent_second_moment
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod α) B ≠ ∞)
    {A : Set (LegalMarkedOptimalInputScene q)} (hA : MeasurableSet A) :
    let N : LegalMarkedOptimalInputScene q → ℝ := fun s ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0})).toReal
    Integrable (fun s ↦ (A.indicator N s) ^ 2) (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, (A.indicator N s) ^ 2 ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        (192 * Real.exp (Real.exp 1 - 1) *
          (1 + (((volume : Measure (Fin q → ℝ)).prod α) B).toReal ^ 4)) ^ (1 / 2 : ℝ) *
          ((M.law : Measure (LegalMarkedOptimalInputScene q)).real A) ^ (1 / 2 : ℝ) := by
  dsimp only
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0})).toReal) :=
    ((Measure.measurable_coe (hB.prod (measurableSet_singleton 0))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  have h4 := M.original_source_fourth_moment hB hfin
  have h2 := integrable_indicator_sq_and_integral_le_fourth hm.aestronglyMeasurable h4.2.1 hA
  refine ⟨h2.1, h2.2.trans ?_⟩
  gcongr
  exact h4.2.2

/-- The same quantitative actual mean-square bad-event bound holds for the
whole unchanged original target color. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_badEvent_second_moment
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod β) B ≠ ∞)
    {A : Set (LegalMarkedOptimalInputScene q)} (hA : MeasurableSet A) :
    let N : LegalMarkedOptimalInputScene q → ℝ := fun s ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1})).toReal
    Integrable (fun s ↦ (A.indicator N s) ^ 2) (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, (A.indicator N s) ^ 2 ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        (192 * Real.exp (Real.exp 1 - 1) *
          (1 + (((volume : Measure (Fin q → ℝ)).prod β) B).toReal ^ 4)) ^ (1 / 2 : ℝ) *
          ((M.law : Measure (LegalMarkedOptimalInputScene q)).real A) ^ (1 / 2 : ℝ) := by
  dsimp only
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1})).toReal) :=
    ((Measure.measurable_coe (hB.prod (measurableSet_singleton 1))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  have h4 := M.original_target_fourth_moment hB hfin
  have h2 := integrable_indicator_sq_and_integral_le_fourth hm.aestronglyMeasurable h4.2.1 hA
  refine ⟨h2.1, h2.2.trans ?_⟩
  gcongr
  exact h4.2.2

end OTSelector.Reconstruction
