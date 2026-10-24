import OTSelector.Probability.PoissonExponentialFourthMoment
import OTSelector.Reconstruction.OriginalStationaryFiniteIntensityCounts

/-! Fourth moments of complete unchanged original input counts. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- A finite original source intensity produces the polynomial fourth moment
of the actual full count, including noncompact marked phase envelopes. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_fourth_moment
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod α) B ≠ ∞) :
    (∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0}) < ∞) ∧
      Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q))
        (B ×ˢ {0})).toReal ^ 4) (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0})).toReal ^ 4
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          192 * Real.exp (Real.exp 1 - 1) *
            (1 + (((volume : Measure (Fin q → ℝ)).prod α) B).toReal ^ 4) := by
  have hm := fun t ht ↦ M.original_source_exp_moment_of_finite_intensity hB hfin (t := t) ht
  have hN : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0})).toReal) :=
    ((Measure.measurable_coe (hB.prod (measurableSet_singleton 0))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  refine ⟨(hm 0 le_rfl).1, ?_⟩
  exact integrable_fourth_pow_and_integral_le_of_poisson_exp_bound hN.aemeasurable
    (.of_forall (fun _ ↦ ENNReal.toReal_nonneg)) ENNReal.toReal_nonneg
    (fun t ht ↦ (hm t ht).2.1) (fun t ht ↦ (hm t ht).2.2)

/-- The same fourth-moment estimate holds for the complete original target count. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_fourth_moment
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod β) B ≠ ∞) :
    (∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1}) < ∞) ∧
      Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q))
        (B ×ˢ {1})).toReal ^ 4) (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1})).toReal ^ 4
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          192 * Real.exp (Real.exp 1 - 1) *
            (1 + (((volume : Measure (Fin q → ℝ)).prod β) B).toReal ^ 4) := by
  have hm := fun t ht ↦ M.original_target_exp_moment_of_finite_intensity hB hfin (t := t) ht
  have hN : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1})).toReal) :=
    ((Measure.measurable_coe (hB.prod (measurableSet_singleton 1))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  refine ⟨(hm 0 le_rfl).1, ?_⟩
  exact integrable_fourth_pow_and_integral_le_of_poisson_exp_bound hN.aemeasurable
    (.of_forall (fun _ ↦ ENNReal.toReal_nonneg)) ENNReal.toReal_nonneg
    (fun t ht ↦ (hm t ht).2.1) (fun t ht ↦ (hm t ht).2.2)

end OTSelector.Reconstruction
