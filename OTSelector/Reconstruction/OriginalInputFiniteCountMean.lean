import OTSelector.Reconstruction.OriginalStationaryFiniteIntensityCounts

/-! Literal full original colored-input count means on arbitrary finite-intensity
windows. No independence of selected matching edges is assumed. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The unchanged whole input's color count has its exact physical intensity. -/
theorem lintegral_originalInput_colorCount {q : ℕ}
    (P : Measure (LegalMarkedOptimalInputScene q)) (c : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) ∂P) =
      legalMarkedInputColorIntensity q P c B := by
  rw [← lintegral_legalInputColorMeasure_eq_intensity q P c hB]
  apply lintegral_congr
  intro s
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hB,
    Measure.restrict_apply (hB.preimage measurable_fst)]
  congr 1

/-- Finite original intensity gives integrability of the literal real-valued
color count and identifies its expectation with the same original intensity. -/
theorem originalInput_colorCount_integrable_and_integral {q : ℕ}
    (P : Measure (LegalMarkedOptimalInputScene q)) (c : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : legalMarkedInputColorIntensity q P c B ≠ ∞) :
    Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})).toReal) P ∧
      (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})).toReal ∂P) =
        (legalMarkedInputColorIntensity q P c B).toReal := by
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})) :=
    (Measure.measurable_coe (hB.prod (measurableSet_singleton c))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)
  have hmean : (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) ∂P) ≠ ∞ := by
    rwa [lintegral_originalInput_colorCount P c hB]
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hmean, ?_⟩
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hmean),
    lintegral_originalInput_colorCount P c hB]

/-- Every genuine original matching has the exact source count mean. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_count_integrable_and_integral
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod α) B ≠ ∞) :
    Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0})).toReal)
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {0})).toReal
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
        (((volume : Measure (Fin q → ℝ)).prod α) B).toReal := by
  have hi := originalInput_colorCount_integrable_and_integral (M.law : Measure _) 0 hB
  rw [M.inputColorIntensities_eq_volume_prod.1] at hi
  exact hi hfin

/-- The target count mean uses the unchanged original target clock law. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_count_integrable_and_integral
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hfin : ((volume : Measure (Fin q → ℝ)).prod β) B ≠ ∞) :
    Integrable (fun s ↦ ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1})).toReal)
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {1})).toReal
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
        (((volume : Measure (Fin q → ℝ)).prod β) B).toReal := by
  have hi := originalInput_colorCount_integrable_and_integral (M.law : Measure _) 1 hB
  rw [M.inputColorIntensities_eq_volume_prod.2] at hi
  exact hi hfin

end OTSelector.Reconstruction
