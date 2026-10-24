import OTSelector.Reconstruction.CompactRestrictionErgodicity
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalInputTranslation
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputSeparatedShift

/-!
# Ergodicity of the complete original colored Poisson input

Every nonzero spatial translation is ergodic for the original two-color Poisson input law.
This concerns the entire original input, with all clocks and colors retained.  The genuine
matching corollary derives the input functional and both probability clock laws internally.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual original Poisson Laplace field and spatial stationarity force ergodicity of
the whole input under every single nonzero spatial translation. -/
theorem ergodic_legalOriginalInputTranslation_of_laplace
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : Measure (LocalFiniteMeasure (LegalColoredInputPoint q))) [IsProbabilityMeasure ρ]
    (hLaplace : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) =
        Real.exp (legalOriginalInputPoissonExponent q α β F.1))
    {v : Fin q → ℝ} (hv : v ≠ 0)
    (hstat : MeasurePreserving (legalOriginalInputTranslation q v) ρ ρ) :
    Ergodic (legalOriginalInputTranslation q v) ρ := by
  apply ergodic_of_compact_restriction_independence ρ _ hstat
  intro U hU
  obtain ⟨k, hk⟩ :=
    (eventually_legalInputRestrictionLocal_indep_shift α β ρ hLaplace hU hU hv).exists
  refine ⟨k, ?_⟩
  rw [legalOriginalInputTranslation_iterate]
  exact hk

/-- Every genuine matching has an ergodic complete original input law.  No additional
ergodicity, conditional-input, topology, or matching-selection hypothesis is imposed. -/
theorem LegalWeightedStationaryPoissonMatching.originalInput_ergodic
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {v : Fin q → ℝ} (hv : v ≠ 0) :
    Ergodic (legalOriginalInputTranslation q v)
      ((M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have : IsProbabilityMeasure α := by
    rw [← M.source_clock]
    exact Measure.isProbabilityMeasure_map (measurable_fst.comp measurable_fst).aemeasurable
  have : IsProbabilityMeasure β := by
    rw [← M.target_clock]
    exact Measure.isProbabilityMeasure_map (measurable_snd.comp measurable_fst).aemeasurable
  have : IsProbabilityMeasure
      ((M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact ergodic_legalOriginalInputTranslation_of_laplace α β _
    M.inputMeasure_laplace_eq_global_exp hv
    (measurePreserving_legalOriginalInputTranslation _ v (M.stationary v))

end OTSelector.Reconstruction
