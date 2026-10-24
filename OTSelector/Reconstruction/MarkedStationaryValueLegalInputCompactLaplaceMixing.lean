import OTSelector.Reconstruction.MarkedStationaryValueLegalInputSeparatedShift

/-!
# Exact compact Laplace mixing of the original Poisson input

Repeated nonzero spatial translation eventually gives exact factorization.
For a stationary original input, the second factor is its unchanged original
expectation. Genuine matching laws supply the required original input formula.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Separated actual compact Laplace observations factor exactly after
sufficiently many steps of any fixed nonzero spatial translation. -/
theorem eventually_originalInput_compactLaplace_factorization_shift
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : Measure (LocalFiniteMeasure (LegalColoredInputPoint q))) [IsProbabilityMeasure ρ]
    (hLaplace : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) =
        Real.exp (legalOriginalInputPoissonExponent q α β F.1))
    (F G : LegalNonnegativeInputTest (LegalColoredInputPoint q))
    {v : Fin q → ℝ} (hv : v ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (∫ μ, legalInputMeasureLaplace F μ * legalInputMeasureLaplace G
        (localFiniteMapHomeomorph (legalColoredInputPointReroot q ((n : ℝ) • v)) μ) ∂ρ) =
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) *
        ∫ μ, legalInputMeasureLaplace G
          (localFiniteMapHomeomorph (legalColoredInputPointReroot q ((n : ℝ) • v)) μ) ∂ρ := by
  filter_upwards [eventually_disjoint_legalColoredInputTests_shift F.1 G.1 hv] with n hn
  let G' : LegalNonnegativeInputTest (LegalColoredInputPoint q) :=
    ⟨G.1.comp (legalColoredInputPointReroot q ((n : ℝ) • v)).toCocompactMap,
      fun x ↦ G.2 (legalColoredInputPointReroot q ((n : ℝ) • v) x)⟩
  have hread (μ) : legalInputMeasureLaplace G
      (localFiniteMapHomeomorph (legalColoredInputPointReroot q ((n : ℝ) • v)) μ) =
      legalInputMeasureLaplace G' μ :=
    legalInputMeasureLaplace_localFiniteMapHomeomorph _ G μ
  simp_rw [hread]
  exact originalInput_laplace_factorization_of_disjoint α β ρ hLaplace F G' hn

/-- Stationarity makes the eventual product the two unchanged original expectations. -/
theorem eventually_originalInput_compactLaplace_mixing
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : Measure (LocalFiniteMeasure (LegalColoredInputPoint q))) [IsProbabilityMeasure ρ]
    (hLaplace : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) =
        Real.exp (legalOriginalInputPoissonExponent q α β F.1))
    (hstat : ∀ w : Fin q → ℝ,
      MeasurePreserving (localFiniteMapHomeomorph (legalColoredInputPointReroot q w)) ρ ρ)
    (F G : LegalNonnegativeInputTest (LegalColoredInputPoint q))
    {v : Fin q → ℝ} (hv : v ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (∫ μ, legalInputMeasureLaplace F μ * legalInputMeasureLaplace G
        (localFiniteMapHomeomorph (legalColoredInputPointReroot q ((n : ℝ) • v)) μ) ∂ρ) =
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) * ∫ μ, legalInputMeasureLaplace G μ ∂ρ := by
  filter_upwards [eventually_originalInput_compactLaplace_factorization_shift α β ρ
    hLaplace F G hv] with n hn
  rw [hn]
  congr 1
  calc
    _ = ∫ μ, legalInputMeasureLaplace G μ
        ∂ρ.map (localFiniteMapHomeomorph (legalColoredInputPointReroot q ((n : ℝ) • v))) :=
      (integral_map (hstat ((n : ℝ) • v)).measurable.aemeasurable
        (legalInputMeasureLaplace G).continuous.aestronglyMeasurable).symm
    _ = _ := by rw [(hstat ((n : ℝ) • v)).map_eq]

/-- The original stationary matching itself yields eventual independence of
any two compact observations of its complete marked/color input. -/
theorem LegalWeightedStationaryPoissonMatching.eventually_inputRestrictionLocal_indep_shift
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {U V : Set (LegalColoredInputPoint q)} (hU : IsCompact U) (hV : IsCompact V)
    {v : Fin q → ℝ} (hv : v ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      IndepFun (legalInputRestrictionLocal U)
        (fun μ ↦ legalInputRestrictionLocal V
          (localFiniteMapHomeomorph (legalColoredInputPointReroot q ((n : ℝ) • v)) μ))
        ((M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) := by
  let : IsProbabilityMeasure
      ((M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact eventually_legalInputRestrictionLocal_indep_shift α β _
    M.inputMeasure_laplace_eq_global_exp hU hV hv

end OTSelector.Reconstruction
