import OTSelector.PointProcess.PairLaplaceDetermination
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonLaplace
import OTSelector.PointProcess.CutoffLaplaceLaw

/-!
# Exact separated-support factorization of the original input

The prescribed two-color Poisson Laplace functional itself gives independence
of disjoint compact observations. Both original clock laws and immutable colors
are retained. All global exponent integrals are genuinely integrable.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

section Exponents
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]

/-- A compact test gives a genuinely integrable global Laplace exponent. -/
theorem integrable_compactLaplaceExponent (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (F : C_c(X, ℝ)) : Integrable (fun x ↦ Real.exp (-F x) - 1) μ := by
  apply Continuous.integrable_of_hasCompactSupport
    ((Real.continuous_exp.comp F.continuous.neg).sub continuous_const)
  exact F.hasCompactSupport.comp_left (g := fun r : ℝ ↦ Real.exp (-r) - 1) (by simp)

/-- Disjoint tests split the global Poisson exponent with no infinite-volume shortcut. -/
theorem integral_compactLaplaceExponent_add_of_disjoint
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (F G : C_c(X, ℝ))
    (hdisj : ∀ x, F x = 0 ∨ G x = 0) :
    (∫ x, (Real.exp (-(F + G) x) - 1) ∂μ) =
      (∫ x, (Real.exp (-F x) - 1) ∂μ) + ∫ x, (Real.exp (-G x) - 1) ∂μ := by
  rw [← integral_add (integrable_compactLaplaceExponent μ F)
    (integrable_compactLaplaceExponent μ G)]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    rcases hdisj x with hF | hG
    · simp [hF]
    · simp [hG]
end Exponents

/-- Restricting a colored compact test to one immutable color stays compact. -/
def legalColoredInputTestSlice (q : ℕ) (F : C_c(LegalColoredInputPoint q, ℝ))
    (c : Fin 2) : C_c(LegalMarkedPhysicalPoint q, ℝ) :=
  F.comp
    { toFun := fun x ↦ (x, c)
      continuous_toFun := continuous_id.prodMk continuous_const
      cocompact_tendsto' :=
        (Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap
          (isEmbedding_prodMkLeft c) (isClosedMap_prodMk_right c)).tendsto_cocompact }

@[simp] theorem legalColoredInputTestSlice_apply (q : ℕ)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (c : Fin 2) (x : LegalMarkedPhysicalPoint q) :
    legalColoredInputTestSlice q F c x = F (x, c) := rfl

/-- The complete original two-color Haar-times-clock exponent. -/
def legalOriginalInputPoissonExponent (q : ℕ) (α β : Measure ℝ)
    (F : C_c(LegalColoredInputPoint q, ℝ)) : ℝ :=
  (∫ x, (Real.exp (-F (x, 0)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod α) +
    ∫ y, (Real.exp (-F (y, 1)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod β

/-- Separated compact tests add their exact original two-color exponent. -/
theorem legalOriginalInputPoissonExponent_add_of_disjoint
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (F G : C_c(LegalColoredInputPoint q, ℝ))
    (hdisj : ∀ x, F x = 0 ∨ G x = 0) :
    legalOriginalInputPoissonExponent q α β (F + G) =
      legalOriginalInputPoissonExponent q α β F + legalOriginalInputPoissonExponent q α β G := by
  have heq (γ : Measure ℝ) [IsProbabilityMeasure γ] (c : Fin 2) :
      (∫ x, (Real.exp (-(F + G) (x, c)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ) =
      (∫ x, (Real.exp (-F (x, c)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ) +
        ∫ x, (Real.exp (-G (x, c)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ := by
    simpa only [legalColoredInputTestSlice_apply, CompactlySupportedContinuousMap.add_apply]
      using integral_compactLaplaceExponent_add_of_disjoint
        ((volume : Measure (Fin q → ℝ)).prod γ)
        (legalColoredInputTestSlice q F c) (legalColoredInputTestSlice q G c)
        (fun x ↦ hdisj (x, c))
  unfold legalOriginalInputPoissonExponent
  rw [heq α 0, heq β 1]
  ring

/-- Actual original-input compact Laplace identities imply exact separated-test factorization. -/
theorem originalInput_laplace_factorization_of_disjoint
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : Measure (LocalFiniteMeasure (LegalColoredInputPoint q))) [IsProbabilityMeasure ρ]
    (hLaplace : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) =
        Real.exp (legalOriginalInputPoissonExponent q α β F.1))
    (F G : LegalNonnegativeInputTest (LegalColoredInputPoint q))
    (hdisj : ∀ x, F.1 x = 0 ∨ G.1 x = 0) :
    (∫ μ, legalInputMeasureLaplace F μ * legalInputMeasureLaplace G μ ∂ρ) =
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) * ∫ μ, legalInputMeasureLaplace G μ ∂ρ := by
  have heq : (fun μ ↦ legalInputMeasureLaplace F μ * legalInputMeasureLaplace G μ) =
      fun μ ↦ legalInputMeasureLaplace
        ⟨F.1 + G.1, fun x ↦ add_nonneg (F.2 x) (G.2 x)⟩ μ :=
    funext fun μ ↦ (legalInputMeasureLaplace_add F G μ).symm
  rw [heq, hLaplace, hLaplace, hLaplace,
    legalOriginalInputPoissonExponent_add_of_disjoint q α β F.1 G.1 hdisj, Real.exp_add]

/-- The genuine original stationary matching provides this global input field internally. -/
theorem LegalWeightedStationaryPoissonMatching.inputMeasure_laplace_eq_global_exp
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (F : LegalNonnegativeInputTest (LegalColoredInputPoint q)) :
    (∫ μ, legalInputMeasureLaplace F μ
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) =
      Real.exp (legalOriginalInputPoissonExponent q α β F.1) := by
  rw [integral_map measurable_snd.aemeasurable
    (legalInputMeasureLaplace F).continuous.aestronglyMeasurable]
  exact M.input_laplace_eq_global_exp F.1 F.2

end OTSelector.Reconstruction
