import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplaceFactorization
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowLocalLaw
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointStationarity

/-!
# Distant spatial translations of the original colored input

For every nonzero spatial translation, two fixed compact observations eventually
use disjoint original spatial locations. The exact original Poisson field then
makes their actual compact-window restrictions independent.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- Pushforward of the same actual measure pulls back its original compact test. -/
theorem legalInputMeasureLaplace_localFiniteMapHomeomorph
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]
    (e : X ≃ₜ X) (F : LegalNonnegativeInputTest X) (μ : LocalFiniteMeasure X) :
    legalInputMeasureLaplace F (localFiniteMapHomeomorph e μ) =
      legalInputMeasureLaplace ⟨F.1.comp e.toCocompactMap, fun x ↦ F.2 (e x)⟩ μ := by
  change Real.exp (-(∫ x, F.1 x ∂(μ : Measure X).map e)) =
    Real.exp (-(∫ x, F.1 (e x) ∂(μ : Measure X)))
  congr 1
  congr 1
  exact integral_map e.continuous.measurable.aemeasurable
    F.1.continuous.measurable.aestronglyMeasurable

/-- Two compact colored tests are spatially disjoint after sufficiently many
steps of any fixed nonzero spatial translation; their original clocks are fixed. -/
theorem eventually_disjoint_legalColoredInputTests_shift
    {q : ℕ} (F G : C_c(LegalColoredInputPoint q, ℝ))
    {v : Fin q → ℝ} (hv : v ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ x : LegalColoredInputPoint q,
      F x = 0 ∨ G (legalColoredInputPointReroot q ((n : ℝ) • v) x) = 0 := by
  obtain ⟨a, ha, hF⟩ := (F.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  obtain ⟨b, hb, hG⟩ := (G.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlarge : ∀ᶠ n : ℕ in atTop, (a + b) / ‖v‖ < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop _)
  filter_upwards [hlarge] with n hn
  intro x
  by_cases hx : F x = 0
  · exact Or.inl hx
  · right
    by_contra hy
    have hFx : ‖x.1.1‖ < a := hF _ ⟨x, subset_tsupport F hx, rfl⟩
    have hGx : ‖x.1.1 - (n : ℝ) • v‖ < b :=
      hG _ ⟨legalColoredInputPointReroot q ((n : ℝ) • v) x,
        subset_tsupport G hy, rfl⟩
    have hbound : (n : ℝ) * ‖v‖ < a + b := by
      calc
        (n : ℝ) * ‖v‖ = ‖(n : ℝ) • v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
        _ = ‖x.1.1 - (x.1.1 - (n : ℝ) • v)‖ := by congr 1; abel
        _ ≤ ‖x.1.1‖ + ‖x.1.1 - (n : ℝ) • v‖ := norm_sub_le _ _
        _ < a + b := add_lt_add hFx hGx
    exact (not_lt_of_ge ((div_lt_iff₀ hvpos).mp hn).le) hbound

/-- Fixed disjoint cutoff observations of the same original input are independent. -/
theorem originalInput_indepFun_cutoffs_shift_of_disjoint
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : Measure (LocalFiniteMeasure (LegalColoredInputPoint q))) [IsProbabilityMeasure ρ]
    (hLaplace : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) =
        Real.exp (legalOriginalInputPoissonExponent q α β F.1))
    (η ζ : C_c(LegalColoredInputPoint q, ℝ))
    (hη : ∀ x, 0 ≤ η x) (hζ : ∀ x, 0 ≤ ζ x) (v : Fin q → ℝ)
    (hdisj : ∀ x, η x = 0 ∨ ζ (legalColoredInputPointReroot q v x) = 0) :
    IndepFun (legalInputCutoffLocal η.toContinuousMap)
      (fun μ ↦ legalInputCutoffLocal ζ.toContinuousMap
        (localFiniteMapHomeomorph (legalColoredInputPointReroot q v) μ)) ρ := by
  have hmη := (continuous_legalInputCutoffLocal η.toContinuousMap hη).measurable
  have hmζ := ((continuous_legalInputCutoffLocal ζ.toContinuousMap hζ).comp
    (continuous_localFiniteMapHomeomorph (legalColoredInputPointReroot q v))).measurable
  apply indepFun_of_legalInput_compact_laplace_factorization ρ _ _ hmη hmζ
  intro F G
  let A : LegalNonnegativeInputTest (LegalColoredInputPoint q) :=
    ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap,
      fun x ↦ mul_nonneg (F.2 x) (hη x)⟩
  let B₀ : LegalNonnegativeInputTest (LegalColoredInputPoint q) :=
    ⟨LocalFiniteMeasure.weightedContinuousTest G.1 ζ.toContinuousMap,
      fun x ↦ mul_nonneg (G.2 x) (hζ x)⟩
  let B : LegalNonnegativeInputTest (LegalColoredInputPoint q) :=
    ⟨B₀.1.comp (legalColoredInputPointReroot q v).toCocompactMap,
      fun x ↦ B₀.2 (legalColoredInputPointReroot q v x)⟩
  have hA (μ) : legalInputMeasureLaplace F (legalInputCutoffLocal η.toContinuousMap μ) =
      legalInputMeasureLaplace A μ := by
    change Real.exp (-LocalFiniteMeasure.testIntegral
      (legalInputCutoffLocal η.toContinuousMap μ) F.1) = _
    rw [testIntegral_legalInputCutoffLocal η.toContinuousMap hη]
    rfl
  have hB (μ) : legalInputMeasureLaplace G
      (legalInputCutoffLocal ζ.toContinuousMap
        (localFiniteMapHomeomorph (legalColoredInputPointReroot q v) μ)) =
      legalInputMeasureLaplace B μ := by
    change Real.exp (-LocalFiniteMeasure.testIntegral
      (legalInputCutoffLocal ζ.toContinuousMap
        (localFiniteMapHomeomorph (legalColoredInputPointReroot q v) μ)) G.1) = _
    rw [testIntegral_legalInputCutoffLocal ζ.toContinuousMap hζ]
    exact legalInputMeasureLaplace_localFiniteMapHomeomorph
      (legalColoredInputPointReroot q v) B₀ μ
  simp only [Function.comp_apply]
  simp_rw [hA, hB]
  apply originalInput_laplace_factorization_of_disjoint α β ρ hLaplace A B
  intro x
  rcases hdisj x with hx | hx
  · left
    change F.1 x * η x = 0
    rw [hx, mul_zero]
  · right
    change G.1 (legalColoredInputPointReroot q v x) *
      ζ (legalColoredInputPointReroot q v x) = 0
    rw [hx, mul_zero]

/-- Every two actual compact marked/color windows eventually become independent
under repeated nonzero spatial translation of the original colored input. -/
theorem eventually_legalInputRestrictionLocal_indep_shift
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (ρ : Measure (LocalFiniteMeasure (LegalColoredInputPoint q))) [IsProbabilityMeasure ρ]
    (hLaplace : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace F μ ∂ρ) =
        Real.exp (legalOriginalInputPoissonExponent q α β F.1))
    {U V : Set (LegalColoredInputPoint q)} (hU : IsCompact U) (hV : IsCompact V)
    {v : Fin q → ℝ} (hv : v ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      IndepFun (legalInputRestrictionLocal U)
        (fun μ ↦ legalInputRestrictionLocal V
          (localFiniteMapHomeomorph (legalColoredInputPointReroot q ((n : ℝ) • v)) μ)) ρ := by
  obtain ⟨η, hηU, hη⟩ := LocalFiniteMeasure.exists_compact_cutoff hU
  obtain ⟨ζ, hζV, hζ⟩ := LocalFiniteMeasure.exists_compact_cutoff hV
  have hevent := eventually_disjoint_legalColoredInputTests_shift η ζ hv
  filter_upwards [hevent] with n hn
  have hind := originalInput_indepFun_cutoffs_shift_of_disjoint α β ρ hLaplace η ζ
    (fun x ↦ (hη x).1) (fun x ↦ (hζ x).1) ((n : ℝ) • v) hn
  have hcomp := hind.comp (measurable_legalInputRestrictionLocal hU.measurableSet)
    (measurable_legalInputRestrictionLocal hV.measurableSet)
  have hηeq (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) :
      legalInputRestrictionLocal U (legalInputCutoffLocal η.toContinuousMap μ) =
        legalInputRestrictionLocal U μ := by
    apply Subtype.ext
    exact restrict_legalInputCutoffLocal_eq η.toContinuousMap hU.measurableSet hηU μ
  have hζeq (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) :
      legalInputRestrictionLocal V (legalInputCutoffLocal ζ.toContinuousMap μ) =
        legalInputRestrictionLocal V μ := by
    apply Subtype.ext
    exact restrict_legalInputCutoffLocal_eq ζ.toContinuousMap hV.measurableSet hζV μ
  simpa only [Function.comp_def, hηeq, hζeq] using hcomp

end OTSelector.Reconstruction
