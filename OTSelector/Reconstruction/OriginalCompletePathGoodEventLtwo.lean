import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell
import Mathlib.MeasureTheory.Function.L2Space

/-! Good-event complete-path traffic squares are estimated by the actual original
Campbell/Tonelli occupation. All random variables belong to the same scene law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- An actual nonnegative integrable scene majorant gives the good-event square
bound. The event may depend on the entire original scene and on the traffic. -/
theorem goodEvent_memLp_two_of_integrable_majorant
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T U : Ω → ℝ} (hT : AEStronglyMeasurable T P)
    {A : Set Ω} (hA : MeasurableSet A) {C : ℝ} (hC : 0 ≤ C)
    (hU : Integrable U P) (hU0 : ∀ᵐ s ∂P, 0 ≤ U s)
    (hpoint : ∀ᵐ s ∂P, s ∉ A → T s ^ 2 ≤ C * U s) :
    MemLp (Aᶜ.indicator T) 2 P ∧
      (∫ s, (Aᶜ.indicator T s) ^ 2 ∂P) ≤ C * ∫ s, U s ∂P := by
  have hmeas := (hT.indicator hA.compl).pow 2
  have hdom : ∀ᵐ s ∂P, (Aᶜ.indicator T s) ^ 2 ≤ C * U s := by
    filter_upwards [hU0, hpoint] with s hs0 hs
    by_cases hsA : s ∈ A
    · simp only [Set.indicator_of_notMem (show s ∉ Aᶜ from fun h ↦ h hsA), zero_pow (by norm_num : 2 ≠ 0)]
      exact mul_nonneg hC hs0
    · simpa only [Set.indicator_of_mem (show s ∈ Aᶜ from hsA)] using hs hsA
  have hi : Integrable (fun s ↦ (Aᶜ.indicator T s) ^ 2) P := by
    apply (hU.const_mul C).mono' hmeas
    filter_upwards [hdom] with s hs
    change ‖(Aᶜ.indicator T s) ^ 2‖ ≤ C * U s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hs
  refine ⟨(memLp_two_iff_integrable_sq (hT.indicator hA.compl)).mpr hi, ?_⟩
  calc
    _ ≤ ∫ s, C * U s ∂P := integral_mono_ae hi (hU.const_mul C) hdom
    _ = _ := integral_const_mul _ _

/-- Actual original complete-path occupation controls a good-event traffic square
by its true original Palm occupation integral. The Campbell identity removes
spatial anchoring and all mark-dependent translations without independence. -/
theorem LegalWeightedStationaryPoissonMatching.goodEvent_completePath_traffic_memLp_two
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (hfinite : (∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
      (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q M.law) ≠ ∞)
    {T : LegalMarkedOptimalInputScene q → ℝ}
    (hT : AEStronglyMeasurable T (M.law : Measure (LegalMarkedOptimalInputScene q)))
    {A : Set (LegalMarkedOptimalInputScene q)} (hA : MeasurableSet A)
    {C : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), s ∉ A →
      T s ^ 2 ≤ C * (legalMarkedCompletePathTraffic q d h f s).toReal) :
    MemLp (Aᶜ.indicator T) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, (Aᶜ.indicator T s) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ C *
        ((∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
          (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q M.law)).toReal := by
  have hm := measurable_legalMarkedCompletePathTraffic d hd hh hf
  have hmean : (∫⁻ s, legalMarkedCompletePathTraffic q d h f s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≠ ∞ := by
    rwa [M.lintegral_completePathTraffic d hd hh hf]
  have hI := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hmean
  have heq : (∫ s, (legalMarkedCompletePathTraffic q d h f s).toReal
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ((∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume ∂legalMarkedJointPalm q M.law)).toReal := by
    rw [integral_toReal hm.aemeasurable (ae_lt_top hm hmean),
      M.lintegral_completePathTraffic d hd hh hf]
  obtain ⟨hL2, hbound⟩ := goodEvent_memLp_two_of_integrable_majorant hT hA hC hI
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hpoint
  exact ⟨hL2, by rwa [heq] at hbound⟩

end OTSelector.Reconstruction
