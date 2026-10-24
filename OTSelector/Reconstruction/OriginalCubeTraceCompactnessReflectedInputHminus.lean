import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedPoissonDual
import OTSelector.Reconstruction.OriginalCubeGradientCountableHilbertBasis

/-! Genuine reflected-input negative Sobolev control on the unchanged original input scene. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- The original reflected input error admits a common measurable squared negative-Sobolev
bound with true surface-order expectation. The literal full-input field is integrable and
one full-measure scene set controls all original smooth mean-zero tests by their actual
coordinate derivative energy. Reflection, Sobolev control, the canonical Hilbert response,
countable-basis existence, original Poisson moments and literal Fubini are all proved inputs
within the library, rather than extra assumptions of this theorem. -/
theorem LegalWeightedStationaryPoissonMatching.original_fullInput_reflected_Hminus_moments
    {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g)
    (K : Compacts (Fin q → ℝ)) (hq : 2 < q) (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ v, |η v| ≤ M) (hηone : ∫ v, η v = 1)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    let γ := if c = 0 then α else β
    let B := originalReflectedInputDualBound K hη hηsupport R C c
    Measurable B ∧ (∀ s, 0 ≤ B s) ∧
    Integrable B (P.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, B s ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      cubeReflectedResponseSobolevConstant q M ^ 2 *
        (4 * (q : ℝ) * 4^(q-1)) * R^(q-1) * γ.real C ∧
    ∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (originalClassReflectedInputScalarField η R C
        (legalInputColorMeasure q s.2 c)) (volume.restrict (haarRootCube (Fin q) R)) ∧
      ∀ φ : 𝓓_{K}(Fin q → ℝ, ℝ), (∫ z in haarRootCube (Fin q) R, φ z) = 0 →
        |∫ z in haarRootCube (Fin q) R,
          originalClassReflectedInputScalarField η R C (legalInputColorMeasure q s.2 c) z *
            φ z|^2 ≤ B s * ∑ k : Fin q, ∫ z in haarRootCube (Fin q) R,
              (fderiv ℝ φ z (Pi.single k 1))^2 := by
  obtain ⟨w, hw, b, _⟩ := exists_countable_hilbertBasis_originalMeanZeroGradientClosure K R
  have : Countable w := hw.to_subtype
  obtain ⟨hB, hBnonneg, hBi, hBE, hbound⟩ :=
    P.original_fullInput_reflected_dual_bound K hq hη hηsupport hM hηM hηone hηeven hR hC c b
  refine ⟨hB, hBnonneg, hBi, hBE, ?_⟩
  filter_upwards [hbound, P.ae_finite_reflectedInputOuterWindow R c] with s hs hfin
  refine ⟨?_, ?_⟩
  · simpa only [mul_one] using
      (integrable_originalClassReflectedInputScalarField_mul_of_finite_outer hη.measurable hM
        hηM hηsupport hR hC (legalInputColorMeasure q s.2 c) hfin
        (u := fun _ ↦ (1 : ℝ)) continuous_const)
  · intro φ hm
    let φ₀ : originalMeanZeroSmoothTests K (volume.restrict (haarRootCube (Fin q) R)) :=
      ⟨φ, by change (∫ z in haarRootCube (Fin q) R, φ z) = 0; exact hm⟩
    have h := hs φ₀
    rw [originalHaarRootCubeGradientLtwo_norm_sq K R] at h
    exact h

end OTSelector.Reconstruction
