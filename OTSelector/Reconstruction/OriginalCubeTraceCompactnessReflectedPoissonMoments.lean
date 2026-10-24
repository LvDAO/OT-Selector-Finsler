import OTSelector.Reconstruction.OriginalCubeReflectedHilbertIntensity
import OTSelector.Reconstruction.OriginalPoissonHilbertInputMomentsActual
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! The actual original full-input reflected Hilbert error has surface-order second moment. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- The unchanged original color input integrated against the literal class-marked reflected
Hilbert response, preserving all actual input marks and the same scene. -/
def originalReflectedInputHilbertPoissonIntegral (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) (C : Set ℝ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q) :
    originalGradientClosure (originalMeanZeroGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R))) :=
  ∫ p, originalClassReflectedInputHilbertResponse K hη hηsupport R C p
    ∂legalInputColorMeasure q s.2 c

/-- The actual original full-input reflected Hilbert random variable is strongly measurable. -/
theorem stronglyMeasurable_originalReflectedInputHilbertPoissonIntegral
    (K : Compacts (Fin q → ℝ)) (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) {C : Set ℝ}
    (hC : MeasurableSet C) (c : Fin 2) :
    StronglyMeasurable (originalReflectedInputHilbertPoissonIntegral K hη hηsupport R C c) := by
  have hs := stronglyMeasurable_originalClassReflectedInputHilbertResponse K hη hηsupport R hC
  have h := hs.integral_kernel (κ := legalMarkedInputColorKernel q c)
  simp only [legalMarkedInputColorKernel_apply] at h
  convert h using 1 <;> rfl

/-- Actual coordinate reflection, genuine cube Sobolev-Poincare and the full same-scene
Hilbert Poisson law prove the reflected error's true surface-order second moment. The
response mean is zero for each original color separately; no rate or variance is an input. -/
theorem LegalWeightedStationaryPoissonMatching.original_fullInput_reflectedHilbert_moments
    {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g)
    (K : Compacts (Fin q → ℝ)) (hq : 2 < q) (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ v, |η v| ≤ M) (hηone : ∫ v, η v = 1)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2)
    {N : Type*} [Countable N]
    (b : HilbertBasis N ℝ (originalGradientClosure (originalMeanZeroGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R))))) :
    let γ := if c = 0 then α else β
    let I := originalReflectedInputHilbertPoissonIntegral K hη hηsupport R C c
    (∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (originalClassReflectedInputHilbertResponse K hη hηsupport R C)
        (legalInputColorMeasure q s.2 c)) ∧
    MemLp I 2 (P.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, I s ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) = 0 ∧
    (∫ s, ‖I s‖^2 ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      cubeReflectedResponseSobolevConstant q M ^ 2 *
        (4 * (q : ℝ) * 4^(q-1)) * R^(q-1) * γ.real C := by
  let H := originalGradientClosure (originalMeanZeroGradientLtwo K
    (volume.restrict (haarRootCube (Fin q) R)))
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology H := by
    dsimp only [H, originalGradientClosure]
    infer_instance
  let F : LegalMarkedPhysicalPoint q → H :=
    originalClassReflectedInputHilbertResponse K hη hηsupport R C
  let γ : Measure ℝ := if c = 0 then α else β
  have : IsProbabilityMeasure γ := by
    by_cases hc : c = 0 <;> simp only [γ, hc, ↓reduceIte] <;> infer_instance
  have hF : Measurable F :=
    (stronglyMeasurable_originalClassReflectedInputHilbertResponse K hη hηsupport R hC).measurable
  have hs : ∀ p : LegalMarkedPhysicalPoint q,
      p.1 ∉ haarRootCube (Fin q) (R + 1) → F p = 0 := by
    intro p hp
    exact originalClassReflectedInputHilbertResponse_eq_zero_off_shell_or_class K hη hηsupport
      hR C p (Or.inl (fun hx ↦ hp hx.1))
  have hbnd : ∀ p : LegalMarkedPhysicalPoint q, ‖F p‖ ≤ cubeReflectedResponseSobolevConstant q M :=
    norm_originalClassReflectedInputHilbertResponse_le K hq hη hηsupport hM hηM hR C
  have hm : (∫ p, F p ∂(volume : Measure (Fin q → ℝ)).prod γ) = 0 :=
    integral_originalClassReflectedInputHilbertResponse_eq_zero K hη hηsupport hM hηM
      hηone hηeven hR γ hC
  have h := P.centered_fullInput_hilbert_moments b (K := haarRootCube (Fin q) (R + 1))
    isCompact_Icc hF hs (cubeReflectedResponseSobolevConstant_nonneg q hM) hbnd c
  dsimp only at h
  rcases h with ⟨hi, hLp, hmean, hvar⟩
  change (∫ p, F p ∂(volume : Measure (Fin q → ℝ)).prod γ) = 0 at hm
  dsimp only [γ] at hm
  rw [hm] at hLp hvar
  simp only [sub_zero] at hLp hvar
  have hmean0 := hmean.trans hm
  refine ⟨hi, hLp, hmean0, ?_⟩
  exact hvar.trans_le (integral_sq_originalClassReflectedInputHilbertResponse_le_surface K hq
    hη hηsupport hM hηM hR γ hC)

end OTSelector.Reconstruction
