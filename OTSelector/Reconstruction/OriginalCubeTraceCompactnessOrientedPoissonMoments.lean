import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedInputHminus
import OTSelector.Analysis.Calculus.OrthonormalCubeEnergy

/-! Original Poisson moments of the actual reflected response in a fixed physical frame. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- The physical-to-frame coordinate readout retains the original real mark. -/
def originalOrientedInputCoordinates
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    LegalMarkedPhysicalPoint q ≃ᵐ LegalMarkedPhysicalPoint q :=
  (orthonormalPhysicalCubeMap b).symm.toHomeomorph.toMeasurableEquiv.prodCongr
    (MeasurableEquiv.refl ℝ)

/-- The actual frame readout preserves the full original Haar-times-mark intensity. -/
theorem measurePreserving_originalOrientedInputCoordinates
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (γ : Measure ℝ) [IsFiniteMeasure γ] :
    MeasurePreserving (originalOrientedInputCoordinates b) (volume.prod γ) (volume.prod γ) := by
  have hO : MeasurePreserving (orthonormalPhysicalCubeMap b).symm :=
    MeasurePreserving.symm (orthonormalPhysicalCubeMap b).toHomeomorph.toMeasurableEquiv
      (measurePreserving_orthonormalPhysicalCubeMap b)
  exact hO.prod (MeasurePreserving.id γ)

/-- The unchanged original physical input is read in the chosen cube frame. -/
def originalOrientedClassReflectedHilbertResponse (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) (C : Set ℝ) (p : LegalMarkedPhysicalPoint q) :
    originalGradientClosure (originalMeanZeroGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R))) :=
  originalClassReflectedInputHilbertResponse K hη hηsupport R C
    (originalOrientedInputCoordinates b p)

/-- The actual oriented response is strongly measurable in the original physical input. -/
theorem stronglyMeasurable_originalOrientedClassReflectedHilbertResponse
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C) :
    StronglyMeasurable (originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C) := by
  have hs := stronglyMeasurable_originalClassReflectedInputHilbertResponse K hη hηsupport R hC
  exact hs.comp_measurable (originalOrientedInputCoordinates b).measurable

/-- The true oriented response vanishes outside the actual rotated compact input window. -/
theorem originalOrientedClassReflectedHilbertResponse_eq_zero_off_outer
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    (C : Set ℝ) (p : LegalMarkedPhysicalPoint q)
    (hp : p.1 ∉ orthonormalPhysicalCubeMap b '' haarRootCube (Fin q) (R + 1)) :
    originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C p = 0 := by
  apply originalClassReflectedInputHilbertResponse_eq_zero_off_shell_or_class K hη hηsupport
    hR C (originalOrientedInputCoordinates b p)
  left
  intro hs
  exact hp ⟨(orthonormalPhysicalCubeMap b).symm p.1, hs.1,
    (orthonormalPhysicalCubeMap b).apply_symm_apply p.1⟩

/-- Haar preservation gives the same exact zero mean in the original physical frame. -/
theorem integral_originalOrientedClassReflectedHilbertResponse_eq_zero
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) (hηone : ∫ v, η v = 1)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) (γ : Measure ℝ) [IsFiniteMeasure γ]
    {C : Set ℝ} (hC : MeasurableSet C) :
    (∫ p, originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C p
      ∂volume.prod γ) = 0 := by
  rw [show (∫ p, originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C p
      ∂volume.prod γ) = ∫ p, originalClassReflectedInputHilbertResponse K hη hηsupport R C p
      ∂volume.prod γ from
    (measurePreserving_originalOrientedInputCoordinates b γ).integral_comp' _]
  exact integral_originalClassReflectedInputHilbertResponse_eq_zero K hη hηsupport hM hηM
    hηone hηeven hR γ hC

/-- The actual original oriented input retains the true surface-order response intensity. -/
theorem integral_sq_originalOrientedClassReflectedHilbertResponse_le_surface
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (γ : Measure ℝ) [IsFiniteMeasure γ] {C : Set ℝ} (hC : MeasurableSet C) :
    (∫ p, ‖originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C p‖^2
      ∂volume.prod γ) ≤ cubeReflectedResponseSobolevConstant q M ^ 2 *
        (4 * (q : ℝ) * 4^(q-1)) * R^(q-1) * γ.real C := by
  rw [show (∫ p, ‖originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C p‖^2
      ∂volume.prod γ) = ∫ p, ‖originalClassReflectedInputHilbertResponse K hη hηsupport R C p‖^2
      ∂volume.prod γ from
    (measurePreserving_originalOrientedInputCoordinates b γ).integral_comp'
      (fun p ↦ ‖originalClassReflectedInputHilbertResponse K hη hηsupport R C p‖^2)]
  exact integral_sq_originalClassReflectedInputHilbertResponse_le_surface K hq hη hηsupport
    hM hηM hR γ hC

/-- The actual oriented Hilbert integral uses the original unchanged matching scene. -/
def originalOrientedReflectedInputHilbertIntegral (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) (C : Set ℝ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q) :
    originalGradientClosure (originalMeanZeroGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R))) :=
  ∫ p, originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C p
    ∂legalInputColorMeasure q s.2 c

/-- The actual same-scene oriented integral is strongly measurable. -/
theorem stronglyMeasurable_originalOrientedReflectedInputHilbertIntegral
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    StronglyMeasurable (originalOrientedReflectedInputHilbertIntegral K b hη hηsupport R C c) := by
  have hs := stronglyMeasurable_originalOrientedClassReflectedHilbertResponse K b hη hηsupport R hC
  have h := hs.integral_kernel (κ := legalMarkedInputColorKernel q c)
  simp only [legalMarkedInputColorKernel_apply] at h
  convert h using 1 <;> rfl

/-- No rotated matching law is needed for original Poisson moments in a fixed physical frame. -/
theorem LegalWeightedStationaryPoissonMatching.original_orientedInput_reflectedHilbert_moments
    {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g)
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) (hηone : ∫ v, η v = 1)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    let γ := if c = 0 then α else β
    let I := originalOrientedReflectedInputHilbertIntegral K b hη hηsupport R C c
    (∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C)
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
  have : SecondCountableTopology H := by dsimp only [H, originalGradientClosure]; infer_instance
  let F : LegalMarkedPhysicalPoint q → H :=
    originalOrientedClassReflectedHilbertResponse K b hη hηsupport R C
  let γ : Measure ℝ := if c = 0 then α else β
  have : IsProbabilityMeasure γ := by
    by_cases hc : c = 0 <;> simp only [γ, hc, ↓reduceIte] <;> infer_instance
  obtain ⟨w, hw, e, _⟩ := exists_countable_hilbertBasis_originalMeanZeroGradientClosure K R
  have : Countable w := hw.to_subtype
  have hF : Measurable F :=
    (stronglyMeasurable_originalOrientedClassReflectedHilbertResponse K b hη hηsupport R hC).measurable
  have hs := originalOrientedClassReflectedHilbertResponse_eq_zero_off_outer K b hη hηsupport hR C
  have hbnd : ∀ p, ‖F p‖ ≤ cubeReflectedResponseSobolevConstant q M := fun p ↦
    norm_originalClassReflectedInputHilbertResponse_le K hq hη hηsupport hM hηM hR C _
  have hm : (∫ p, F p ∂(volume : Measure (Fin q → ℝ)).prod γ) = 0 :=
    integral_originalOrientedClassReflectedHilbertResponse_eq_zero K b hη hηsupport hM hηM
      hηone hηeven hR γ hC
  have h := P.centered_fullInput_hilbert_moments e
    (isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous) hF hs
    (cubeReflectedResponseSobolevConstant_nonneg q hM) hbnd c
  dsimp only at h
  rcases h with ⟨hi, hLp, hmean, hvar⟩
  dsimp only [γ] at hm
  rw [hm] at hLp hvar
  simp only [sub_zero] at hLp hvar
  refine ⟨hi, hLp, hmean.trans hm, ?_⟩
  exact hvar.trans_le (integral_sq_originalOrientedClassReflectedHilbertResponse_le_surface K b
    hq hη hηsupport hM hηM hR γ hC)

end OTSelector.Reconstruction
