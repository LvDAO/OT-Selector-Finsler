import OTSelector.Reconstruction.OriginalCubeTraceCompactnessCanonicalOrientedInputHminus
import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessPhysicalGradientBound

/-! Both literal full-input errors retain the same actual physical cube and canonical kernel. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual source-side canonical Hilbert response bound, with source half slab [s,t). -/
def originalStageOrientedSourceReflectedInputBound {q : ℕ} (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (R s t : ℝ) : LegalMarkedOptimalInputScene q → ℝ :=
  originalCanonicalOrientedReflectedInputDualBound K b (2*R) (Ico s t) 0

/-- The actual target-side canonical Hilbert response bound, with target half slab (s,t]. -/
def originalStageOrientedTargetReflectedInputBound {q : ℕ} (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (R s t : ℝ) : LegalMarkedOptimalInputScene q → ℝ :=
  originalCanonicalOrientedReflectedInputDualBound K b (2*R) (Ioc s t) 1

/-- Both actual full-input reflected errors have one common full-measure event for all
mean-zero smooth tests, genuine integrable bounds, and a proved surface-order total mean. -/
theorem LegalWeightedStationaryPoissonMatching.originalStageOriented_reflectedInput_bounds
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (hq : 2 < q) {R : ℝ} (hR : 1 ≤ R) (s t : ℝ) :
    let Bs := originalStageOrientedSourceReflectedInputBound K b R s t
    let Bt := originalStageOrientedTargetReflectedInputBound K b R s t
    Measurable Bs ∧ Measurable Bt ∧ (∀ scene, 0 ≤ Bs scene ∧ 0 ≤ Bt scene) ∧
    Integrable Bs (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    Integrable Bt (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ scene, Bs scene + Bt scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      cubeReflectedResponseSobolevConstant q (originalEuclideanMollifierBound q)^2 *
        (4*(q:ℝ)*4^(q-1)) * R^(q-1) * (μ.real (Ico s t) + ν.real (Ioc s t)) ∧
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ φ : 𝓓_{K}(Fin q → ℝ, ℝ), (∫ z in originalCenteredPhysicalCubeRegion b (2*R), φ z) = 0 →
      ((∫ z in originalCenteredPhysicalCubeRegion b (2*R),
        originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier q) (2*R) (Ico s t)
          (legalInputColorMeasure q scene.2 0) z * φ z)^2 ≤
        Bs scene * ‖smoothPhysicalGradientLtwo K (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) φ‖^2) ∧
      ((∫ z in originalCenteredPhysicalCubeRegion b (2*R),
        originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier q) (2*R) (Ioc s t)
          (legalInputColorMeasure q scene.2 1) z * φ z)^2 ≤
        Bt scene * ‖smoothPhysicalGradientLtwo K (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) φ‖^2) := by
  have hs := Q.original_canonicalOrientedInput_Hminus_moments (C := Ico s t) K b hq
    (show 2 ≤ 2*R by linarith) measurableSet_Ico (0 : Fin 2)
  have ht := Q.original_canonicalOrientedInput_Hminus_moments (C := Ioc s t) K b hq
    (show 2 ≤ 2*R by linarith) measurableSet_Ioc (1 : Fin 2)
  have hhalf : (2*R)/2 = R := by ring
  simp only [hhalf] at hs ht
  dsimp only at hs ht ⊢
  refine ⟨hs.1, ht.1, fun scene ↦ ⟨hs.2.1 scene, ht.2.1 scene⟩,
    hs.2.2.1, ht.2.2.1, ?_, ?_⟩
  · unfold originalStageOrientedSourceReflectedInputBound originalStageOrientedTargetReflectedInputBound
    rw [integral_add hs.2.2.1 ht.2.2.1, mul_add]
    exact add_le_add (by simpa only [↓reduceIte] using hs.2.2.2.1)
      (by simpa using ht.2.2.2.1)
  · filter_upwards [hs.2.2.2.2, ht.2.2.2.2] with scene hsceneS hsceneT
    intro φ hm
    have hS := hsceneS.2 φ hm
    have hT := hsceneT.2 φ hm
    rw [sq_abs, originalCenteredPhysicalCubeGradientEnergy_eq_smoothPhysicalGradientLtwo_norm_sq b (2*R) K φ] at hS hT
    exact ⟨hS, hT⟩

end OTSelector.Reconstruction
