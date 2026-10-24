import OTSelector.Reconstruction.OriginalCubeTraceCompactnessOrientedInputHminus
import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice

/-! The actual normalized smooth radial kernel produces physical reflected-input dual control. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual original-input squared dual bound uses the fixed normalized radial mollifier. -/
def originalCanonicalOrientedReflectedInputDualBound {q : ℕ} (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (L : ℝ) (C : Set ℝ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  originalOrientedReflectedInputDualBound K b (contDiff_originalEuclideanMollifier q).continuous
    (originalEuclideanMollifier_unit_range q) L C c s

/-- A concrete nonnegative smooth normalized Euclidean-radial kernel, the original full-input
Poisson law, and the same chosen physical cube yield a genuine common reflected-input bound.
Every kernel property and the uniform amplitude are produced internally. -/
theorem LegalWeightedStationaryPoissonMatching.original_canonicalOrientedInput_Hminus_moments
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g)
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hq : 2 < q) {L : ℝ} (hL : 2 ≤ L) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    let γ := if c = 0 then α else β
    let B := originalCanonicalOrientedReflectedInputDualBound K b L C c
    Measurable B ∧ (∀ s, 0 ≤ B s) ∧
    Integrable B (P.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, B s ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      cubeReflectedResponseSobolevConstant q (originalEuclideanMollifierBound q)^2 *
        (4 * (q : ℝ) * 4^(q-1)) * (L / 2)^(q-1) * γ.real C ∧
    ∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (originalOrientedClassReflectedInputScalarField b
        (originalEuclideanMollifier q) L C (legalInputColorMeasure q s.2 c))
          (volume.restrict (originalCenteredPhysicalCubeRegion b L)) ∧
      ∀ φ : 𝓓_{K}(Fin q → ℝ, ℝ),
        (∫ z in originalCenteredPhysicalCubeRegion b L, φ z) = 0 →
        |∫ z in originalCenteredPhysicalCubeRegion b L,
          originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier q) L C
            (legalInputColorMeasure q s.2 c) z * φ z|^2 ≤
          B s * ∑ k : Fin q, ∫ z in originalCenteredPhysicalCubeRegion b L,
            (fderiv ℝ φ z (Pi.single k 1))^2 := by
  exact P.original_orientedInput_reflected_Hminus_moments K b hq
    (contDiff_originalEuclideanMollifier q).continuous
    (originalEuclideanMollifier_unit_range q) (originalEuclideanMollifier_radial q)
    (originalEuclideanMollifierBound_nonneg q) (abs_originalEuclideanMollifier_le q)
    (integral_originalEuclideanMollifier_eq_one q) hL hC c

end OTSelector.Reconstruction
