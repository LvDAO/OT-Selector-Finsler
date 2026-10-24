import OTSelector.Reconstruction.OriginalCubeTraceCompactnessOrientedPoissonMoments
import OTSelector.Reconstruction.OriginalOrientedCubeReflectedFubini

/-! Literal original reflected-input dual control on the same selected physical cube. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- One measurable physical-cube random dominator from the unchanged actual original input. -/
def originalOrientedReflectedInputDualBound (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0)
    (L : ℝ) (C : Set ℝ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ‖originalOrientedReflectedInputHilbertIntegral (originalOrientedCubeTestSupport b K) b hη
    (raw_unit_range_of_euclidean_unit_range hηsupport) (L / 2) C c s‖^2

/-- The oriented original-input bound is genuinely measurable on the original scene law. -/
theorem measurable_originalOrientedReflectedInputDualBound (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0)
    (L : ℝ) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    Measurable (originalOrientedReflectedInputDualBound K b hη hηsupport L C c) := by
  exact ((stronglyMeasurable_originalOrientedReflectedInputHilbertIntegral
    (originalOrientedCubeTestSupport b K) b hη
    (raw_unit_range_of_euclidean_unit_range hηsupport) (L / 2) hC c).norm.measurable).pow_const 2

/-- The literal physical reflected response is realized by the actual oriented Hilbert
integral on the same selected cube, retaining the original physical test and derivative energy. -/
theorem originalOrientedReflectedInputDualBound_controls_pairing
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0)
    (hηradial : IsOriginalEuclideanRadial η) {L : ℝ} (hL : 2 ≤ L)
    (C : Set ℝ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q)
    (hi : Integrable (originalOrientedClassReflectedHilbertResponse
      (originalOrientedCubeTestSupport b K) b hη
      (raw_unit_range_of_euclidean_unit_range hηsupport) (L / 2) C)
      (legalInputColorMeasure q s.2 c))
    (φ : 𝓓_{K}(Fin q → ℝ, ℝ))
    (hm : (∫ z in originalCenteredPhysicalCubeRegion b L, φ z) = 0) :
    |∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
      (∫ z in originalCenteredPhysicalCubeRegion b L,
        originalOrientedCubeReflectedInputResponse b η L z p.1 * φ z)
      ∂legalInputColorMeasure q s.2 c|^2 ≤
      originalOrientedReflectedInputDualBound K b hη hηsupport L C c s *
        ∑ k : Fin q, ∫ z in originalCenteredPhysicalCubeRegion b L,
          (fderiv ℝ φ z (Pi.single k 1))^2 := by
  let K₀ := originalOrientedCubeTestSupport b K
  let hs := raw_unit_range_of_euclidean_unit_range hηsupport
  let ψ : originalMeanZeroSmoothTests K₀ (volume.restrict (haarRootCube (Fin q) (L / 2))) :=
    ⟨originalOrientedCubeTestPullback b φ,
      originalOrientedCubeTestPullback_mean_zero b L φ hm⟩
  let d := originalDenseGradient (originalMeanZeroGradientLtwo K₀
    (volume.restrict (haarRootCube (Fin q) (L / 2)))) ψ
  let I := originalOrientedReflectedInputHilbertIntegral K₀ b hη hs (L / 2) C c s
  have he : (∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
      (∫ z in originalCenteredPhysicalCubeRegion b L,
        originalOrientedCubeReflectedInputResponse b η L z p.1 * φ z)
      ∂legalInputColorMeasure q s.2 c) = ⟪d, I⟫_ℝ := by
    dsimp only [I, originalOrientedReflectedInputHilbertIntegral]
    rw [← integral_inner hi]
    apply integral_congr_ae
    exact ae_of_all _ (fun p ↦ by
      dsimp only
      rw [real_inner_comm, originalOrientedClassReflectedHilbertResponse,
        originalClassReflectedInputHilbertResponse, real_inner_smul_left,
        inner_originalReflectedInputHilbertResponse_gradient K₀ hη hs
          (show 1 ≤ L / 2 by linarith) _ ψ,
        integral_orientedCube_reflected_response_mul b hηradial L p.1]
      rfl)
  have hd : ‖d‖^2 = ∑ k : Fin q, ∫ z in originalCenteredPhysicalCubeRegion b L,
      (fderiv ℝ φ z (Pi.single k 1))^2 := by
    change ‖smoothPhysicalGradientLtwo K₀
      (volume.restrict (haarRootCube (Fin q) (L / 2))) (originalOrientedCubeTestPullback b φ)‖^2 = _
    rw [originalHaarRootCubeGradientLtwo_norm_sq,
      originalOrientedCubeTestPullback_gradient_energy b L φ]
  rw [he]
  calc
    |⟪d, I⟫_ℝ|^2 ≤ (‖d‖ * ‖I‖)^2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm d I) 2
    _ = _ := by
      rw [mul_pow, hd]
      dsimp only [originalOrientedReflectedInputDualBound, I, K₀, hs]
      ring

/-- The actual full original color input has finite mass on the rotated expanded window. -/
theorem LegalWeightedStationaryPoissonMatching.ae_finite_orientedReflectedInputOuterWindow
    {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (L : ℝ) (c : Fin 2) :
    ∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      legalInputColorMeasure q s.2 c
        (originalCenteredPhysicalCubeRegion b (L + 2) ×ˢ univ) < ∞ := by
  let A := originalCenteredPhysicalCubeRegion b (L + 2)
  have hA : IsCompact A := isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous
  let W : Set (LegalMarkedPhysicalPoint q) := A ×ˢ univ
  have hW : MeasurableSet W := hA.measurableSet.prod MeasurableSet.univ
  filter_upwards [P.ae_finite_fullSpatialInput hA] with s hs
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hW,
    Measure.restrict_apply (hW.preimage measurable_fst)]
  exact lt_of_le_of_lt (measure_mono (by
    intro p hp
    exact ⟨hp.1, mem_univ _⟩)) hs


/-- The literal reflected full-input error has a genuine surface-order common dual bound
on the same selected physical cube, without changing the original matching law or eta. -/
theorem LegalWeightedStationaryPoissonMatching.original_orientedInput_reflected_Hminus_moments
    {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g)
    (K : Compacts (Fin q → ℝ))
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (hq : 2 < q) (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ → η v = 0)
    (hηradial : IsOriginalEuclideanRadial η)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) (hηone : ∫ v, η v = 1)
    {L : ℝ} (hL : 2 ≤ L) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    let γ := if c = 0 then α else β
    let B := originalOrientedReflectedInputDualBound K b hη hηsupport L C c
    Measurable B ∧ (∀ s, 0 ≤ B s) ∧
    Integrable B (P.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, B s ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      cubeReflectedResponseSobolevConstant q M ^ 2 *
        (4 * (q : ℝ) * 4^(q-1)) * (L / 2)^(q-1) * γ.real C ∧
    ∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (originalOrientedClassReflectedInputScalarField b η L C
        (legalInputColorMeasure q s.2 c))
          (volume.restrict (originalCenteredPhysicalCubeRegion b L)) ∧
      ∀ φ : 𝓓_{K}(Fin q → ℝ, ℝ),
        (∫ z in originalCenteredPhysicalCubeRegion b L, φ z) = 0 →
        |∫ z in originalCenteredPhysicalCubeRegion b L,
          originalOrientedClassReflectedInputScalarField b η L C
            (legalInputColorMeasure q s.2 c) z * φ z|^2 ≤
          B s * ∑ k : Fin q, ∫ z in originalCenteredPhysicalCubeRegion b L,
            (fderiv ℝ φ z (Pi.single k 1))^2 := by
  let hs := raw_unit_range_of_euclidean_unit_range hηsupport
  obtain ⟨hi, hLp, _, hsecond⟩ := P.original_orientedInput_reflectedHilbert_moments
    (originalOrientedCubeTestSupport b K) b hq hη hs hM hηM hηone
    (coordinate_even_of_euclideanRadial hηradial) (show 1 ≤ L / 2 by linarith) hC c
  refine ⟨measurable_originalOrientedReflectedInputDualBound K b hη hηsupport L hC c,
    fun _ ↦ sq_nonneg _, hLp.integrable_norm_pow' (p := 2), hsecond, ?_⟩
  filter_upwards [hi, P.ae_finite_orientedReflectedInputOuterWindow b L c] with s hsi hfin
  refine ⟨?_, ?_⟩
  · simpa only [mul_one] using
      (integrable_originalOrientedClassReflectedInputScalarField_mul b hη.measurable hηradial
        hM hηM hηsupport hL hC (legalInputColorMeasure q s.2 c) hfin
        (u := fun _ ↦ (1 : ℝ)) continuous_const)
  · intro φ hm
    rw [integral_originalOrientedClassReflectedInputScalarField_mul_eq b hη.measurable hηradial
      hM hηM hηsupport hL hC (legalInputColorMeasure q s.2 c) hfin φ.continuous]
    exact originalOrientedReflectedInputDualBound_controls_pairing K b hη hηsupport hηradial
      hL C c s hsi φ hm

end OTSelector.Reconstruction
