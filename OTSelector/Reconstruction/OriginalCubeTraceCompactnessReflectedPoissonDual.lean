import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedPoissonMoments
import OTSelector.Reconstruction.OriginalCubeReflectedInputFubini

/-! A common measurable dominator for all actual mean-zero reflected-input smooth tests. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- The squared norm of the actual same-scene reflected-input Hilbert integral. -/
def originalReflectedInputDualBound (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) (C : Set ℝ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ‖originalReflectedInputHilbertPoissonIntegral K hη hηsupport R C c s‖^2

/-- The actual random dominator is measurable, without selecting a test function. -/
theorem measurable_originalReflectedInputDualBound (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    Measurable (originalReflectedInputDualBound K hη hηsupport R C c) := by
  exact ((stronglyMeasurable_originalReflectedInputHilbertPoissonIntegral K hη hηsupport R
    hC c).norm.measurable).pow_const 2

/-- The actual canonical Hilbert integral controls every literal scalar response pairing. -/
theorem originalReflectedInputDualBound_controls_double_integral
    (K : Compacts (Fin q → ℝ)) (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    (C : Set ℝ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q)
    (hi : Integrable (originalClassReflectedInputHilbertResponse K hη hηsupport R C)
      (legalInputColorMeasure q s.2 c))
    (φ : originalMeanZeroSmoothTests K (volume.restrict (haarRootCube (Fin q) R))) :
    |∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
      (∫ z in haarRootCube (Fin q) R,
        originalCubeReflectedInputResponse η R z p.1 * (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z)
      ∂legalInputColorMeasure q s.2 c|^2 ≤
    originalReflectedInputDualBound K hη hηsupport R C c s *
      ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube (Fin q) R))
        (φ : 𝓓_{K}(Fin q → ℝ, ℝ))‖^2 := by
  let d := originalDenseGradient (originalMeanZeroGradientLtwo K
    (volume.restrict (haarRootCube (Fin q) R))) φ
  let I := originalReflectedInputHilbertPoissonIntegral K hη hηsupport R C c s
  have he : (∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
      (∫ z in haarRootCube (Fin q) R,
        originalCubeReflectedInputResponse η R z p.1 * (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z)
      ∂legalInputColorMeasure q s.2 c) = ⟪d, I⟫_ℝ := by
    dsimp only [I, originalReflectedInputHilbertPoissonIntegral]
    rw [← integral_inner hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p ↦ by
      dsimp only
      rw [real_inner_comm, originalClassReflectedInputHilbertResponse, real_inner_smul_left,
        inner_originalReflectedInputHilbertResponse_gradient K hη hηsupport hR p.1 φ])
  rw [he]
  have hd : ‖d‖ = ‖smoothPhysicalGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ))‖ := rfl
  calc
    |⟪d, I⟫_ℝ|^2 ≤ (‖d‖ * ‖I‖)^2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm d I) 2
    _ = _ := by
      rw [mul_pow, hd]
      dsimp only [originalReflectedInputDualBound, I]
      ring

/-- The full actual color input is finite on every compact spatial observation window. -/
theorem LegalWeightedStationaryPoissonMatching.ae_finite_reflectedInputOuterWindow
    {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g) (R : ℝ) (c : Fin 2) :
    ∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      legalInputColorMeasure q s.2 c (haarRootCube (Fin q) (R + 1) ×ˢ univ) < ∞ := by
  let W : Set (LegalMarkedPhysicalPoint q) := haarRootCube (Fin q) (R + 1) ×ˢ univ
  have hW : MeasurableSet W := measurableSet_Icc.prod MeasurableSet.univ
  filter_upwards [P.ae_finite_fullSpatialInput (K := haarRootCube (Fin q) (R + 1))
    isCompact_Icc] with s hs
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hW,
    Measure.restrict_apply (hW.preimage measurable_fst)]
  exact lt_of_le_of_lt (measure_mono (by
    intro p hp
    exact ⟨hp.1, mem_univ _⟩)) hs

/-- The actual literal reflected scalar field is bounded simultaneously on every smooth
mean-zero test by one measurable same-scene random variable of surface-order expectation. -/
theorem LegalWeightedStationaryPoissonMatching.original_fullInput_reflected_dual_bound
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
    let B := originalReflectedInputDualBound K hη hηsupport R C c
    Measurable B ∧ (∀ s, 0 ≤ B s) ∧
    Integrable B (P.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, B s ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      cubeReflectedResponseSobolevConstant q M ^ 2 *
        (4 * (q : ℝ) * 4^(q-1)) * R^(q-1) * γ.real C ∧
    ∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ φ : originalMeanZeroSmoothTests K (volume.restrict (haarRootCube (Fin q) R)),
      |∫ z in haarRootCube (Fin q) R,
        originalClassReflectedInputScalarField η R C (legalInputColorMeasure q s.2 c) z *
          (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z|^2 ≤
        B s * ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube (Fin q) R))
          (φ : 𝓓_{K}(Fin q → ℝ, ℝ))‖^2 := by
  obtain ⟨hi, hLp, _, hsecond⟩ := P.original_fullInput_reflectedHilbert_moments K hq hη
    hηsupport hM hηM hηone hηeven hR hC c b
  refine ⟨measurable_originalReflectedInputDualBound K hη hηsupport R hC c,
    fun s ↦ sq_nonneg _, hLp.integrable_norm_pow' (p := 2), hsecond, ?_⟩
  filter_upwards [hi, P.ae_finite_reflectedInputOuterWindow R c] with s hs hfin
  intro φ
  rw [integral_originalClassReflectedInputScalarField_mul_eq_of_finite_outer hη.measurable hM
    hηM hηsupport hR hC (legalInputColorMeasure q s.2 c) hfin
    (φ : 𝓓_{K}(Fin q → ℝ, ℝ)).continuous]
  exact originalReflectedInputDualBound_controls_double_integral K hη hηsupport hR C c s hs φ

end OTSelector.Reconstruction
