import OTSelector.Reconstruction.OriginalCubeTraceCompactnessCanonicalHilbertResponse
import OTSelector.Reconstruction.OriginalCubeReflectedLtwoMean

/-! Actual class-marked reflected Hilbert responses have zero mean and surface-order intensity. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ} (K : Compacts (Fin q → ℝ)) {η : (Fin q → ℝ) → ℝ}

/-- The original class-marked Hilbert response on physical location and real clock mark. -/
def originalClassReflectedInputHilbertResponse (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) (C : Set ℝ)
    (p : (Fin q → ℝ) × ℝ) :
    originalGradientClosure (originalMeanZeroGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R))) :=
  C.indicator (fun _ ↦ (1 : ℝ)) p.2 • originalReflectedInputHilbertResponse K hη hηsupport R p.1

/-- Class-marking preserves actual strong measurability of the original Hilbert family. -/
theorem stronglyMeasurable_originalClassReflectedInputHilbertResponse
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C) :
    StronglyMeasurable (originalClassReflectedInputHilbertResponse K hη hηsupport R C) := by
  have hi : StronglyMeasurable (C.indicator (fun _ : ℝ ↦ (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hC
  change StronglyMeasurable (fun p : (Fin q → ℝ) × ℝ ↦
    C.indicator (fun _ ↦ (1 : ℝ)) p.2 • originalReflectedInputHilbertResponse K hη hηsupport R p.1)
  simpa only [Function.comp_def, Pi.smul_def'] using
    (hi.comp_measurable measurable_snd).smul
      ((stronglyMeasurable_originalReflectedInputHilbertResponse K hη hηsupport R).comp_measurable measurable_fst)

/-- The class-marked response is zero outside the true spatial shell or the chosen class. -/
theorem originalClassReflectedInputHilbertResponse_eq_zero_off_shell_or_class
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {R : ℝ} (hR : 1 ≤ R) (C : Set ℝ) (p : (Fin q → ℝ) × ℝ)
    (hp : p.1 ∉ originalInputBoundaryShell (ι := Fin q) R ∨ p.2 ∉ C) :
    originalClassReflectedInputHilbertResponse K hη hηsupport R C p = 0 := by
  rcases hp with hx | ha
  · rw [originalClassReflectedInputHilbertResponse,
      originalReflectedInputHilbertResponse_eq_zero_off_shell K hη hηsupport hR p.1 hx, smul_zero]
  · rw [originalClassReflectedInputHilbertResponse, indicator_of_notMem ha, zero_smul]

/-- The class-marked response has the same genuine dimension-only Sobolev norm bound. -/
theorem norm_originalClassReflectedInputHilbertResponse_le
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (C : Set ℝ) (p : (Fin q → ℝ) × ℝ) :
    ‖originalClassReflectedInputHilbertResponse K hη hηsupport R C p‖ ≤
      cubeReflectedResponseSobolevConstant q M := by
  by_cases ha : p.2 ∈ C
  · simpa only [originalClassReflectedInputHilbertResponse, indicator_of_mem ha, one_smul] using
      norm_originalReflectedInputHilbertResponse_le K hq hη hηsupport hM hηM hR p.1
  · rw [originalClassReflectedInputHilbertResponse_eq_zero_off_shell_or_class K hη hηsupport hR C p (Or.inr ha), norm_zero]
    exact cubeReflectedResponseSobolevConstant_nonneg q hM

/-- The canonical continuous linear response transports genuine full-input L2 integrability. -/
theorem integrable_originalReflectedInputHilbertResponse
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R) :
    Integrable (originalReflectedInputHilbertResponse K hη hηsupport R) volume :=
  (originalCubeMeanZeroResponse K R).integrable_comp
    (integrable_originalReflectedInputResponseLtwo hη hηsupport hM hηM hR)

/-- The actual Hilbert response has zero full-input Haar Bochner mean. -/
theorem integral_originalReflectedInputHilbertResponse_eq_zero
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηone : ∫ v, η v = 1)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) :
    (∫ x, originalReflectedInputHilbertResponse K hη hηsupport R x) = 0 := by
  change (∫ x, originalCubeMeanZeroResponse K R
    (originalReflectedInputResponseLtwo hη hηsupport R x)) = 0
  rw [(originalCubeMeanZeroResponse K R).integral_comp_comm
    (integrable_originalReflectedInputResponseLtwo hη hηsupport hM hηM hR),
    integral_originalReflectedInputResponseLtwo_eq_zero hη hηsupport hM hηM hηone hηeven hR, map_zero]

/-- The actual marked response is integrable for every original finite mark measure. -/
theorem integrable_originalClassReflectedInputHilbertResponse
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (γ : Measure ℝ) [IsFiniteMeasure γ] {C : Set ℝ} (hC : MeasurableSet C) :
    Integrable (originalClassReflectedInputHilbertResponse K hη hηsupport R C)
      (volume.prod γ) := by
  have hi : Integrable (C.indicator (fun _ ↦ (1 : ℝ))) γ := (integrable_const _).indicator hC
  have h := (hi.smul_prod
    (integrable_originalReflectedInputHilbertResponse K hη hηsupport hM hηM hR)).swap
  change Integrable (fun p : (Fin q → ℝ) × ℝ ↦
    C.indicator (fun _ ↦ (1 : ℝ)) p.2 • originalReflectedInputHilbertResponse K hη hηsupport R p.1)
    (volume.prod γ)
  simpa only [Function.comp_def, Prod.swap] using h

/-- The original class-marked response has zero intensity mean under full spatial Haar
measure times any finite original clock-mark measure. -/
theorem integral_originalClassReflectedInputHilbertResponse_eq_zero
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηone : ∫ v, η v = 1)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) (γ : Measure ℝ) [IsFiniteMeasure γ]
    {C : Set ℝ} (hC : MeasurableSet C) :
    (∫ p, originalClassReflectedInputHilbertResponse K hη hηsupport R C p ∂volume.prod γ) = 0 := by
  rw [integral_prod _ (integrable_originalClassReflectedInputHilbertResponse K hη hηsupport hM hηM hR γ hC)]
  simp_rw [originalClassReflectedInputHilbertResponse, integral_smul_const, integral_smul]
  rw [integral_originalReflectedInputHilbertResponse_eq_zero K hη hηsupport hM hηM hηone hηeven hR, smul_zero]

private theorem integrable_sq_originalReflectedInputHilbertResponse
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R) :
    Integrable (fun x ↦ ‖originalReflectedInputHilbertResponse K hη hηsupport R x‖^2) volume := by
  have hc : HasCompactSupport (fun x ↦ ‖originalReflectedInputHilbertResponse K hη hηsupport R x‖^2) := by
    apply HasCompactSupport.intro (K := haarRootCube (Fin q) (R + 1)) isCompact_Icc
    intro x hx
    rw [originalReflectedInputHilbertResponse_eq_zero_off_shell K hη hηsupport hR x (fun hs ↦ hx hs.1), norm_zero, zero_pow (by decide : 2 ≠ 0)]
  apply memLp_one_iff_integrable.mp
  apply hc.memLp_of_bound
    ((stronglyMeasurable_originalReflectedInputHilbertResponse K hη hηsupport R).norm.pow 2).aestronglyMeasurable
    (cubeReflectedResponseSobolevConstant q M ^ 2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_originalReflectedInputHilbertResponse_le K hq hη hηsupport hM hηM hR x) 2

private theorem norm_sq_originalClassReflectedInputHilbertResponse
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (R : ℝ) (C : Set ℝ) (p : (Fin q → ℝ) × ℝ) :
    ‖originalClassReflectedInputHilbertResponse K hη hηsupport R C p‖^2 =
      ‖originalReflectedInputHilbertResponse K hη hηsupport R p.1‖^2 * C.indicator (fun _ ↦ (1 : ℝ)) p.2 := by
  by_cases ha : p.2 ∈ C
  · rw [originalClassReflectedInputHilbertResponse, indicator_of_mem ha, one_smul, mul_one]
  · rw [originalClassReflectedInputHilbertResponse, indicator_of_notMem ha, zero_smul,
      norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- The genuine marked Hilbert response has integrable squared norm under actual intensity. -/
theorem integrable_sq_originalClassReflectedInputHilbertResponse
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (γ : Measure ℝ) [IsFiniteMeasure γ] {C : Set ℝ} (hC : MeasurableSet C) :
    Integrable (fun p ↦ ‖originalClassReflectedInputHilbertResponse K hη hηsupport R C p‖^2)
      (volume.prod γ) := by
  have hi : Integrable (C.indicator (fun _ ↦ (1 : ℝ))) γ := (integrable_const _).indicator hC
  apply ((integrable_sq_originalReflectedInputHilbertResponse K hq hη hηsupport hM hηM hR).mul_prod hi).congr
  exact ae_of_all _ (fun p ↦ (norm_sq_originalClassReflectedInputHilbertResponse K hη hηsupport R C p).symm)

/-- Literal marked response energy is bounded by the actual boundary-shell intensity. -/
theorem integral_sq_originalClassReflectedInputHilbertResponse_le_shell
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (γ : Measure ℝ) [IsFiniteMeasure γ] {C : Set ℝ} (hC : MeasurableSet C) :
    (∫ p, ‖originalClassReflectedInputHilbertResponse K hη hηsupport R C p‖^2 ∂volume.prod γ) ≤
      cubeReflectedResponseSobolevConstant q M ^ 2 *
        volume.real (originalInputBoundaryShell (ι := Fin q) R) * γ.real C := by
  let S := originalInputBoundaryShell (ι := Fin q) R
  let U := cubeReflectedResponseSobolevConstant q M
  have hS : MeasurableSet S := measurableSet_Icc.diff measurableSet_Icc
  have hI : Integrable (S.indicator (fun _ : Fin q → ℝ ↦ U^2)) volume := by
    apply (integrable_indicator_iff hS).mpr
    exact integrableOn_const (ne_of_lt ((measure_mono sdiff_subset).trans_lt isCompact_Icc.measure_lt_top))
  have hspatial : (∫ x, ‖originalReflectedInputHilbertResponse K hη hηsupport R x‖^2) ≤
      U^2 * volume.real S := by
    calc
      _ ≤ ∫ x, S.indicator (fun _ ↦ U^2) x := by
        apply integral_mono (integrable_sq_originalReflectedInputHilbertResponse K hq hη hηsupport hM hηM hR) hI
        intro x
        change ‖originalReflectedInputHilbertResponse K hη hηsupport R x‖^2 ≤
          S.indicator (fun _ ↦ U^2) x
        by_cases hx : x ∈ S
        · rw [indicator_of_mem hx]
          exact pow_le_pow_left₀ (norm_nonneg _)
            (norm_originalReflectedInputHilbertResponse_le K hq hη hηsupport hM hηM hR x) 2
        · rw [indicator_of_notMem hx,
            originalReflectedInputHilbertResponse_eq_zero_off_shell K hη hηsupport hR x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      _ = U^2 * volume.real S := by rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]
  calc
    _ = (∫ x, ‖originalReflectedInputHilbertResponse K hη hηsupport R x‖^2) * γ.real C := by
      calc
        _ = ∫ p : (Fin q → ℝ) × ℝ,
            ‖originalReflectedInputHilbertResponse K hη hηsupport R p.1‖^2 * C.indicator (fun _ ↦ (1 : ℝ)) p.2 ∂volume.prod γ := by
          exact integral_congr_ae (ae_of_all _ (norm_sq_originalClassReflectedInputHilbertResponse K hη hηsupport R C))
        _ = _ := by
          have h := integral_prod_mul (μ := (volume : Measure (Fin q → ℝ))) (ν := γ)
            (fun x ↦ ‖originalReflectedInputHilbertResponse K hη hηsupport R x‖^2)
            (C.indicator (fun _ ↦ (1 : ℝ)))
          rw [integral_indicator hC, setIntegral_const, smul_eq_mul, mul_one] at h
          exact h
    _ ≤ _ := mul_le_mul_of_nonneg_right hspatial measureReal_nonneg

/-- The actual marked response intensity has the literal surface-order polynomial bound. -/
theorem integral_sq_originalClassReflectedInputHilbertResponse_le_surface
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (γ : Measure ℝ) [IsFiniteMeasure γ] {C : Set ℝ} (hC : MeasurableSet C) :
    (∫ p, ‖originalClassReflectedInputHilbertResponse K hη hηsupport R C p‖^2 ∂volume.prod γ) ≤
      cubeReflectedResponseSobolevConstant q M ^ 2 *
        (4 * (q : ℝ) * 4^(q-1)) * R^(q-1) * γ.real C := by
  apply (integral_sq_originalClassReflectedInputHilbertResponse_le_shell K hq hη hηsupport hM hηM hR γ hC).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (volume_real_originalInputBoundaryShell_le (ι := Fin q) hR)
      (sq_nonneg (cubeReflectedResponseSobolevConstant q M))) (show 0 ≤ γ.real C from measureReal_nonneg)
  simpa only [Fintype.card_fin, mul_assoc] using h

end OTSelector.Reconstruction
