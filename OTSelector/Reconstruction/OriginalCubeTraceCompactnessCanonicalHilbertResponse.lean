import OTSelector.Reconstruction.OriginalCubeTraceCompactnessCanonicalKernelLtwo
import OTSelector.Reconstruction.OriginalCubeSobolevReflectedResponseBound

/-! Actual reflected full-input kernels have uniformly bounded measurable Hilbert responses. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- The actual reflected full-input response in the true closed original mean-zero gradient
Hilbert space, through one canonical continuous linear map. -/
def originalReflectedInputHilbertResponse (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) (x : Fin q → ℝ) :
    originalGradientClosure (originalMeanZeroGradientLtwo K
      (volume.restrict (haarRootCube (Fin q) R))) :=
  originalCubeMeanZeroResponse K R (originalReflectedInputResponseLtwo hη hηsupport R x)

/-- The true Hilbert response is strongly measurable in the actual original input location. -/
theorem stronglyMeasurable_originalReflectedInputHilbertResponse (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) :
    StronglyMeasurable (originalReflectedInputHilbertResponse K hη hηsupport R) :=
  (originalCubeMeanZeroResponse K R).continuous.comp_stronglyMeasurable
    (stronglyMeasurable_originalReflectedInputResponseLtwo hη hηsupport R)

/-- Every actual mean-zero smooth test sees exactly the literal original reflected input
kernel response through the true Hilbert pairing, simultaneously without any test selection. -/
theorem inner_originalReflectedInputHilbertResponse_gradient (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    (x : Fin q → ℝ)
    (φ : originalMeanZeroSmoothTests K (volume.restrict (haarRootCube (Fin q) R))) :
    ⟪originalReflectedInputHilbertResponse K hη hηsupport R x,
      originalDenseGradient (originalMeanZeroGradientLtwo K
        (volume.restrict (haarRootCube (Fin q) R))) φ⟫_ℝ =
      ∫ z in haarRootCube (Fin q) R,
        originalCubeReflectedInputResponse η R z x * (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z := by
  rw [originalReflectedInputHilbertResponse,
    inner_originalCubeMeanZeroResponse_gradient K (by linarith : 0 < R)]
  apply integral_congr_ae
  filter_upwards [originalReflectedInputResponseLtwo_ae hη hηsupport R x] with z hz
  rw [hz]

/-- The actual critical Sobolev estimate proves a radius-independent bound for the canonical
Hilbert response. No dual-norm, response bound, solution map or rate is a premise. -/
theorem norm_originalReflectedInputHilbertResponse_le (K : Compacts (Fin q → ℝ))
    (hq : 2 < q) (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (x : Fin q → ℝ) :
    ‖originalReflectedInputHilbertResponse K hη hηsupport R x‖ ≤
      cubeReflectedResponseSobolevConstant q M := by
  apply norm_originalCanonicalGradientResponse_le
    (originalMeanZeroGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)))
    (originalMeanZeroPotentialLtwo K (volume.restrict (haarRootCube (Fin q) R)))
    ⟨Real.sqrt (q : ℝ) * (2 * R), originalMeanZeroPotentialLtwo_norm_le K (by linarith)⟩
    (originalReflectedInputResponseLtwo hη hηsupport R x)
    (cubeReflectedResponseSobolevConstant_nonneg q hM)
  intro φ
  have hm : (∫ z in haarRootCube (Fin q) R, (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z) = 0 := φ.property
  have hs := abs_integral_originalCubeReflectedInputResponse_mul_le_sqrt_energy hq
    hη.measurable hM hηM hηsupport hR x
    ((φ : 𝓓_{K}(Fin q → ℝ, ℝ)).contDiff.of_le (by norm_num)) hm
  rw [← originalHaarRootCubeGradientLtwo_norm_sq K R,
    Real.sqrt_sq (norm_nonneg _)] at hs
  have he : ⟪originalReflectedInputResponseLtwo hη hηsupport R x,
      originalMeanZeroPotentialLtwo K (volume.restrict (haarRootCube (Fin q) R)) φ⟫_ℝ =
      ∫ z in haarRootCube (Fin q) R,
        originalCubeReflectedInputResponse η R z x * (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z := by
    rw [← inner_originalCanonicalGradientResponse_grad
      (originalMeanZeroGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)))
      (originalMeanZeroPotentialLtwo K (volume.restrict (haarRootCube (Fin q) R)))
      ⟨Real.sqrt (q : ℝ) * (2 * R), originalMeanZeroPotentialLtwo_norm_le K (by linarith)⟩]
    exact inner_originalReflectedInputHilbertResponse_gradient K hη hηsupport hR x φ
  rw [he]
  exact hs

/-- The same true Hilbert response is zero for every original input outside the actual
unit inner-and-outer cube boundary shell. -/
theorem originalReflectedInputHilbertResponse_eq_zero_off_shell (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    (x : Fin q → ℝ) (hx : x ∉ originalInputBoundaryShell (ι := Fin q) R) :
    originalReflectedInputHilbertResponse K hη hηsupport R x = 0 := by
  rw [originalReflectedInputHilbertResponse,
    originalReflectedInputResponseLtwo_eq_zero_off_shell hη hηsupport hR x hx, map_zero]

/-- The actual Hilbert response is supported on a genuine compact original input window. -/
theorem hasCompactSupport_originalReflectedInputHilbertResponse (K : Compacts (Fin q → ℝ))
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R) :
    HasCompactSupport (originalReflectedInputHilbertResponse K hη hηsupport R) := by
  apply HasCompactSupport.intro (K := haarRootCube (Fin q) (R + 1)) isCompact_Icc
  intro x hx
  exact originalReflectedInputHilbertResponse_eq_zero_off_shell K hη hηsupport hR x
    (fun hs ↦ hx hs.1)

end OTSelector.Reconstruction
