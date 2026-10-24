import OTSelector.Analysis.InnerProductSpace.CanonicalGradientResponse
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Analysis.Sobolev.SmoothBoxPoincare
import OTSelector.Reconstruction.OriginalPathLengthRetention
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Actual smooth mean-zero cube tests produce the canonical linear Hilbert response. -/
open Set Function MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Original Haar volume on every actual centered coordinate cube is finite. -/
theorem isFiniteMeasure_originalHaarRootCubeVolume {q : ℕ} (R : ℝ) :
    IsFiniteMeasure (volume.restrict (haarRootCube (Fin q) R)) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
attribute [instance] isFiniteMeasure_originalHaarRootCubeVolume

/-- The actual smooth-test mean under the original finite physical measure. -/
def originalSmoothTestMean {q : ℕ} (K : Compacts (Fin q → ℝ))
    (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ] : 𝓓_{K}(Fin q → ℝ, ℝ) →ₗ[ℝ] ℝ where
  toFun φ := ∫ z, φ z ∂μ
  map_add' φ ψ := by
    exact integral_add
      (BoundedContinuousFunction.integrable μ (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ φ))
      (BoundedContinuousFunction.integrable μ (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ ψ))
  map_smul' c φ := integral_const_mul c φ

/-- The genuine original zero-mean smooth test space. -/
def originalMeanZeroSmoothTests {q : ℕ} (K : Compacts (Fin q → ℝ))
    (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ] : Submodule ℝ 𝓓_{K}(Fin q → ℝ, ℝ) :=
  (originalSmoothTestMean K μ).ker

/-- The original smooth test itself, represented in its true scalar L2 space. -/
def originalSmoothPotentialLtwo {q : ℕ} (K : Compacts (Fin q → ℝ))
    (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ] :
    𝓓_{K}(Fin q → ℝ, ℝ) →ₗ[ℝ] Lp ℝ 2 μ :=
  (BoundedContinuousFunction.toLp 2 μ ℝ).toLinearMap.comp
    (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ)

/-- The potential of an original mean-zero test uses the same actual scalar L2 function. -/
def originalMeanZeroPotentialLtwo {q : ℕ} (K : Compacts (Fin q → ℝ))
    (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ] :
    originalMeanZeroSmoothTests K μ →ₗ[ℝ] Lp ℝ 2 μ :=
  (originalSmoothPotentialLtwo K μ).comp (originalMeanZeroSmoothTests K μ).subtype

/-- The gradient of an original mean-zero test uses the original physical gradient L2 map. -/
def originalMeanZeroGradientLtwo {q : ℕ} (K : Compacts (Fin q → ℝ))
    (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ] :
    originalMeanZeroSmoothTests K μ →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin q)) 2 μ :=
  (smoothPhysicalGradientLtwo K μ).comp (originalMeanZeroSmoothTests K μ).subtype

/-- The scalar potential representative agrees with the literal original smooth test. -/
theorem originalSmoothPotentialLtwo_ae {q : ℕ} (K : Compacts (Fin q → ℝ))
    (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ] (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    originalSmoothPotentialLtwo K μ φ =ᵐ[μ] φ :=
  BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℝ)
    (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ φ)

/-- The actual potential norm squared is its original scalar square integral. -/
theorem originalSmoothPotentialLtwo_norm_sq {q : ℕ} (K : Compacts (Fin q → ℝ))
    (μ : Measure (Fin q → ℝ)) [IsFiniteMeasure μ] (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    ‖originalSmoothPotentialLtwo K μ φ‖^2 = ∫ z, (φ z)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [originalSmoothPotentialLtwo_ae K μ φ] with z hz
  simp only [hz, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The original full coordinate derivative energy is exactly the actual cube gradient norm. -/
theorem originalHaarRootCubeGradientLtwo_norm_sq {q : ℕ}
    (K : Compacts (Fin q → ℝ)) (R : ℝ) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)) φ‖^2 =
      ∑ k : Fin q, ∫ z in haarRootCube (Fin q) R,
        (fderiv ℝ φ z (Pi.single k 1))^2 := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (haarRootCube (Fin q) R)
  have hi (k : Fin q) : Integrable (fun z ↦ (fderiv ℝ φ z (Pi.single k 1))^2) μ :=
    (((φ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).continuousOn.integrableOn_Icc
  rw [physicalFlux_norm_sq]
  calc
    _ = ∫ z, ∑ k : Fin q, (fderiv ℝ φ z (Pi.single k 1))^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [smoothPhysicalGradientLtwo_ae K μ φ] with z hz
      rw [hz, EuclideanSpace.real_norm_sq_eq]
      rfl
    _ = _ := integral_finsetSum Finset.univ (fun k _ ↦ hi k)

/-- Actual cube Poincare bounds the real scalar potential by its real original gradient.
This is the ordinary radius-dependent bound used only to construct one canonical operator. -/
theorem originalMeanZeroPotentialLtwo_norm_le {q : ℕ} (K : Compacts (Fin q → ℝ))
    {R : ℝ} (hR : 0 < R)
    (φ : originalMeanZeroSmoothTests K (volume.restrict (haarRootCube (Fin q) R))) :
    ‖originalMeanZeroPotentialLtwo K (volume.restrict (haarRootCube (Fin q) R)) φ‖ ≤
      (Real.sqrt (q : ℝ) * (2 * R)) *
        ‖originalMeanZeroGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)) φ‖ := by
  have hm : (∫ z in haarRootCube (Fin q) R, (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z) = 0 := φ.property
  have hP := smooth_box_poincare_sq_of_mean_zero
    (a := fun _ : Fin q ↦ -R) (b := fun _ ↦ R) (fun _ ↦ by linarith)
    ((φ : 𝓓_{K}(Fin q → ℝ, ℝ)).contDiff.of_le (by norm_num)) hm
  simp only [sub_neg_eq_add, ← two_mul, ← Finset.mul_sum] at hP
  change 2 * (∫ z in haarRootCube (Fin q) R, (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z ^ 2) ≤
    (q : ℝ) * ((2 * R)^2 * ∑ k : Fin q, ∫ z in haarRootCube (Fin q) R,
      (fderiv ℝ (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z (Pi.single k 1))^2) at hP
  have hpot := originalSmoothPotentialLtwo_norm_sq K
    (volume.restrict (haarRootCube (Fin q) R)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ))
  have hgrad := originalHaarRootCubeGradientLtwo_norm_sq K R
    (φ : 𝓓_{K}(Fin q → ℝ, ℝ))
  have hC : 0 ≤ Real.sqrt (q : ℝ) * (2 * R) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  change ‖originalSmoothPotentialLtwo K (volume.restrict (haarRootCube (Fin q) R))
      (φ : 𝓓_{K}(Fin q → ℝ, ℝ))‖^2 ≤
    ((Real.sqrt (q : ℝ) * (2 * R)) *
      ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube (Fin q) R))
        (φ : 𝓓_{K}(Fin q → ℝ, ℝ))‖)^2
  rw [hpot, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q), hgrad]
  have hn : 0 ≤ (∫ z in haarRootCube (Fin q) R,
      ((φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z)^2) := integral_nonneg (fun _ ↦ sq_nonneg _)
  nlinarith [hn]

/-- The actual original mean-zero smooth cube tests define one canonical continuous linear
Hilbert response, valued in the genuine closed original gradient space. -/
def originalCubeMeanZeroResponse {q : ℕ} (K : Compacts (Fin q → ℝ)) (R : ℝ) :
    Lp ℝ 2 (volume.restrict (haarRootCube (Fin q) R)) →L[ℝ]
      originalGradientClosure (originalMeanZeroGradientLtwo K
        (volume.restrict (haarRootCube (Fin q) R))) :=
  originalCanonicalGradientResponse
    (originalMeanZeroGradientLtwo K (volume.restrict (haarRootCube (Fin q) R)))
    (originalMeanZeroPotentialLtwo K (volume.restrict (haarRootCube (Fin q) R)))

/-- The canonical cube response realizes the literal original integral against every smooth
mean-zero test; neither a solution operator nor the pairing identity is an input. -/
theorem inner_originalCubeMeanZeroResponse_gradient {q : ℕ}
    (K : Compacts (Fin q → ℝ)) {R : ℝ} (hR : 0 < R)
    (f : Lp ℝ 2 (volume.restrict (haarRootCube (Fin q) R)))
    (φ : originalMeanZeroSmoothTests K (volume.restrict (haarRootCube (Fin q) R))) :
    ⟪originalCubeMeanZeroResponse K R f,
      originalDenseGradient (originalMeanZeroGradientLtwo K
        (volume.restrict (haarRootCube (Fin q) R))) φ⟫_ℝ =
      ∫ z in haarRootCube (Fin q) R, f z * (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) z := by
  rw [originalCubeMeanZeroResponse,
    inner_originalCanonicalGradientResponse_grad _ _
      ⟨Real.sqrt (q : ℝ) * (2 * R), originalMeanZeroPotentialLtwo_norm_le K hR⟩,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [originalSmoothPotentialLtwo_ae K
    (volume.restrict (haarRootCube (Fin q) R)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ))] with z hz
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  change (f z) * (originalSmoothPotentialLtwo K
    (volume.restrict (haarRootCube (Fin q) R)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ))) z = _
  rw [hz]

end OTSelector.Reconstruction
