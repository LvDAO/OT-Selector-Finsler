import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedKernel

/-! Genuine Euclidean unit-range support of the same physical reflected port kernel. -/
open Set Function MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Each coordinate reflection can only increase coordinatewise endpoint distance inside
its original cube. This also controls the genuine Euclidean norm. -/
theorem abs_sub_le_abs_sub_originalCubeReflectionImage {q : ℕ} {R : ℝ}
    {z x : Fin q → ℝ} (hz : z ∈ haarRootCube (Fin q) R) (hx : x ∈ haarRootCube (Fin q) R)
    (a : Fin q → Fin 3) (i : Fin q) :
    |z i - x i| ≤ |z i - originalCubeReflectionImage R a x i| := by
  unfold originalCubeReflectionImage
  by_cases h0 : a i = 0
  · simp [h0]
  · rw [ite_eq_right h0]
    by_cases h1 : a i = 1
    · rw [ite_eq_left h1]
      have hi : |z i - x i| ≤ z i - (-2 * R - x i) :=
        abs_le.mpr ⟨by linarith [hz.1 i], by linarith [hx.1 i]⟩
      exact hi.trans (le_abs_self _)
    · rw [ite_eq_right h1]
      have hi : |z i - x i| ≤ -(z i - (2 * R - x i)) :=
        abs_le.mpr ⟨by linarith [hx.2 i], by linarith [hz.2 i]⟩
      exact hi.trans (neg_le_abs _)

/-- Orthogonal reflection preserves the original Euclidean unit-range bound, with no
coordinate-dimension penalty. -/
theorem euclidean_norm_sub_le_reflection {q : ℕ} {R : ℝ} {z x : Fin q → ℝ}
    (hz : z ∈ haarRootCube (Fin q) R) (hx : x ∈ haarRootCube (Fin q) R)
    (a : Fin q → Fin 3) :
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (z - x)‖ ≤
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (z - originalCubeReflectionImage R a x)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  change ‖z i - x i‖ ^ 2 ≤ ‖z i - originalCubeReflectionImage R a x i‖ ^ 2
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_abs_sub_originalCubeReflectionImage hz hx a i) _

/-- The inverse chosen physical frame preserves genuine Euclidean distance exactly. -/
theorem norm_euclidean_inverse_originalStageFrame {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (v : Fin q → ℝ) :
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm ((orthonormalPhysicalCubeMap b).symm v)‖ =
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖ := by
  have h := norm_euclidean_orthonormalPhysicalCubeMap b ((orthonormalPhysicalCubeMap b).symm v)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm

/-- The same canonical physical port kernel vanishes at genuine Euclidean distance at
least one from its unchanged original endpoint, in every chosen physical orientation. -/
theorem originalCanonicalOrientedReflectedKernel_eq_zero_of_one_le_euclidean {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} {z x : Fin q → ℝ}
    (hz : z ∈ originalCenteredPhysicalCubeRegion b (2 * R))
    (hx : x ∈ originalCenteredPhysicalCubeRegion b (2 * R))
    (hd : 1 ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (z - x)‖) :
    originalCanonicalOrientedReflectedKernel b R z x = 0 := by
  have hhalf : 2 * R / 2 = R := by ring
  have hz' : (orthonormalPhysicalCubeMap b).symm z ∈ haarRootCube (Fin q) R := by
    simpa only [hhalf] using (mem_originalCenteredPhysicalCubeRegion_iff b (2 * R) z).mp hz
  have hx' : (orthonormalPhysicalCubeMap b).symm x ∈ haarRootCube (Fin q) R := by
    simpa only [hhalf] using (mem_originalCenteredPhysicalCubeRegion_iff b (2 * R) x).mp hx
  unfold originalCanonicalOrientedReflectedKernel originalCubeReflectedKernel
  apply Finset.sum_eq_zero
  intro a _
  apply originalEuclideanMollifier_unit_range
  have hnorm := euclidean_norm_sub_le_reflection hz' hx' a
  rw [← map_sub, norm_euclidean_inverse_originalStageFrame] at hnorm
  exact hd.trans hnorm

end OTSelector.Reconstruction
