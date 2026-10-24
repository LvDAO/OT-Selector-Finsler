import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetPhysicalGaussGreen

/-! Actual Euclidean energy controls the current-gradient term on the same physical cube. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The literal Euclidean square energy on the unchanged selected physical cube. -/
def originalScreeningPhysicalCurrentEnergy {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (J : (Fin q → ℝ) → Fin q → ℝ) (L : ℝ) : ℝ :=
  ∫ z in originalCenteredPhysicalCubeRegion b L,
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (J z)‖^2

/-- The actual original physical vector-current energy is nonnegative. -/
theorem originalScreeningPhysicalCurrentEnergy_nonneg {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (J : (Fin q → ℝ) → Fin q → ℝ) (L : ℝ) :
    0 ≤ originalScreeningPhysicalCurrentEnergy b J L := integral_nonneg (fun _ ↦ sq_nonneg _)

/-- Physical Hilbert Cauchy bounds the genuine derivative-current pairing by the exact
original Euclidean current energy and original smooth physical gradient norm. -/
theorem originalScreeningPhysicalCurrentGradientPairing_sq_le {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {J : (Fin q → ℝ) → Fin q → ℝ} (hJ : Continuous J) (L : ℝ)
    (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    (originalScreeningPhysicalCurrentGradientPairing b J L φ)^2 ≤
      originalScreeningPhysicalCurrentEnergy b J L *
        ‖smoothPhysicalGradientLtwo K
          (volume.restrict (originalCenteredPhysicalCubeRegion b L)) φ‖^2 := by
  let μ := volume.restrict (originalCenteredPhysicalCubeRegion b L)
  let V := fun z ↦ (EuclideanSpace.equiv (Fin q) ℝ).symm (J z)
  have hc : IsCompact (originalCenteredPhysicalCubeRegion b L) :=
    isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous
  have hV : Continuous V := (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.comp hJ
  have hVm : MemLp V 2 μ :=
    (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr
      ((hV.norm.pow 2).continuousOn.integrableOn_compact hc)
  let v := hVm.toLp V
  have hi : ⟪v, smoothPhysicalGradientLtwo K μ φ⟫_ℝ =
      originalScreeningPhysicalCurrentGradientPairing b J L φ := by
    rw [inner_smoothPhysicalGradientLtwo]
    apply integral_congr_ae
    filter_upwards [hVm.coeFn_toLp] with z hz
    rw [hz]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      physicalCoordinateGradient_apply]
    exact (linear_current_readout_eq_sum_coordinates (fderiv ℝ φ z).toLinearMap (J z)).symm
  have hv : ‖v‖^2 = originalScreeningPhysicalCurrentEnergy b J L := by
    rw [physicalFlux_norm_sq]
    apply integral_congr_ae
    filter_upwards [hVm.coeFn_toLp] with z hz
    rw [hz]
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (abs_real_inner_le_norm v (smoothPhysicalGradientLtwo K μ φ)) 2
  rw [sq_abs, mul_pow, hi, hv] at h
  exact h

end OTSelector.Reconstruction
