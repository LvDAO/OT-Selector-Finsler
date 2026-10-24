import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetGaussGreen

/-! The literal current-gradient pairing is controlled by actual Euclidean current energy. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The actual original Euclidean square energy of the spatial vector current on the cube. -/
def originalStageCurrentLtwoEnergy {q : ℕ} (J : (Fin q → ℝ) → Fin q → ℝ) (R : ℝ) : ℝ :=
  ∫ z in haarRootCube (Fin q) R,
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (J z)‖^2

/-- The literal current energy is nonnegative. -/
theorem originalStageCurrentLtwoEnergy_nonneg {q : ℕ}
    (J : (Fin q → ℝ) → Fin q → ℝ) (R : ℝ) : 0 ≤ originalStageCurrentLtwoEnergy J R :=
  integral_nonneg (fun _ ↦ sq_nonneg _)

/-- Cauchy in the genuine physical L2 spaces controls every original gradient test by
actual vector-current energy, without a supplied field-energy or dual-norm bound. -/
theorem originalStageCurrentGradientPairing_sq_le {q : ℕ}
    {J : (Fin q → ℝ) → Fin q → ℝ} (hJ : Continuous J) (R : ℝ)
    (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    (originalStageCurrentGradientPairing J R φ)^2 ≤ originalStageCurrentLtwoEnergy J R *
      ‖smoothPhysicalGradientLtwo K
        (volume.restrict (haarRootCube (Fin q) R)) φ‖^2 := by
  let μ := volume.restrict (haarRootCube (Fin q) R)
  let V := fun z ↦ (EuclideanSpace.equiv (Fin q) ℝ).symm (J z)
  have hV : Continuous V := (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.comp hJ
  have hVm : MemLp V 2 μ :=
    (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr
      (hV.norm.pow 2).continuousOn.integrableOn_Icc
  let v := hVm.toLp V
  have hi : ⟪v, smoothPhysicalGradientLtwo K μ φ⟫_ℝ =
      originalStageCurrentGradientPairing J R φ := by
    rw [inner_smoothPhysicalGradientLtwo]
    apply integral_congr_ae
    filter_upwards [hVm.coeFn_toLp] with z hz
    rw [hz]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      physicalCoordinateGradient_apply]
    rfl
  have hv : ‖v‖^2 = originalStageCurrentLtwoEnergy J R := by
    rw [physicalFlux_norm_sq]
    apply integral_congr_ae
    filter_upwards [hVm.coeFn_toLp] with z hz
    rw [hz]
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (abs_real_inner_le_norm v (smoothPhysicalGradientLtwo K μ φ)) 2
  rw [sq_abs, mul_pow, hi, hv] at h
  exact h

end OTSelector.Reconstruction
