import OTSelector.Analysis.Sobolev.UnitCubePoincareEnergy
import OTSelector.MeasureTheory.Lp.AffineCubeScaling
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessAffineScale

/-! True scale-independent critical Sobolev-Poincare on translated and centered cubes. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction

/-- The actual critical dimension exponent cancels the genuine affine energy scale. -/
theorem critical_sobolev_affine_scale_cancel {q : ℕ} (hq : 0 < q) {p : ℝ≥0}
    (hp : (p : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (q : ℝ)⁻¹) {L : ℝ} (hL : 0 < L) :
    (L^q) ^ (1 / (p : ℝ)) * Real.sqrt (L^2 * (L^q)⁻¹) = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hF : 0 < L^2 * (L^q)⁻¹ := mul_pos (pow_pos hL _) (inv_pos.mpr (pow_pos hL _))
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (pow_pos hL _), Real.rpow_def_of_pos hF,
    ← Real.exp_add, Real.log_mul (pow_ne_zero _ hL.ne') (inv_ne_zero (pow_ne_zero _ hL.ne')),
    Real.log_inv, Real.log_pow, Real.log_pow]
  have he : (q : ℝ) * Real.log L * (1 / (p : ℝ)) +
      ((2 : ℝ) * Real.log L - (q : ℝ) * Real.log L) * (1 / (2 : ℝ)) = 0 := by
    rw [one_div, hp]
    field_simp [hq0]
    ring
  simpa only [Nat.cast_ofNat, sub_eq_add_neg, Real.exp_zero] using congrArg Real.exp he

/-- Genuine critical Sobolev-Poincare on every translated cube with exactly the unit-cube
constant. The affine norm, volume, original derivative and mean scalings are proved inputs. -/
theorem smooth_affine_cube_sobolev_poincare
    {q : ℕ} (hq : 2 < q) {p : ℝ≥0}
    (hp : (p : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (q : ℝ)⁻¹)
    (a : Fin q → ℝ) {L : ℝ} (hL : 0 < L)
    {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hmean : (∫ x in Icc a (a + L • 1), u x) = 0) :
    eLpNorm u p (volume.restrict (Icc a (a + L • 1))) ≤
      ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt
        (originalRawBoxGradientEnergy a (a + L • 1) u)) := by
  have hf : ContDiff ℝ 1 (fun y : Fin q → ℝ ↦ u (a + L • y)) :=
    hu.comp (contDiff_const.add (contDiff_id.const_smul L))
  have hm : (∫ y in Icc (0 : Fin q → ℝ) 1, u (a + L • y)) = 0 := by
    rw [integral_affine_unit_cube_eq_inv_smul u a hL, hmean, smul_zero]
  have hunit := smooth_unit_cube_eLpNorm_critical_le_sqrt_coordinate_energy hq hp hf hm
  change eLpNorm (fun y ↦ u (a + L • y)) p (volume.restrict (Icc (0 : Fin q → ℝ) 1)) ≤
    ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt
      (originalRawUnitCubeGradientEnergy (fun y ↦ u (a + L • y)))) at hunit
  rw [originalRawUnitCubeGradientEnergy_affine hu a hL] at hunit
  have hF : 0 ≤ L^2 * (L^q)⁻¹ := mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (pow_nonneg hL.le _))
  have hc := critical_sobolev_affine_scale_cancel (show 0 < q by omega) hp hL
  rw [eLpNorm_affine_cube_eq_pow_mul u p a hL]
  calc
    _ ≤ ENNReal.ofReal (L^q) ^ (1 / (p : ℝ)) *
        ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt
          (L^2 * (L^q)⁻¹ * originalRawBoxGradientEnergy a (a + L • 1) u)) :=
      mul_le_mul le_rfl hunit bot_le bot_le
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_pos (pow_pos hL _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg hL.le _) _)]
      congr 1
      rw [Real.sqrt_mul hF]
      calc
        _ = cubeSobolevPoincareConstant q *
            ((L^q) ^ (1 / (p : ℝ)) * Real.sqrt (L^2 * (L^q)⁻¹)) *
              Real.sqrt (originalRawBoxGradientEnergy a (a + L • 1) u) := by ring
        _ = _ := by rw [hc, mul_one]

/-- Actual centered radius-R cubes have the same dimension-only Sobolev-Poincare constant,
with the literal critical exponent and original coordinate-gradient energy. -/
theorem smooth_centered_cube_sobolev_poincare
    {q : ℕ} (hq : 2 < q) {R : ℝ} (hR : 1 ≤ R)
    {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hmean : (∫ x in Icc (fun _ : Fin q ↦ -R) (fun _ ↦ R), u x) = 0) :
    eLpNorm u (ENNReal.ofReal (2 * (q : ℝ) / ((q : ℝ) - 2)))
      (volume.restrict (Icc (fun _ : Fin q ↦ -R) (fun _ ↦ R))) ≤
      ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt
        (∑ k : Fin q, ∫ x in Icc (fun _ : Fin q ↦ -R) (fun _ ↦ R),
          (fderiv ℝ u x (Pi.single k 1))^2)) := by
  have hside : 0 < 2*R := by linarith
  have hupper : (fun _ : Fin q ↦ -R) + (2*R) • 1 = (fun _ ↦ R) := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    ring
  have hp : ((Real.toNNReal (2 * (q : ℝ) / ((q : ℝ) - 2))) : ℝ)⁻¹ =
      (2 : ℝ)⁻¹ - (q : ℝ)⁻¹ := by
    have hqr : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < (q : ℝ) := lt_trans (by norm_num) hqr
    have hden : (0 : ℝ) < (q : ℝ) - 2 := sub_pos.mpr hqr
    rw [Real.coe_toNNReal _ (le_of_lt (div_pos (mul_pos (by norm_num) hqpos) hden))]
    field_simp [ne_of_gt hqpos, ne_of_gt hden]
  have hh := smooth_affine_cube_sobolev_poincare hq hp (fun _ ↦ -R) hside hu
    (by rw [hupper]; exact hmean)
  simpa only [hupper, originalRawBoxGradientEnergy, ENNReal.ofReal] using hh

end OTSelector.Reconstruction
