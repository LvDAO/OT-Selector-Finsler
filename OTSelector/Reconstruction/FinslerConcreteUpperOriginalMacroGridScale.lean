import OTSelector.Reconstruction.FinslerRelativeLawPositiveMicrogrid
import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveGridArithmetic

/-! The actual parent-grid order is the integer macro diameter times the
original microscopic order. Its two limits retain this exact factor. -/
open Filter
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- The true count mass at an original macro-grid leaf converges at fixed
microscopic side. No replacement by a noninteger grid order is used. -/
theorem tendsto_original_macro_grid_mass {q R : ℕ} (hq : 0 < q) (_hR : 0 < R)
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) /
      ((2 * R * positiveMicroscopicGridOrder q L N : ℕ) : ℝ) ^ q)
      atTop (𝓝 ((L / (2 * (R : ℝ))) ^ q)) := by
  have heq (N : ℕ) : (N : ℝ) /
      ((2 * R * positiveMicroscopicGridOrder q L N : ℕ) : ℝ) ^ q =
      ((2 * (R : ℝ)) ^ q)⁻¹ *
        ((N : ℝ) * positiveMicroscopicGridSide q L N ^ q) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, positiveMicroscopicGridSide,
      mul_pow, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring_nf
  simp_rw [heq]
  convert (tendsto_positiveMicroscopicGrid_mass hq hL).const_mul
    (((2 * (R : ℝ)) ^ q)⁻¹) using 1
  rw [div_pow]
  ring_nf

/-- The original sample limit is taken while the microscopic side is fixed. -/
theorem tendsto_original_macro_grid_repair_fixed_side {q R : ℕ}
    (hq : 0 < q) (hR : 0 < R) (K C G tilt : ℝ) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ activeGridRepairError q K C G tilt 1
      ((N : ℝ) / ((2 * R * positiveMicroscopicGridOrder q L N : ℕ) : ℝ) ^ q))
      atTop (𝓝 (activeGridRepairError q K C G tilt 1 ((L / (2 * (R : ℝ))) ^ q))) :=
  (continuousAt_activeGridRepairError q K C G tilt (by norm_num)
    (pow_pos (div_pos hL (mul_pos (by norm_num) (Nat.cast_pos.mpr hR))) q)).tendsto.comp
      (tendsto_original_macro_grid_mass hq hR hL)

/-- After the original sample limit, the parent repair tends to zero as the
fixed microscopic side grows. The integer macro normalization is preserved. -/
theorem tendsto_original_macro_grid_repair_microscopic_side {q R : ℕ}
    (hq : 4 < q) (hR : 0 < R) (K C G tilt : ℝ) :
    Tendsto (fun L : ℝ ↦ activeGridRepairError q K C G tilt 1
      ((L / (2 * (R : ℝ))) ^ q)) atTop (𝓝 0) := by
  have hx : Tendsto (fun L : ℝ ↦ L / (2 * (R : ℝ))) atTop atTop :=
    tendsto_id.atTop_div_const (mul_pos (by norm_num) (Nat.cast_pos.mpr hR))
  exact (tendsto_activeGridRepairError_microscopicSide hq K C G tilt (by norm_num)).comp hx

end OTSelector.Reconstruction
