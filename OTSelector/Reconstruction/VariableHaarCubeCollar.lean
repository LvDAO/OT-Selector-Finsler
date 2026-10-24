import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary
import Mathlib.Analysis.Real.Sqrt

/-! # Sublinear collars of the actual Haar cubes -/
open Set Function MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
variable (ι : Type*) [Fintype ι]

/-- Exact normalized volume of an inner collar of the original physical cube. -/
theorem haarRootCube_innerCollar_real_ratio
    {R ell k : ℝ} (hR : 0 < R) (hell : 0 ≤ ell) (hk : 0 ≤ k) (hke : k * ell ≤ R) :
    volume.real (haarRootCube ι R \ haarRootCube ι (R - k * ell)) /
      volume.real (haarRootCube ι R) = 1 - (1 - k * (ell / R)) ^ Fintype.card ι := by
  have hsub : haarRootCube ι (R - k * ell) ⊆ haarRootCube ι R :=
    (haarRootCube_shift_shell ι (0 : ι → ℝ) (mul_nonneg hk hell)
      (fun _ ↦ by simpa using mul_nonneg hk hell)).1
  rw [measureReal_sdiff hsub measurableSet_Icc isCompact_Icc.measure_ne_top,
    volume_real_haarRootCube ι hR.le, volume_real_haarRootCube ι (sub_nonneg.mpr hke)]
  rw [sub_div, div_self (pow_ne_zero _ (mul_ne_zero two_ne_zero hR.ne')), ← div_pow]
  congr 2
  field_simp

/-- Any nonnegative collar whose relative width vanishes has vanishing relative
volume, for the same original cubes and in every finite dimension. -/
theorem tendsto_haarRootCube_innerCollar_ratio
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R) {k : ℝ} (hk : 0 ≤ k)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦ volume.real (haarRootCube ι R \ haarRootCube ι (R - k * ell R)) /
      volume.real (haarRootCube ι R)) atTop (𝓝 0) := by
  have hkell : Tendsto (fun R ↦ k * (ell R / R)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsmall
  have hmodel : Tendsto (fun R ↦ 1 - (1 - k * (ell R / R)) ^ Fintype.card ι)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hkell).pow (Fintype.card ι))
  apply hmodel.congr'
  filter_upwards [hell, eventually_gt_atTop (0 : ℝ), hkell.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with R he hR hkR
  exact (haarRootCube_innerCollar_real_ratio ι hR he hk
    (by
      have hkr : (k * ell R) / R < 1 := by rw [mul_div_assoc]; exact hkR
      exact ((div_lt_one hR).mp hkr).le)).symm

/-- The concrete collar square root diverges and occupies vanishing relative width. -/
theorem sqrt_collar_limits :
    Tendsto Real.sqrt atTop atTop ∧
      Tendsto (fun R : ℝ ↦ Real.sqrt R / R) atTop (𝓝 0) := by
  refine ⟨Real.tendsto_sqrt_atTop, ?_⟩
  simpa only [Real.sqrt_div_self, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)

end OTSelector.Reconstruction
