import OTSelector.Reconstruction.OriginalNormalizedPressureLipschitz
import OTSelector.Reconstruction.OriginalDensityWeightedPressureUpper

/-! Retained pressure is read against the unchanged original population root.
The actual retained coordinate density is divided by the ORIGINAL coordinate density. -/
open Filter
open scoped Topology NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The physical retained pressure per unit ORIGINAL root mass. Here theta is
the exact original coordinate intensity and density is the actual retained one. -/
def originalRetainedNormalizedPressure (q theta density : ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  theta⁻¹ * density ^ (1 - 2/q) * p (t * density ^ (2/q))

/-- Losing original mass cannot worsen the common physical probe lower bound.
No original or retained positive lower density bound is required. -/
theorem originalRetainedNormalizedPressure_lower_bound
    {q theta density : ℝ} (hq : 2 < q) (htheta : 0 ≤ theta)
    (hdensity : 0 ≤ density) (hle : density ≤ theta)
    {p : ℝ → ℝ} {G : ℝ≥0} (hLip : LipschitzWith G p) (hzero : 0 ≤ p 0) (t : ℝ) :
    -(|t| * (G : ℝ)) ≤ originalRetainedNormalizedPressure q theta density p t := by
  by_cases hz : theta = 0
  · simp only [originalRetainedNormalizedPressure,hz,inv_zero,zero_mul]
    exact neg_nonpos.mpr (mul_nonneg (abs_nonneg _) G.coe_nonneg)
  have htheta0 : 0 < theta := lt_of_le_of_ne htheta (Ne.symm hz)
  have hq0 : 0 < q := by linarith only [hq]
  have hexp : 0 < 1 - 2/q := sub_pos.mpr ((div_lt_one hq0).mpr hq)
  have hpower : density ^ (1 - 2/q) = density * density ^ (-2/q) := by
    have hh := Real.rpow_add' hdensity
      (show (1:ℝ) + (-2/q) ≠ 0 by convert hexp.ne' using 1; ring)
    simpa only [Real.rpow_one,show (1:ℝ) + (-2/q) = 1 - 2/q by ring] using hh
  have hweight0 : 0 ≤ theta⁻¹ * density := mul_nonneg (inv_nonneg.mpr htheta) hdensity
  have hweight1 : theta⁻¹ * density ≤ 1 := by
    have hh := (div_le_one htheta0).mpr hle
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hlower := mul_le_mul_of_nonneg_left
    (normalized_pressure_lower_bound hdensity hq0 hLip hzero t) hweight0
  have hbase : -(|t| * (G : ℝ)) ≤ (theta⁻¹ * density) * -(|t| * (G : ℝ)) := by
    nlinarith only [hweight1,mul_nonneg (abs_nonneg t) G.coe_nonneg]
  apply hbase.trans
  simpa only [originalRetainedNormalizedPressure,hpower,mul_assoc] using hlower

/-- The true retained-density pressure upper transfers to the unchanged
original population normalization, with its original coordinate intensity.
The case theta=0 is exact zero, not an extra positivity assumption. -/
theorem eventually_originalRetainedNormalizedPressure_lt
    {J : Type*} (l : Filter J) [NeBot l] {q theta : ℝ}
    (hq : 2 < q) (htheta : 0 ≤ theta)
    (p : J → ℝ → ℝ) (pref : ℝ → ℝ) (G : ℝ≥0)
    (hLip : ∀ j, LipschitzWith G (p j))
    (hupper : ∀ t ε, 0 < ε → ∀ᶠ j in l, p j t < pref t + ε)
    (density : J → ℝ) (hdensity : Tendsto density l (𝓝 theta))
    (hdensity0 : ∀ j, 0 ≤ density j) (t : ℝ) :
    ∀ ε > 0, ∀ᶠ j in l,
      originalRetainedNormalizedPressure q theta (density j) (p j) t <
        theta ^ (-2/q) * pref (t * theta ^ (2/q)) + ε := by
  intro ε hε
  by_cases hz : theta = 0
  · have hq0 : 0 < q := by linarith only [hq]
    have hn : (-2/q : ℝ) ≠ 0 := div_ne_zero (by norm_num) hq0.ne'
    simp only [originalRetainedNormalizedPressure,hz,inv_zero,zero_mul,
      Real.zero_rpow hn,zero_add]
    exact Filter.Eventually.of_forall (fun _ ↦ hε)
  have htheta0 : 0 < theta := lt_of_le_of_ne htheta (Ne.symm hz)
  have hscale : theta⁻¹ * theta ^ (1 - 2/q) = theta ^ (-2/q) := by
    calc
      _ = theta ^ (-1:ℝ) * theta ^ (1 - 2/q) := by rw [Real.rpow_neg_one]
      _ = theta ^ ((-1:ℝ) + (1 - 2/q)) := (Real.rpow_add htheta0 _ _).symm
      _ = _ := by congr 1; ring
  filter_upwards [eventually_density_weighted_pressure_lt l hq p pref G hLip hupper
    density theta hdensity hdensity0 t (ε * theta) (mul_pos hε htheta0)] with j hj
  have hh := mul_lt_mul_of_pos_left hj (inv_pos.mpr htheta0)
  have heps : theta⁻¹ * (ε * theta) = ε := by field_simp
  simpa only [originalRetainedNormalizedPressure,mul_add,← mul_assoc,hscale,heps] using hh

end OTSelector.Reconstruction
