import OTSelector.Reconstruction.VariableHaarCubeCollar

/-! # Finite original count bounds normalized by their own Haar volume -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000
variable (ι : Type*) [Fintype ι]

/-- Convert an actual finite collar-and-tail count bound to its normalized real
mean. Finiteness of the count is derived from that same bound. -/
theorem finite_and_normalized_count_le_haarCube_collar_tail
    {R ell k : ℝ} (hR : 0 < R) (hell : 0 ≤ ell) (hk : 0 ≤ k) (hke : k * ell ≤ R)
    {z tail : ℝ≥0∞} (htail : tail ≠ ∞)
    (hz : z ≤ volume (haarRootCube ι R \ haarRootCube ι (R - k * ell)) +
      volume (haarRootCube ι R) * tail) :
    z ≠ ∞ ∧ z.toReal / volume.real (haarRootCube ι R) ≤
      1 - (1 - k * (ell / R)) ^ Fintype.card ι + tail.toReal := by
  have hvol : volume (haarRootCube ι R) ≠ ∞ := isCompact_Icc.measure_ne_top
  have hcollar : volume (haarRootCube ι R \ haarRootCube ι (R - k * ell)) ≠ ∞ :=
    measure_ne_top_of_subset sdiff_subset hvol
  have hproduct : volume (haarRootCube ι R) * tail ≠ ∞ := ENNReal.mul_ne_top hvol htail
  have hrhs : volume (haarRootCube ι R \ haarRootCube ι (R - k * ell)) +
      volume (haarRootCube ι R) * tail ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hcollar, hproduct⟩
  have hfinite : z ≠ ∞ := ne_top_of_le_ne_top hrhs hz
  have hzreal := ENNReal.toReal_mono hrhs hz
  rw [ENNReal.toReal_add hcollar hproduct, ENNReal.toReal_mul] at hzreal
  have hpos : 0 < volume.real (haarRootCube ι R) := by
    rw [volume_real_haarRootCube ι hR.le]
    positivity
  refine ⟨hfinite, ?_⟩
  calc
    _ ≤ (volume.real (haarRootCube ι R \ haarRootCube ι (R - k * ell)) +
        volume.real (haarRootCube ι R) * tail.toReal) /
          volume.real (haarRootCube ι R) := div_le_div_of_nonneg_right hzreal hpos.le
    _ = volume.real (haarRootCube ι R \ haarRootCube ι (R - k * ell)) /
        volume.real (haarRootCube ι R) + tail.toReal := by field_simp
    _ = _ := by rw [haarRootCube_innerCollar_real_ratio ι hR hell hk hke]

/-- A sublinear collar eventually fits inside the original cube. -/
theorem eventually_collar_mul_le_radius
    {ell : ℝ → ℝ} {k : ℝ}
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    ∀ᶠ R in atTop, k * ell R ≤ R := by
  have h : Tendsto (fun R ↦ k * (ell R / R)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsmall
  filter_upwards [eventually_gt_atTop (0 : ℝ), h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with R hR hkR
  have hkr : (k * ell R) / R < 1 := by rw [mul_div_assoc]; exact hkR
  exact ((div_lt_one hR).mp hkr).le

end OTSelector.Reconstruction
