import OTSelector.Reconstruction.BirthResidueNormalizerJacobian

/-! The exact physical Haar factor of the actual birth frame at the traffic
coarse scale. The time-window factor cancels, leaving the same residue rank. -/
open Matrix
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The deterministic coarse phase scale for a `q`-dimensional birth window. -/
def birthTrafficCoarseScale (q : ℕ) (t s : ℝ) : ℝ :=
  (Real.sqrt s)⁻¹ * t ^ (-(1 / (q : ℝ)))

/-- The actual coarse scale is positive at positive physical scales. -/
theorem birthTrafficCoarseScale_pos (q : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    0 < birthTrafficCoarseScale q t s := by unfold birthTrafficCoarseScale; positivity

/-- The dimension root has exactly the physical inverse-length dilation power. -/
theorem rpow_inverse_dimension_natPow {q : ℕ} (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (t ^ (-(1 / (q : ℝ)))) ^ q = t⁻¹ := by
  rw [← Real.rpow_mul_natCast ht.le]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : -(1 / (q : ℝ)) * (q : ℝ) = -1 := by field_simp
  rw [he, Real.rpow_neg_one]

/-- The exact scalar traffic dilation cancels the physical birth-window Haar
power, retaining `t^(-rank-1)` from the same original residue. -/
theorem birthTrafficCoarseScale_mul_sqrt_volume {q k : ℕ} (hq : 0 < q)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    birthTrafficCoarseScale q t s ^ q * Real.sqrt (s ^ q / t ^ (2 * k)) =
      (t ^ (k + 1))⁻¹ := by
  have hnum : Real.sqrt (s ^ q) = Real.sqrt s ^ q := by
    simp only [Real.sqrt_eq_rpow, Real.rpow_pow_comm hs.le]
  have hden : Real.sqrt (t ^ (2 * k)) = t ^ k := by
    rw [show 2 * k = k * 2 from Nat.mul_comm _ _, pow_mul, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (pow_nonneg ht.le _)]
  rw [birthTrafficCoarseScale, mul_pow, inv_pow, rpow_inverse_dimension_natPow hq ht,
    Real.sqrt_div (pow_nonneg hs.le _) _, hnum, hden, pow_succ]
  field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual birth-frame inverse Jacobians at the traffic scale have their
internally produced physical rank bound. -/
theorem exists_birthTraffic_scaled_inverseJacobian_bound {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) (hq : 0 < Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s →
      birthTrafficCoarseScale (Fintype.card ι) t s ^ Fintype.card ι *
        |((positiveMatrixNormalizer (birthResidueScale G t s))⁻¹).det| ≤
          C * (t ^ (G.rank + 1))⁻¹ := by
  obtain ⟨c, hc, C, hC, hb⟩ := exists_birthNormalizer_inverse_jacobian_rank_bounds hG
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun t s ht ht1 hs ↦ ?_⟩
  calc
    _ ≤ birthTrafficCoarseScale (Fintype.card ι) t s ^ Fintype.card ι *
        (Real.sqrt C * Real.sqrt (s ^ Fintype.card ι / t ^ (2 * G.rank))) :=
      mul_le_mul_of_nonneg_left (hb t s ht ht1 hs).2
        (pow_nonneg (birthTrafficCoarseScale_pos _ ht hs).le _)
    _ = Real.sqrt C * (birthTrafficCoarseScale (Fintype.card ι) t s ^ Fintype.card ι *
        Real.sqrt (s ^ Fintype.card ι / t ^ (2 * G.rank))) := by ring
    _ = _ := by rw [birthTrafficCoarseScale_mul_sqrt_volume hq ht hs]

/-- The actual physical birth frame used to pull a bounded phase box back to
original source space, retaining both its traffic dilation and its canonical frame. -/
def birthTrafficSpatialFrame (G : Matrix ι ι ℝ) (t s : ℝ) : Matrix ι ι ℝ :=
  birthTrafficCoarseScale (Fintype.card ι) t s • (positiveMatrixNormalizer (birthResidueScale G t s))⁻¹

/-- The actual original frame is invertible; no separate frame oracle is supplied. -/
theorem birthTrafficSpatialFrame_isUnit_det {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) : IsUnit (birthTrafficSpatialFrame G t s).det := by
  have hN := (positiveMatrixNormalizer_spec (birthResidueScale_posDef (t := t) hG hs)).1
  have hNi := (positiveMatrixNormalizer (birthResidueScale G t s)).isUnit_nonsing_inv_det hN
  rw [birthTrafficSpatialFrame, Matrix.det_smul]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (birthTrafficCoarseScale_pos _ ht hs).ne')).mul hNi

/-- Exact physical Haar determinant of this same actual birth frame. -/
theorem birthTrafficSpatialFrame_abs_det {G : Matrix ι ι ℝ} {t s : ℝ}
    (ht : 0 < t) (hs : 0 < s) :
    |(birthTrafficSpatialFrame G t s).det| =
      birthTrafficCoarseScale (Fintype.card ι) t s ^ Fintype.card ι *
        |((positiveMatrixNormalizer (birthResidueScale G t s))⁻¹).det| := by
  rw [birthTrafficSpatialFrame, Matrix.det_smul, abs_mul, abs_pow,
    abs_of_pos (birthTrafficCoarseScale_pos _ ht hs)]

/-- The actual same-residue physical source frame has the precise rank-plus-one
upper Haar power needed by the unchanged original birth-band input intensity. -/
theorem exists_birthTrafficSpatialFrame_det_bound {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) (hq : 0 < Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ t s : ℝ, 0 < t → t ≤ 1 → 0 < s →
      |(birthTrafficSpatialFrame G t s).det| ≤ C * (t ^ (G.rank + 1))⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_birthTraffic_scaled_inverseJacobian_bound hG hq
  exact ⟨C, hC, fun t s ht ht1 hs ↦ by rw [birthTrafficSpatialFrame_abs_det ht hs]; exact hb t s ht ht1 hs⟩

end OTSelector.Reconstruction
