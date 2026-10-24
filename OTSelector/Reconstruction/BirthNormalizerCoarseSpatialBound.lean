import OTSelector.Reconstruction.BirthNormalizerSpatialBound
import OTSelector.Reconstruction.BirthTrafficPhysicalHaarScale

/-! The actual canonical birth frame puts every original physical compact
support inside one dimension-controlled ball at the traffic coarse scale. -/
open Matrix
open scoped Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- For physical inward scale at most one, the actual coarse scale dominates `1/√s`. -/
theorem inv_sqrt_le_birthTrafficCoarseScale (q : ℕ) {t s : ℝ}
    (ht : 0 < t) (htone : t ≤ 1) :
    (Real.sqrt s)⁻¹ ≤ birthTrafficCoarseScale q t s := by
  have hp : 1 ≤ t ^ (-(1 / (q : ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht htone (neg_nonpos.mpr (by positivity))
  exact le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg s)) hp

/-- The unchanged coarse traffic scale is at least one at every physical birth scale. -/
theorem one_le_birthTrafficCoarseScale (q : ℕ) {t s : ℝ}
    (ht : 0 < t) (htone : t ≤ 1) (hs : 0 < s) (hst : s ≤ t) :
    1 ≤ birthTrafficCoarseScale q t s := by
  have hroot : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr (hst.trans htone)
  have hinv : 1 ≤ (Real.sqrt s)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hs)).mpr
    simpa only [one_mul] using hroot
  exact hinv.trans (inv_sqrt_le_birthTrafficCoarseScale q ht htone)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The same canonical normalizer satisfies the required uniform coarse spatial bound. -/
theorem birthNormalizer_mulVec_norm_le_coarseScale {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t s : ℝ} (ht : 0 < t) (htone : t ≤ 1)
    (hs : 0 < s) (x : ι → ℝ) :
    ‖positiveMatrixNormalizer (birthResidueScale G t s) *ᵥ x‖ ≤
      Real.sqrt (Fintype.card ι : ℝ) * ‖x‖ * birthTrafficCoarseScale (Fintype.card ι) t s := by
  calc
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖x‖ / Real.sqrt s :=
      birthNormalizer_mulVec_norm_le hG hs x
    _ = (Real.sqrt s)⁻¹ * (Real.sqrt (Fintype.card ι : ℝ) * ‖x‖) := by ring
    _ ≤ birthTrafficCoarseScale (Fintype.card ι) t s *
        (Real.sqrt (Fintype.card ι : ℝ) * ‖x‖) :=
      mul_le_mul_of_nonneg_right (inv_sqrt_le_birthTrafficCoarseScale _ ht htone)
        (by positivity)
    _ = _ := by ring

/-- One original physical radius has one deterministic coarse normalized radius. -/
theorem birthNormalizer_mulVec_norm_le_coarseScale_of_norm_le {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t s R : ℝ} (ht : 0 < t) (htone : t ≤ 1)
    (hs : 0 < s) {x : ι → ℝ} (hx : ‖x‖ ≤ R) :
    ‖positiveMatrixNormalizer (birthResidueScale G t s) *ᵥ x‖ ≤
      Real.sqrt (Fintype.card ι : ℝ) * R * birthTrafficCoarseScale (Fintype.card ι) t s := by
  exact (birthNormalizer_mulVec_norm_le_coarseScale hG ht htone hs x).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _))
      (birthTrafficCoarseScale_pos _ ht hs).le)

/-- The coordinate dimension alone supplies the spatial constant, including
the empty coordinate space; no residue norm or condition number is an input. -/
theorem exists_birthNormalizer_spatial_coarseScale_bound (q : ℕ) :
    ∃ C ≥ 0, ∀ {G : Matrix (Fin q) (Fin q) ℝ}, G.PosSemidef →
      ∀ {t s R : ℝ}, 0 < t → t ≤ 1 → 0 < s → s ≤ t →
      ∀ {x : Fin q → ℝ}, ‖x‖ ≤ R →
        1 ≤ birthTrafficCoarseScale q t s ∧
        ‖positiveMatrixNormalizer (birthResidueScale G t s) *ᵥ x‖ ≤
          C * R * birthTrafficCoarseScale q t s := by
  refine ⟨Real.sqrt (q : ℝ), Real.sqrt_nonneg _, ?_⟩
  intro G hG t s R ht htone hs hst x hx
  exact ⟨one_le_birthTrafficCoarseScale q ht htone hs hst,
    by simpa only [Fintype.card_fin] using
      birthNormalizer_mulVec_norm_le_coarseScale_of_norm_le hG ht htone hs hx⟩

end OTSelector.Reconstruction
