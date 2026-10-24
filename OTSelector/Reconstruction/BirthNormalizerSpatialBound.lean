import OTSelector.Reconstruction.BirthResidueNormalizedMomentum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The actual birth normalizer controls unchanged physical positions by a
dimension constant and the inverse square root of the elapsed scale. -/
open Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual normalizer's own scale identity bounds its row Gram matrix. -/
theorem birthNormalizer_scaledGram_le_identity {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t s : ℝ} (hs : 0 < s) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    (1 - s • (T * Tᵀ)).PosSemidef := by
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  have hA := birthResidueScale_posDef (t := t) hG hs
  have hlow : (birthResidueScale G t s - s • 1).PosSemidef := by
    simpa only [birthResidueScale, add_sub_cancel_left] using
      hG.smul (div_nonneg hs.le (sq_nonneg t))
  have h := hlow.mul_mul_conjTranspose_same T
  have hn : T * birthResidueScale G t s * Tᵀ = 1 :=
    (positiveMatrixNormalizer_spec hA).2
  change (1 - s • (T * Tᵀ)).PosSemidef
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hn] using h

/-- Each row of the same actual birth normalizer has squared length at most `1/s`. -/
theorem birthNormalizer_row_sq_bound {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t s : ℝ} (hs : 0 < s) (i : ι) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    s * (∑ j, T i j ^ 2) ≤ 1 := by
  have h := (birthNormalizer_scaledGram_le_identity (t := t) hG hs).diag_nonneg (i := i)
  have hd : 0 ≤ 1 - s * (∑ j,
      positiveMatrixNormalizer (birthResidueScale G t s) i j ^ 2) := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  linarith

/-- Canonical birth coordinates of any physical vector have a dimension-only
bound; no norm bound for an independently chosen frame is supplied. -/
theorem birthNormalizer_mulVec_norm_le {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t s : ℝ} (hs : 0 < s) (x : ι → ℝ) :
    ‖positiveMatrixNormalizer (birthResidueScale G t s) *ᵥ x‖ ≤
      Real.sqrt (Fintype.card ι : ℝ) * ‖x‖ / Real.sqrt s := by
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hq : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hsq := Real.sq_sqrt hs.le
  have hqsq := Real.sq_sqrt hq
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hrow := birthNormalizer_row_sq_bound (t := t) hG hs i
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (T i) x
  have hcomponent : s * ((T *ᵥ x) i) ^ 2 ≤ ∑ j, x j ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hc hs.le
    have hlast := mul_le_mul_of_nonneg_right hrow
      (show 0 ≤ ∑ j : ι, x j ^ 2 from Finset.sum_nonneg (fun j _ ↦ sq_nonneg (x j)))
    change s * (∑ j, T i j * x j) ^ 2 ≤ _
    nlinarith
  have hsum := sum_sq_le_card_mul_pi_norm_sq x
  have hprod : Real.sqrt s * |(T *ᵥ x) i| ≤
      Real.sqrt (Fintype.card ι : ℝ) * ‖x‖ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_abs ((T *ᵥ x) i)]
  exact (le_div_iff₀ hsqrt).mpr (by nlinarith [hprod])

/-- An unchanged physical ball maps into the corresponding deterministic birth ball. -/
theorem birthNormalizer_mulVec_norm_le_of_norm_le {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t s R : ℝ} (hs : 0 < s) {x : ι → ℝ} (hx : ‖x‖ ≤ R) :
    ‖positiveMatrixNormalizer (birthResidueScale G t s) *ᵥ x‖ ≤
      (Real.sqrt (Fintype.card ι : ℝ) / Real.sqrt s) * R := by
  calc
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖x‖ / Real.sqrt s :=
      birthNormalizer_mulVec_norm_le hG hs x
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) * R / Real.sqrt s := by
      gcongr
    _ = _ := by ring

end OTSelector.Reconstruction
