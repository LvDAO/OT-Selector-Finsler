import OTSelector.Reconstruction.BirthResidueNormalizedMomentum
import OTSelector.LinearAlgebra.Matrix.PositiveResidueVelocity

/-! The actual birth-normalized momentum and physical double-pole velocity
have the joint energy scale needed by Campbell, with the same positive residue. -/
open Set Function Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The physical inverse square-root time power is the reciprocal of its own
positive real square root. -/
theorem rpow_neg_half_eq_inv_sqrt {t : ℝ} (ht : 0 < t) :
    t ^ (-1 / 2 : ℝ) = (Real.sqrt t)⁻¹ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ht.le,
    ← Real.sqrt_eq_rpow]

/-- The two physical momentum/velocity scales multiply to the original
energy density `sqrt s * (e/t² + v²/t)`. -/
theorem birth_momentum_velocity_product_bound
    {t s e v P V A C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (_hs : 0 ≤ s)
    (he : 0 ≤ e) (hv : 0 ≤ v) (hV : 0 ≤ V) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hP : P ≤ A * Real.sqrt s * (t ^ (-1 / 2 : ℝ) * Real.sqrt e + v))
    (hW : V ≤ C * (t ^ (-3 / 2 : ℝ) * Real.sqrt e + v)) :
    P * V ≤ 2 * A * C * Real.sqrt s * (e / t ^ 2 + v ^ 2 / t) := by
  let x := t ^ (-1 / 2 : ℝ) * Real.sqrt e
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hpow : t ^ (-3 / 2 : ℝ) = t⁻¹ * t ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    norm_num
  have hW' : V ≤ C * ((x + v) / t) := by
    apply hW.trans
    apply mul_le_mul_of_nonneg_left _ hC
    rw [hpow]
    dsimp [x]
    have hv' : v ≤ v / t := (le_div_iff₀ ht).mpr (by nlinarith)
    calc
      _ ≤ t⁻¹ * t ^ (-1 / 2 : ℝ) * Real.sqrt e + v / t :=
        add_le_add le_rfl hv'
      _ = _ := by ring
  have hxsq : x ^ 2 = e / t := by
    dsimp [x]
    rw [rpow_neg_half_eq_inv_sqrt ht, mul_pow, inv_pow,
      Real.sq_sqrt ht.le, Real.sq_sqrt he]
    ring
  have hsum : (x + v) ^ 2 ≤ 2 * (e / t + v ^ 2) := by
    nlinarith [sq_nonneg (x - v)]
  calc
    P * V ≤ (A * Real.sqrt s * (x + v)) * (C * ((x + v) / t)) :=
      mul_le_mul hP hW' hV (by positivity)
    _ = (A * C * Real.sqrt s / t) * (x + v) ^ 2 := by ring
    _ ≤ (A * C * Real.sqrt s / t) * (2 * (e / t + v ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The canonical actual inverse-transpose birth momentum admits a fixed
same-residue coefficient in the square-root source-energy scale. -/
theorem birthNormalizer_momentum_le_sqrt_source_energy
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s a : ℝ}
    (ht : 0 < t) (hs : 0 < s) (ha : 0 < a) (hat : a ≤ 2 * t) (p : ι → ℝ) :
    ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ ≤
      (Real.sqrt (Fintype.card ι : ℝ) + Real.sqrt 2) * Real.sqrt s *
        (t ^ (-1 / 2 : ℝ) * Real.sqrt ((p ⬝ᵥ (G *ᵥ p)) / a) + ‖p‖) := by
  have he : 0 ≤ (p ⬝ᵥ (G *ᵥ p)) / a :=
    div_nonneg (by simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg p) ha.le
  have hscale : Real.sqrt (2 / t) = Real.sqrt 2 * t ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_div (by norm_num), rpow_neg_half_eq_inv_sqrt ht]
    rfl
  have h := birthResidueNormalizer_momentum_norm_le hG ht hs ha hat p
  rw [hscale] at h
  apply h.trans
  have hx : 0 ≤ t ^ (-1 / 2 : ℝ) * Real.sqrt ((p ⬝ᵥ (G *ᵥ p)) / a) := by positivity
  nlinarith [mul_nonneg (Real.sqrt_nonneg (Fintype.card ι : ℝ)) hx,
    mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg p),
    mul_nonneg (Real.sqrt_nonneg s)
      (mul_nonneg (Real.sqrt_nonneg (Fintype.card ι : ℝ)) hx),
    mul_nonneg (Real.sqrt_nonneg s)
      (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg p))]

/-- Actual canonical birth momentum times its physical velocity is controlled
by the same original residue energy and full unchanged momentum. -/
theorem birthNormalizer_momentum_mul_velocity_le
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s a C V : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (ha : 0 < a) (hat : a ≤ 2 * t)
    (hC : 0 ≤ C) (hV : 0 ≤ V) (p : ι → ℝ)
    (hvel : V ≤ C * (t ^ (-3 / 2 : ℝ) * Real.sqrt ((p ⬝ᵥ (G *ᵥ p)) / a) + ‖p‖)) :
    ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ p‖ * V ≤
      (2 * (Real.sqrt (Fintype.card ι : ℝ) + Real.sqrt 2) * C) * Real.sqrt s *
        (((p ⬝ᵥ (G *ᵥ p)) / a) / t ^ 2 + ‖p‖ ^ 2 / t) := by
  exact birth_momentum_velocity_product_bound ht ht1 hs.le
    (div_nonneg (by simpa only [star_trivial] using hG.dotProduct_mulVec_nonneg p) ha.le)
    (norm_nonneg p) hV (by positivity) hC
    (birthNormalizer_momentum_le_sqrt_source_energy hG ht hs ha hat p) hvel

end OTSelector.Reconstruction
