import OTSelector.Reconstruction.BirthPoleDyadicBounds
import OTSelector.Reconstruction.FocalPoleComplianceLegs

/-!
# Both sides of actual short compliance legs in the birth normalizer

Intervals of length comparable with s and endpoint distance comparable with t
have compliance comparable with the same matrix s I + (s/t²) G. A long opposite
leg containing a focal comparison segment also dominates this birth scale.
-/
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integrating the original pole comparison over any short interval in the enlarged
band yields its exact elapsed-time birth scale on both sides. -/
theorem birthPole_short_compliance_bounds
    {W : ℝ → Matrix ι ι ℝ} {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t a b c C : ℝ} (ht : 0 < t) (hab : a ≤ b)
    (ha : t / 2 ≤ a) (hb : b ≤ 4 * t) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hW : ContinuousOn W (Icc (t / 2) (4 * t)))
    (hlower : ∀ r ∈ Icc (t / 2) (4 * t),
      (W r - c • ((r ^ 2)⁻¹ • G + 1)).PosSemidef)
    (hupper : ∀ r ∈ Icc (t / 2) (4 * t),
      (C • ((r ^ 2)⁻¹ • G + 1) - W r).PosSemidef) :
    ((∫ r in a..b, W r) - (c / 16) • birthResidueScale G t (b - a)).PosSemidef ∧
      ((4 * C) • birthResidueScale G t (b - a) - (∫ r in a..b, W r)).PosSemidef := by
  have hsub : Icc a b ⊆ Icc (t / 2) (4 * t) := Icc_subset_Icc ha hb
  have hWi : IntervalIntegrable W volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hW.mono hsub
  have hlow : ∀ r ∈ Icc a b,
      (W r - (c / 16) • ((t ^ 2)⁻¹ • G + 1)).PosSemidef := by
    intro r hr
    have hb' := hsub hr
    have hp := (hlower r hb').add
      ((positivePole_dyadic_model_lower hG ht
        (lt_of_lt_of_le (half_pos ht) hb'.1) hb'.2).smul hc)
    convert hp using 1
    module
  have hupp : ∀ r ∈ Icc a b,
      ((4 * C) • ((t ^ 2)⁻¹ • G + 1) - W r).PosSemidef := by
    intro r hr
    have hb' := hsub hr
    have hp := (hupper r hb').add
      ((positivePole_dyadic_model_upper hG ht hb'.1).smul hC)
    convert hp using 1
    module
  have hl := posSemidef_intervalIntegral hab hlow
  have hu := posSemidef_intervalIntegral hab hupp
  rw [intervalIntegral.integral_sub hWi intervalIntegrable_const,
    intervalIntegral.integral_const] at hl
  rw [intervalIntegral.integral_sub intervalIntegrable_const hWi,
    intervalIntegral.integral_const] at hu
  constructor
  · convert hl using 1
    rw [birthResidueScale_eq_smul_model]
    module
  · convert hu using 1
    rw [birthResidueScale_eq_smul_model]
    module

/-- A true short leg of length between αs and βs has a fixed two-sided bound
in the internally produced canonical birth coordinates. -/
theorem birth_normalized_shortLeg_bounds
    {W : ℝ → Matrix ι ι ℝ} {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t s a b c C α β : ℝ} (ht : 0 < t) (hs : 0 < s) (hab : a ≤ b)
    (ha : t / 2 ≤ a) (hb : b ≤ 4 * t) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlenL : α * s ≤ b - a) (hlenU : b - a ≤ β * s)
    (hW : ContinuousOn W (Icc (t / 2) (4 * t)))
    (hlower : ∀ r ∈ Icc (t / 2) (4 * t),
      (W r - c • ((r ^ 2)⁻¹ • G + 1)).PosSemidef)
    (hupper : ∀ r ∈ Icc (t / 2) (4 * t),
      (C • ((r ^ 2)⁻¹ • G + 1) - W r).PosSemidef) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    (T * (∫ r in a..b, W r) * Tᵀ - (c * α / 16) • 1).PosSemidef ∧
      ((4 * C * β) • 1 - T * (∫ r in a..b, W r) * Tᵀ).PosSemidef := by
  obtain ⟨hl, hu⟩ := birthPole_short_compliance_bounds hG ht hab ha hb hc hC hW hlower hupper
  have hmodel : (((t ^ 2)⁻¹ • G) + 1).PosSemidef :=
    (hG.smul (inv_nonneg.mpr (sq_nonneg t))).add Matrix.PosSemidef.one
  have hl' : ((∫ r in a..b, W r) -
      (c * α / 16) • birthResidueScale G t s).PosSemidef := by
    have hp := hl.add (hmodel.smul
      (mul_nonneg (div_nonneg hc (by norm_num : (0 : ℝ) ≤ 16)) (sub_nonneg.mpr hlenL)))
    convert hp using 1
    simp only [birthResidueScale_eq_smul_model]
    module
  have hu' : ((4 * C * β) • birthResidueScale G t s -
      (∫ r in a..b, W r)).PosSemidef := by
    have hp := hu.add (hmodel.smul
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC) (sub_nonneg.mpr hlenU)))
    convert hp using 1
    simp only [birthResidueScale_eq_smul_model]
    module
  have hscale := birthResidueScale_posDef (t := t) hG hs
  refine ⟨posSemidef_positiveMatrixNormalizer_congruence_lower hscale hl', ?_⟩
  have hp := hu'.mul_mul_conjTranspose_same (positiveMatrixNormalizer (birthResidueScale G t s))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, (positiveMatrixNormalizer_spec hscale).2] using hp

omit [Fintype ι] in
/-- The original focal scale dominates the true birth scale whenever the elapsed time
is no larger than the endpoint distance. -/
theorem focalResidueScale_sub_birth_posSemidef {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t s : ℝ} (ht : 0 < t) (hst : s ≤ t) :
    (focalResidueScale G t - birthResidueScale G t s).PosSemidef := by
  have hmodel : (((t ^ 2)⁻¹ • G) + 1).PosSemidef :=
    (hG.smul (inv_nonneg.mpr (sq_nonneg t))).add Matrix.PosSemidef.one
  have hcoef : t * (t ^ 2)⁻¹ = t⁻¹ := by field_simp
  have heq : focalResidueScale G t = t • ((t ^ 2)⁻¹ • G + 1) := by
    simp only [focalResidueScale, smul_add, smul_smul, hcoef]
    module
  have hp := hmodel.smul (sub_nonneg.mpr hst)
  rw [heq, birthResidueScale_eq_smul_model]
  convert hp using 1
  module

/-- Any actual long leg bounded below by the original focal scale remains bounded below
in these same short elapsed-time birth coordinates. -/
theorem birth_normalized_longLeg_lower
    {G B : Matrix ι ι ℝ} (hG : G.PosSemidef) {t s h : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t) (hh : 0 ≤ h)
    (hB : (B - h • focalResidueScale G t).PosSemidef) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    (T * B * Tᵀ - h • 1).PosSemidef := by
  have hp := hB.add ((focalResidueScale_sub_birth_posSemidef hG ht hst).smul hh)
  have hb : (B - h • birthResidueScale G t s).PosSemidef := by
    convert hp using 1
    module
  exact posSemidef_positiveMatrixNormalizer_congruence_lower
    (birthResidueScale_posDef (t := t) hG hs) hb

end OTSelector.Reconstruction
