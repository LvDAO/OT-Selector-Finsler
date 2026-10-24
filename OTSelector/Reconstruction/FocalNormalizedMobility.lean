import OTSelector.Reconstruction.FocalResidueScaleNormalization

/-!
# Mobility in the actual focal residue scale

The same scale which normalizes the true full compliance legs also controls the original
kernel throughout a dyadic inward-distance band. Both inequalities follow from Loewner
comparison; no eigenbasis or condition-number bound is needed.
-/

open Set Matrix
open scoped MatrixOrder Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- On the dyadic band, the true pole upper bound is controlled by the same focal scale. -/
theorem focalResidueScale_mobility_upper {G W : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t s C : ℝ} (ht : 0<t) (hts : t/2≤s) (hC : 0≤C)
    (hW : (C•((s^2)⁻¹•G+1)-W).PosSemidef) :
    ((4*C)•focalResidueScale G t-t•W).PosSemidef := by
  have hs : 0<s := lt_of_lt_of_le (half_pos ht) hts
  have hcoeff : 0≤4*t⁻¹-t*(s^2)⁻¹ := by
    have hsq : t^2≤4*s^2 := by nlinarith
    have h : t/s^2≤4/t := (div_le_div_iff₀ (sq_pos_of_pos hs) ht).mpr (by nlinarith [hsq])
    simpa only [div_eq_mul_inv,mul_comm] using sub_nonneg.mpr h
  have hh := ((hW.smul ht.le).add
    (Matrix.PosSemidef.one.smul (mul_nonneg (by norm_num : (0:ℝ)≤3) (mul_nonneg hC ht.le)))).add
      (hG.smul (mul_nonneg hC hcoeff))
  convert hh using 1
  unfold focalResidueScale
  module

/-- Congruence by the internally constructed scale inverse gives a fixed mobility upper bound. -/
theorem focal_normalized_mobility_upper {G W : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {t s C : ℝ} (ht : 0<t) (hts : t/2≤s) (hC : 0≤C)
    (hW : (C•((s^2)⁻¹•G+1)-W).PosSemidef) :
    let T := positiveMatrixNormalizer (focalResidueScale G t)
    ((4*C)•1-t•(T*W*Tᵀ)).PosSemidef := by
  have hu := focalResidueScale_mobility_upper hG ht hts hC hW
  have hh := hu.mul_mul_conjTranspose_same (positiveMatrixNormalizer (focalResidueScale G t))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,
    (positiveMatrixNormalizer_spec (focalResidueScale_posDef hG ht)).2] using hh

/-- A fixed original kernel upper-comparison constant gives one norm bound for every
normalized scale and every point of its dyadic inward-distance band. -/
theorem exists_norm_bound_focal_normalized_mobility (C : ℝ) :
    ∃ R≥0, ∀{G W : Matrix ι ι ℝ}, G.PosSemidef → W.PosSemidef →
      ∀{t s : ℝ}, 0<t → t/2≤s → 0≤C →
      (C•((s^2)⁻¹•G+1)-W).PosSemidef →
      ‖t•(positiveMatrixNormalizer (focalResidueScale G t)*W*
        (positiveMatrixNormalizer (focalResidueScale G t))ᵀ)‖≤R := by
  obtain ⟨R,hR,hbound⟩ := exists_norm_bound_of_posSemidef_trace_le
    (n:=ι) (4*C*(Fintype.card ι:ℝ))
  refine ⟨R,hR,fun {G W} hG hW {t s} ht hts hC hupper ↦ ?_⟩
  let T := positiveMatrixNormalizer (focalResidueScale G t)
  have hN : (t•(T*W*Tᵀ)).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hW.mul_mul_conjTranspose_same T).smul ht.le
  apply hbound _ hN
  have htrace := (focal_normalized_mobility_upper hG ht hts hC hupper).trace_nonneg
  simp only [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,smul_eq_mul] at htrace
  change (t•(T*W*Tᵀ)).trace≤4*C*(Fintype.card ι:ℝ)
  rw [Matrix.trace_smul,smul_eq_mul]
  linarith

/-- Replacing the shell scale by any actual distance in its dyadic band costs at most two. -/
theorem norm_smul_le_two_mul_of_dyadic_band
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : V} {t s R : ℝ} (ht : 0<t) (hs : 0≤s) (hst : s≤2*t)
    (hbound : ‖t•v‖≤R) : ‖s•v‖≤2*R := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hbound
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  nlinarith [norm_nonneg v]

end OTSelector.Reconstruction
