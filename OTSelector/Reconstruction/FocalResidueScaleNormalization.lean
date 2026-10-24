import OTSelector.Reconstruction.OriginalFocalFullLegScale
import Mathlib.Analysis.Matrix.Order

/-!
# Internal normalization of the actual focal residue scale

For the actual positive residue G and inward distance t>0, the genuine scale is
`t I+t⁻¹G`. Its positive square-root inverse is constructed internally, proved invertible,
and proved to normalize that same scale exactly. Congruence transfers true full-leg lower
bounds into the fixed positive identity lower bounds used by the original phase geometry.
-/

open Set Matrix
open scoped MatrixOrder Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The focal scale of the actual fixed residue in the unchanged original label frame. -/
def focalResidueScale (G : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ := t•1+t⁻¹•G

omit [Fintype ι] in
/-- The genuine focal scale is positive even when the actual residue has a nontrivial kernel. -/
theorem focalResidueScale_posDef {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t : ℝ} (ht : 0<t) :
    (focalResidueScale G t).PosDef := by
  simpa only [focalResidueScale,add_comm] using
    Matrix.PosDef.posSemidef_add (hG.smul (inv_nonneg.mpr ht.le)) (Matrix.PosDef.one.smul ht)

/-- The canonical positive square-root inverse normalizer of a positive matrix scale. -/
def positiveMatrixNormalizer (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := (CFC.sqrt A)⁻¹

/-- The internally constructed normalizer is invertible and sends its own positive scale
to identity exactly, irrespective of the scale's condition number. -/
theorem positiveMatrixNormalizer_spec {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    IsUnit (positiveMatrixNormalizer A).det ∧
      positiveMatrixNormalizer A*A*(positiveMatrixNormalizer A)ᵀ=1 := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSS : S*S=A := by simpa only [pow_two] using CFC.sq_sqrt A
  have hSt : Sᵀ=S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hdet : S.det≠0 := by
    intro hz
    have h : A.det=0 := by rw [←hSS,Matrix.det_mul,hz,zero_mul]
    exact hA.det_pos.ne' h
  let _ := Matrix.invertibleOfIsUnitDet S (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨S.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr hdet),?_⟩
  change S⁻¹*A*(S⁻¹)ᵀ=1
  have hTt : (S⁻¹)ᵀ=S⁻¹ := by rw [Matrix.transpose_nonsing_inv,hSt]
  rw [hTt,←hSS]
  simp only [Matrix.inv_mul_cancel_left_of_invertible,Matrix.mul_inv_of_invertible]

/-- The same actual scale's lower bound becomes the required identity lower bound in its
internally constructed phase coordinates. -/
theorem posSemidef_positiveMatrixNormalizer_congruence_lower
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) {h : ℝ} (hB : (B-h•A).PosSemidef) :
    (positiveMatrixNormalizer A*B*(positiveMatrixNormalizer A)ᵀ-h•1).PosSemidef := by
  have hb := hB.mul_mul_conjTranspose_same (positiveMatrixNormalizer A)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,(positiveMatrixNormalizer_spec hA).2] using hb

end OTSelector.Reconstruction
