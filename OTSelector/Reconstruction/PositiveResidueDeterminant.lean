import OTSelector.Reconstruction.FocalResidueScaleNormalization
import Mathlib.Analysis.Matrix.PosDef

/-!
# Determinant scaling of the genuine positive focal residue scale

The nonzero eigenvalues of an arbitrary positive semidefinite residue determine the
exact determinant power of `t I + t⁻¹ G`. No nonsingularity or positive rank is required.
-/

open Matrix
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of a scalar affine function of a Hermitian matrix in its own
orthonormal eigenbasis. -/
theorem det_smul_one_add_smul_of_isHermitian {G : Matrix ι ι ℝ}
    (hG : G.IsHermitian) (a b : ℝ) :
    (a • (1 : Matrix ι ι ℝ) + b • G).det =
      ∏ i, (a + b * hG.eigenvalues i) := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hG.eigenvectorUnitary
  have hGd : G = e (Matrix.diagonal hG.eigenvalues) := by
    simpa [e] using hG.spectral_theorem
  have hd : a • (1 : Matrix ι ι ℝ) + b • G =
      e (Matrix.diagonal (fun i ↦ a + b * hG.eigenvalues i)) := by
    conv_lhs => rhs; rw [hGd]
    have hi : a • (1 : Matrix ι ι ℝ) + b • Matrix.diagonal hG.eigenvalues =
        Matrix.diagonal (fun i ↦ a + b * hG.eigenvalues i) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [← map_one e, ← map_smul, ← map_smul, ← map_add, hi]
  rw [hd]
  change ((hG.eigenvectorUnitary : Matrix ι ι ℝ) * _ *
    (star hG.eigenvectorUnitary : Matrix ι ι ℝ)).det = _
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.det_one, one_mul,
    Matrix.det_diagonal]

omit [DecidableEq ι] in
/-- Exact finite product decomposition into the zero and nonzero eigendirections. -/
theorem prod_focal_factors (eig : ι → ℝ) {t : ℝ} (ht : t ≠ 0) :
    (∏ i, (t + t⁻¹ * eig i)) =
      (t ^ Fintype.card ι / t ^ (2 * Fintype.card {i // eig i ≠ 0})) *
        ∏ i : {i // eig i ≠ 0}, (t ^ 2 + eig i) := by
  classical
  let N := {i // eig i ≠ 0}
  let Z := {i // ¬eig i ≠ 0}
  have hcard : Fintype.card Z + Fintype.card N = Fintype.card ι := by
    dsimp [Z, N]
    rw [Fintype.card_subtype_compl,
      Nat.sub_add_cancel (Fintype.card_subtype_le (fun i ↦ eig i ≠ 0))]
  have hzero : (∏ i : Z, (t + t⁻¹ * eig i)) = t ^ Fintype.card Z := by
    have hi : ∀ i : Z, eig i = 0 := fun i ↦ not_ne_iff.mp i.property
    simp [hi]
  have hnonzero : (∏ i : N, (t + t⁻¹ * eig i)) =
      (t⁻¹) ^ Fintype.card N * ∏ i : N, (t ^ 2 + eig i) := by
    calc
      (∏ i : N, (t + t⁻¹ * eig i)) =
          ∏ i : N, (t⁻¹ * (t ^ 2 + eig i)) := by
        apply Finset.prod_congr rfl
        intro i _
        field_simp [ht]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hsplit := Fintype.prod_subtype_mul_prod_subtype
    (fun i ↦ eig i ≠ 0) (fun i ↦ t + t⁻¹ * eig i)
  rw [← hsplit, hzero, hnonzero]
  have hp : t ^ Fintype.card ι / t ^ (2 * Fintype.card N) =
      t ^ Fintype.card Z * (t⁻¹) ^ Fintype.card N := by
    rw [← hcard, pow_add, two_mul, pow_add, inv_pow]
    field_simp [ht]
  rw [hp]
  ring

/-- The precise determinant factorization uses the rank of the actual residue. -/
theorem focalResidueScale_det_factorization {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t : ℝ} (ht : t ≠ 0) :
    (focalResidueScale G t).det =
      (t ^ Fintype.card ι / t ^ (2 * G.rank)) *
        ∏ i : {i // hG.isHermitian.eigenvalues i ≠ 0},
          (t ^ 2 + hG.isHermitian.eigenvalues i) := by
  rw [focalResidueScale, det_smul_one_add_smul_of_isHermitian hG.isHermitian,
    prod_focal_factors _ ht, hG.isHermitian.rank_eq_card_non_zero_eigs]

/-- The determinant has exactly the power dictated by the dimension and the rank of
its positive residue; the constants also work for rank zero and dimension zero. -/
theorem exists_focalResidueScale_det_rank_bounds {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      c * (t ^ Fintype.card ι / t ^ (2 * G.rank)) ≤ (focalResidueScale G t).det ∧
      (focalResidueScale G t).det ≤ C * (t ^ Fintype.card ι / t ^ (2 * G.rank)) := by
  classical
  let N := {i // hG.isHermitian.eigenvalues i ≠ 0}
  let c : ℝ := ∏ i : N, hG.isHermitian.eigenvalues i
  let C : ℝ := ∏ i : N, (1 + hG.isHermitian.eigenvalues i)
  have hc : 0 < c := by
    apply Finset.prod_pos
    intro i _
    exact (hG.eigenvalues_nonneg i).lt_of_ne' i.property
  have hC : 0 < C := by
    apply Finset.prod_pos
    intro i _
    have hi := hG.eigenvalues_nonneg i
    linarith
  refine ⟨c, hc, C, hC, ?_⟩
  intro t ht ht1
  have hs : 0 < t ^ Fintype.card ι / t ^ (2 * G.rank) :=
    div_pos (pow_pos ht _) (pow_pos ht _)
  have hl : c ≤ ∏ i : N, (t ^ 2 + hG.isHermitian.eigenvalues i) := by
    apply Finset.prod_le_prod
    · intro i _
      exact hG.eigenvalues_nonneg i
    · intro i _
      nlinarith [sq_nonneg t]
  have hu : (∏ i : N, (t ^ 2 + hG.isHermitian.eigenvalues i)) ≤ C := by
    apply Finset.prod_le_prod
    · intro i _
      have hi := hG.eigenvalues_nonneg i
      nlinarith [sq_nonneg t]
    · intro i _
      nlinarith
  rw [focalResidueScale_det_factorization hG ht.ne']
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl hs.le
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu hs.le

end OTSelector.Reconstruction
