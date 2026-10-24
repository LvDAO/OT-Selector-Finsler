import OTSelector.Reconstruction.PhysicalJacobiMomentWindow

/-! Bounded physical density and continuous original clock factors control the
original conditional density by its actual Jacobi determinant. -/
open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- All coefficients come from the physical density and the closed physical clock;
no positive lower density or prescribed determinant order is used. -/
theorem exists_physical_jacobi_density_determinant_bound
    {J : ℝ → Matrix n n ℝ} {l h R θ κ : ℝ} {ρ w v : ℝ → ℝ}
    (hρ0 : ∀ t ∈ Ioo l h, 0 ≤ ρ t)
    (hρR : ∀ t ∈ Ioo l h, ρ t ≤ R)
    (hw : ContinuousOn w (Icc l h)) (hw0 : ∀ t ∈ Ioo l h, 0 ≤ w t)
    (hv : ContinuousOn v (Icc l h)) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ioo l h,
      0 ≤ (ρ t * w t / θ) * (|v t| * |(J t).det| * κ) ∧
      (ρ t * w t / θ) * (|v t| * |(J t).det| * κ) ≤ K * |(J t).det| := by
  obtain ⟨W₀, hW₀⟩ := isCompact_Icc.bddAbove_image hw
  obtain ⟨V₀, hV₀⟩ := isCompact_Icc.bddAbove_image hv.abs
  let W := max W₀ 0
  let V := max V₀ 0
  let Q := max R 0 * W / θ
  have hW : 0 ≤ W := le_max_right _ _
  have hV : 0 ≤ V := le_max_right _ _
  have hQ : 0 ≤ Q := div_nonneg (mul_nonneg (le_max_right _ _) hW) hθ.le
  refine ⟨Q * V * κ + 1, by positivity, ?_⟩
  intro t ht
  have hwt : w t ≤ W :=
    (hW₀ (mem_image_of_mem _ (Ioo_subset_Icc_self ht))).trans (le_max_left _ _)
  have hvt : |v t| ≤ V :=
    (hV₀ (mem_image_of_mem _ (Ioo_subset_Icc_self ht))).trans (le_max_left _ _)
  have hqt : ρ t * w t / θ ≤ Q :=
    div_le_div_of_nonneg_right
      (mul_le_mul ((hρR t ht).trans (le_max_left _ _)) hwt
        (hw0 t ht) (le_max_right _ _)) hθ.le
  have hq0 : 0 ≤ ρ t * w t / θ :=
    div_nonneg (mul_nonneg (hρ0 t ht) (hw0 t ht)) hθ.le
  refine ⟨mul_nonneg hq0 (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hκ), ?_⟩
  calc
    (ρ t * w t / θ) * (|v t| * |(J t).det| * κ) =
        ((ρ t * w t / θ) * |v t| * κ) * |(J t).det| := by ring
    _ ≤ (Q * V * κ) * |(J t).det| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hqt hvt (abs_nonneg _) hQ) hκ) (abs_nonneg _)
    _ ≤ (Q * V * κ + 1) * |(J t).det| :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg _)

end OTSelector.Reconstruction
