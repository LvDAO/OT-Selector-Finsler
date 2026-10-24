import OTSelector.Reconstruction.ClosedJacobiConditionalMoments
import OTSelector.Geometry.FocalAsymptotics

/-! The actual closed Jacobi system supplies its endpoint determinant rate,
including nullity zero, without a focal-rank hypothesis. -/
open Set Filter Matrix LinearMap
open scoped Topology Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The left endpoint determinant vanishes to exactly its actual nullity order;
this upper estimate includes regular endpoints, whose nullity is zero. -/
theorem ClosedHamiltonianJacobiSystem.exists_left_determinant_power_bound
    {J P A B C : ℝ → Matrix n n ℝ} {l h : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C l h) (hlh : l < h) :
    ∃ ε B : ℝ, 0 < ε ∧ ε < h - l ∧ 0 < B ∧
      ∀ r ∈ Ioo 0 ε,
        |(J (l + r)).det| ≤ B * r ^ Module.finrank ℝ (ker (J l).mulVecLin) := by
  have hl : l ∈ Icc l h := ⟨le_rfl, hlh.le⟩
  have hJ := hasDerivWithinAt_left_inward_parameter
    (H.position_derivative l hl).hasDerivWithinAt
  have hc : ∀ v, J (l + 0) *ᵥ v = 0 →
      (B l * J l + C l * P l) *ᵥ v ∈ LinearMap.range (J (l + 0)).mulVecLin →
      v = 0 := by
    simpa only [add_zero] using
      (fun v hv hr ↦ focal_crossing_kernel_eq_zero
        (H.wronskian l hl) (H.phase_rank l hl) (H.positive_C l hl) hv hr)
  obtain ⟨_, D, _, _, hD, _, hevent⟩ := regular_crossing_bounds hJ hc
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let ε := min δ ((h - l) / 2)
  refine ⟨ε, D, lt_min hδ (half_pos (sub_pos.mpr hlh)),
    (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hlh)), hD, ?_⟩
  intro r hr
  have hb := (hbound ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩).2.1
  change |(J (l + r)).det| ≤ D * |r| ^
    Module.finrank ℝ (ker (J (l + 0)).mulVecLin) at hb
  rw [add_zero, abs_of_pos hr.1] at hb
  exact hb

/-- The right endpoint uses the same actual nullity and inward original time. -/
theorem ClosedHamiltonianJacobiSystem.exists_right_determinant_power_bound
    {J P A B C : ℝ → Matrix n n ℝ} {l h : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C l h) (hlh : l < h) :
    ∃ ε B : ℝ, 0 < ε ∧ ε < h - l ∧ 0 < B ∧
      ∀ r ∈ Ioo 0 ε,
        |(J (h - r)).det| ≤ B * r ^ Module.finrank ℝ (ker (J h).mulVecLin) := by
  have hh : h ∈ Icc l h := ⟨hlh.le, le_rfl⟩
  have hJ := hasDerivWithinAt_right_inward_parameter
    (H.position_derivative h hh).hasDerivWithinAt
  have hc : ∀ v, J (h - 0) *ᵥ v = 0 →
      (-(B h * J h + C h * P h)) *ᵥ v ∈ LinearMap.range (J (h - 0)).mulVecLin →
      v = 0 := by
    simpa only [sub_zero] using matrix_crossing_kernel_condition_neg
      (fun v hv hr ↦ focal_crossing_kernel_eq_zero
        (H.wronskian h hh) (H.phase_rank h hh) (H.positive_C h hh) hv hr)
  obtain ⟨_, D, _, _, hD, _, hevent⟩ := regular_crossing_bounds hJ hc
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let ε := min δ ((h - l) / 2)
  refine ⟨ε, D, lt_min hδ (half_pos (sub_pos.mpr hlh)),
    (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hlh)), hD, ?_⟩
  intro r hr
  have hb := (hbound ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩).2.1
  change |(J (h - r)).det| ≤ D * |r| ^
    Module.finrank ℝ (ker (J (h - 0)).mulVecLin) at hb
  rw [sub_zero, abs_of_pos hr.1] at hb
  exact hb

/-- A density bounded by the actual determinant inherits its left endpoint rate. -/
theorem ClosedHamiltonianJacobiSystem.exists_left_density_power_bound
    {J P A B C : ℝ → Matrix n n ℝ} {l h : ℝ} {f : ℝ → ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C l h) (hlh : l < h)
    (hbound : ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ioo l h,
      0 ≤ f t ∧ f t ≤ K * |(J t).det|) :
    ∃ ε K : ℝ, 0 < ε ∧ ε < h - l ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
      0 ≤ f (l + r) ∧
        f (l + r) ≤ K * r ^ Module.finrank ℝ (ker (J l).mulVecLin) := by
  obtain ⟨K, hK, hcoeff⟩ := hbound
  obtain ⟨ε, D, hε, hεh, hD, hdet⟩ := H.exists_left_determinant_power_bound hlh
  refine ⟨ε, K * D, hε, hεh, mul_pos hK hD, ?_⟩
  intro r hr
  have ht : l + r ∈ Ioo l h := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨(hcoeff _ ht).1, ?_⟩
  exact ((hcoeff _ ht).2.trans
    (mul_le_mul_of_nonneg_left (hdet r hr) hK.le)).trans_eq (by ring)

/-- The analogous right endpoint statement uses inward original time. -/
theorem ClosedHamiltonianJacobiSystem.exists_right_density_power_bound
    {J P A B C : ℝ → Matrix n n ℝ} {l h : ℝ} {f : ℝ → ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C l h) (hlh : l < h)
    (hbound : ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ioo l h,
      0 ≤ f t ∧ f t ≤ K * |(J t).det|) :
    ∃ ε K : ℝ, 0 < ε ∧ ε < h - l ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
      0 ≤ f (h - r) ∧
        f (h - r) ≤ K * r ^ Module.finrank ℝ (ker (J h).mulVecLin) := by
  obtain ⟨K, hK, hcoeff⟩ := hbound
  obtain ⟨ε, D, hε, hεh, hD, hdet⟩ := H.exists_right_determinant_power_bound hlh
  refine ⟨ε, K * D, hε, hεh, mul_pos hK hD, ?_⟩
  intro r hr
  have ht : h - r ∈ Ioo l h := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine ⟨(hcoeff _ ht).1, ?_⟩
  exact ((hcoeff _ ht).2.trans
    (mul_le_mul_of_nonneg_left (hdet r hr) hK.le)).trans_eq (by ring)

end OTSelector.Reconstruction
