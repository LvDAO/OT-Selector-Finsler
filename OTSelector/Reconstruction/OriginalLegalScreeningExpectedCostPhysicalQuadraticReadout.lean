import OTSelector.Reconstruction.OriginalLegalScreeningComparatorFocalCost

/-! One physical repair constant also controls the actual finite-value quadratic bound. -/
open Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- The same physical signed repair bound controls the nonnegative kinetic
without choosing another constant. This preserves the order in which the
constant, tilt, matching and reserve intensity are selected. -/
theorem originalScreening_quadratic_bound_of_physical_cost
    {q : ℕ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {C G : ℝ}
    (hk0 : ∀ a d v, 0 ≤ kin a d v)
    (hphysical : ∀ (a d : ℝ) (x y : Fin q → ℝ) (t : ℝ),
      kin a d (y-x)-t*g a d ≤
        C*dist ((EuclideanSpace.equiv _ ℝ).symm x) ((EuclideanSpace.equiv _ ℝ).symm y)^2+|t| * G) :
    ∀ a d v, |kin a d v| ≤ C*∑ i, v i^2 := by
  intro a d v
  have h := hphysical a d 0 v 0
  simp only [sub_zero,zero_mul,abs_zero,add_zero] at h
  have hd : dist ((EuclideanSpace.equiv (Fin q) ℝ).symm 0)
      ((EuclideanSpace.equiv (Fin q) ℝ).symm v)^2 = ∑ i, v i^2 := by
    rw [map_zero,dist_zero_left,EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Real.norm_eq_abs,sq_abs]
    rfl
  rw [hd] at h
  exact (abs_of_nonneg (hk0 a d v)).le.trans h

end OTSelector.Reconstruction
