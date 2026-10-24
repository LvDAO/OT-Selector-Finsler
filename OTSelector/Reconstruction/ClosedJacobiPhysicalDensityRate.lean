import OTSelector.Reconstruction.ClosedJacobiEndpointDeterminantRate
import OTSelector.Reconstruction.PhysicalJacobiDensityDeterminantBound

/-! Endpoint power rates for the original physical density, with the nullity of
the same actual physical-time Jacobi matrix. -/
open Set Matrix LinearMap
open scoped Topology Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The physical density inherits the actual left determinant rate. -/
theorem ClosedHamiltonianJacobiSystem.exists_left_physical_density_power_bound
    {J P A B C : ℝ → Matrix n n ℝ} {l h R θ κ : ℝ} {ρ w v : ℝ → ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C l h) (hlh : l < h)
    (hρ0 : ∀ t ∈ Ioo l h, 0 ≤ ρ t)
    (hρR : ∀ t ∈ Ioo l h, ρ t ≤ R)
    (hw : ContinuousOn w (Icc l h)) (hw0 : ∀ t ∈ Ioo l h, 0 ≤ w t)
    (hv : ContinuousOn v (Icc l h)) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    ∃ ε K : ℝ, 0 < ε ∧ ε < h - l ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
      0 ≤ (ρ (l + r) * w (l + r) / θ) *
        (|v (l + r)| * |(J (l + r)).det| * κ) ∧
      (ρ (l + r) * w (l + r) / θ) *
        (|v (l + r)| * |(J (l + r)).det| * κ) ≤
          K * r ^ Module.finrank ℝ (ker (J l).mulVecLin) := by
  obtain ⟨K, hK, hcoeff⟩ := exists_physical_jacobi_density_determinant_bound
    (J := J) hρ0 hρR hw hw0 hv hθ hκ
  obtain ⟨ε, D, hε, hεh, hD, hdet⟩ := H.exists_left_determinant_power_bound hlh
  refine ⟨ε, K * D, hε, hεh, mul_pos hK hD, ?_⟩
  intro r hr
  have ht : l + r ∈ Ioo l h := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨(hcoeff _ ht).1, ?_⟩
  calc
    _ ≤ K * |(J (l + r)).det| := (hcoeff _ ht).2
    _ ≤ K * (D * r ^ Module.finrank ℝ (ker (J l).mulVecLin)) :=
      mul_le_mul_of_nonneg_left (hdet r hr) hK.le
    _ = _ := by ring

/-- The same conclusion holds at the actual right endpoint in inward time. -/
theorem ClosedHamiltonianJacobiSystem.exists_right_physical_density_power_bound
    {J P A B C : ℝ → Matrix n n ℝ} {l h R θ κ : ℝ} {ρ w v : ℝ → ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C l h) (hlh : l < h)
    (hρ0 : ∀ t ∈ Ioo l h, 0 ≤ ρ t)
    (hρR : ∀ t ∈ Ioo l h, ρ t ≤ R)
    (hw : ContinuousOn w (Icc l h)) (hw0 : ∀ t ∈ Ioo l h, 0 ≤ w t)
    (hv : ContinuousOn v (Icc l h)) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    ∃ ε K : ℝ, 0 < ε ∧ ε < h - l ∧ 0 < K ∧ ∀ r ∈ Ioo 0 ε,
      0 ≤ (ρ (h - r) * w (h - r) / θ) *
        (|v (h - r)| * |(J (h - r)).det| * κ) ∧
      (ρ (h - r) * w (h - r) / θ) *
        (|v (h - r)| * |(J (h - r)).det| * κ) ≤
          K * r ^ Module.finrank ℝ (ker (J h).mulVecLin) := by
  obtain ⟨K, hK, hcoeff⟩ := exists_physical_jacobi_density_determinant_bound
    (J := J) hρ0 hρR hw hw0 hv hθ hκ
  obtain ⟨ε, D, hε, hεh, hD, hdet⟩ := H.exists_right_determinant_power_bound hlh
  refine ⟨ε, K * D, hε, hεh, mul_pos hK hD, ?_⟩
  intro r hr
  have ht : h - r ∈ Ioo l h := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine ⟨(hcoeff _ ht).1, ?_⟩
  calc
    _ ≤ K * |(J (h - r)).det| := (hcoeff _ ht).2
    _ ≤ K * (D * r ^ Module.finrank ℝ (ker (J h).mulVecLin)) :=
      mul_le_mul_of_nonneg_left (hdet r hr) hK.le
    _ = _ := by ring

end OTSelector.Reconstruction
