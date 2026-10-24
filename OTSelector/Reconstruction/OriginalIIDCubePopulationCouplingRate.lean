import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingCost
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingProductRate

/-! The actual sample-to-population transport, obtained by averaging a real
finite optimizer over its second iid cloud, inherits the proven cube rate. -/
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q n : ℕ}

/-- The actual population-coupling energy has the distribution-free expected
quadratic rate, for every population probability on the closed cube and n=0. -/
theorem expected_originalIIDCubePopulationCoupling_squareCost_rate (hq : 4 < q)
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ] :
    Integrable (fun x : Fin n → DyadicUnitCube q ↦
      ∫ p, originalCubePopulationSquareCost p
        ∂originalIIDPopulationCoupling μ
          (fun u v ↦ originalCubePopulationSquareCost (u, v)) x)
      (Measure.pi (fun _ : Fin n ↦ μ)) ∧
    (∫ x, ∫ p, originalCubePopulationSquareCost p
      ∂originalIIDPopulationCoupling μ
        (fun u v ↦ originalCubePopulationSquareCost (u, v)) x
      ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
        dyadicMatchingConstant q * (n : ℝ) ^ (1 - 2 / (q : ℝ)) := by
  have h := expected_originalIIDCube_product_assignment_rate (n := n) hq μ
  change Integrable (fun ξ : (Fin n → DyadicUnitCube q) × (Fin n → DyadicUnitCube q) ↦
    perturbedAssignmentValue (fun i j ↦ originalCubePopulationSquareCost
      (ξ.1 i, ξ.2 j)) 0 0) _ ∧ _ at h
  simp_rw [integral_originalIIDCubePopulationCoupling_squareCost]
  exact ⟨h.1.integral_prod_left, (integral_prod _ h.1).symm.trans_le h.2⟩

end OTSelector.Reconstruction
