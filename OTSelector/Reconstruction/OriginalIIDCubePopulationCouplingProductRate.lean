import OTSelector.Reconstruction.IIDDyadicCubeMatching

/-! The actual product iid cube sample satisfies the quadratic matching rate. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Independent product samples satisfy the literal optimal assignment bound,
including an empty sample, without a separate iid or rate input. -/
theorem expected_originalIIDCube_product_assignment_rate {q n : ℕ} (hq : 4 < q)
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ] :
    let P₀ := Measure.pi (fun _ : Fin n ↦ μ)
    let P := P₀.prod P₀
    Integrable (fun ξ : (Fin n → DyadicUnitCube q) × (Fin n → DyadicUnitCube q) ↦
      perturbedAssignmentValue (fun i j ↦
        ‖dyadicCubePoint (ξ.1 i) - dyadicCubePoint (ξ.2 j)‖ ^ 2) 0 0) P ∧
    (∫ ξ, perturbedAssignmentValue (fun i j ↦
      ‖dyadicCubePoint (ξ.1 i) - dyadicCubePoint (ξ.2 j)‖ ^ 2) 0 0 ∂P) ≤
        dyadicMatchingConstant q * (n : ℝ) ^ (1 - 2 / (q : ℝ)) := by
  let P₀ := Measure.pi (fun _ : Fin n ↦ μ)
  let P := P₀.prod P₀
  let xs : Fin n → ((Fin n → DyadicUnitCube q) × (Fin n → DyadicUnitCube q)) →
      DyadicUnitCube q := fun i ξ ↦ ξ.1 i
  let ys : Fin n → ((Fin n → DyadicUnitCube q) × (Fin n → DyadicUnitCube q)) →
      DyadicUnitCube q := fun i ξ ↦ ξ.2 i
  have hx (i : Fin n) : Measurable (xs i) := (measurable_pi_apply i).comp measurable_fst
  have hy (i : Fin n) : Measurable (ys i) := (measurable_pi_apply i).comp measurable_snd
  have hxl (i : Fin n) : P.map (xs i) = μ :=
    ((measurePreserving_eval (fun _ : Fin n ↦ μ) i).comp measurePreserving_fst).map_eq
  have hyl (i : Fin n) : P.map (ys i) = μ :=
    ((measurePreserving_eval (fun _ : Fin n ↦ μ) i).comp measurePreserving_snd).map_eq
  have hxi : iIndepFun xs P := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hx i).aemeasurable)).2
    simp only [hxl]
    exact measurePreserving_fst.map_eq
  have hyi : iIndepFun ys P := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hy i).aemeasurable)).2
    simp only [hyl]
    exact measurePreserving_snd.map_eq
  have hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  exact expected_cubeSquaredAssignment_rate hq P μ xs ys hx hy hxi hyi hxl hyl hxy

end OTSelector.Reconstruction
