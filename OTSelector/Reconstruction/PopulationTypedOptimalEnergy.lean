import OTSelector.Reconstruction.PopulationTypedRecoveryEnergy
import OTSelector.Reconstruction.TiltedOptimalRecoveryEnergy

/-!
# Uniform original pressure and energy on the whole fractional optimal face

Actual population type data bound the true microscopic pressure. The same bound
then controls every measurable fractional optimum at any bounded probe tilt.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)

/-- Literal microscopic zero-tilt pressure under the unchanged physical iid law. -/
theorem original_scaled_pressure_uniform {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    Integrable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i) (ω.2 j)) 0 0 / n) P₀ ∧
    (∫ ω : (Fin n → X) × (Fin n → Y),
      perturbedAssignmentValue (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i) (ω.2 j)) 0 0 / n ∂P₀) ≤
      D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card (Option T)) := by
  have h := D.original_iid_assignment_uniform hq hn hπ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < (n : ℝ) ^ (2 / (q : ℝ)) := Real.rpow_pos_of_pos hnR _
  have heq : (fun ω : (Fin n → X) × (Fin n → Y) ↦
      perturbedAssignmentValue (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i) (ω.2 j)) 0 0 / n) =
      (fun ω ↦ ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        perturbedAssignmentValue (fun i j ↦ cost (ω.1 i) (ω.2 j)) 0 0) := by
    funext ω
    rw [assignmentValue_posScale _ hk]
    ring
  rw [heq]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  exact h.2

/-- The actual microscopic base energy of every fractional tilted optimum is
uniformly bounded, with the precise bounded-probe increment from the paper. -/
theorem original_tilted_optimal_energy_uniform {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (probe : X → Y → ℝ) (τ G : ℝ)
    (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G)
    (W : ((Fin n → X) × (Fin n → Y)) → Matrix (Fin n) (Fin n) ℝ)
    (hWm : ∀ i j, Measurable (fun ω ↦ W ω i j))
    (hopt : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)),
      OptimalFractionalAssignment
        (perturbedEdgeCost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i) (ω.2 j))
          (fun i j ↦ probe (ω.1 i) (ω.2 j)) τ) (W ω)) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    Integrable (fun ω ↦ fractionalAssignmentCost
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i) (ω.2 j)) (W ω) / n) P₀ ∧
    (∫ ω, fractionalAssignmentCost
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i) (ω.2 j)) (W ω) / n ∂P₀) ≤
      D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card (Option T)) + 2 * |τ| * G := by
  let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
  let k : ℝ := (n : ℝ) ^ (2 / (q : ℝ))
  have hk : 0 ≤ k := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hraw : ∀ᵐ ω ∂P₀, ∀ i j,
      0 ≤ cost (ω.1 i) (ω.2 j) ∧ cost (ω.1 i) (ω.2 j) ≤ D.globalBound := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) i)
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) j)).ae D.global_bounds
  have hprobe : ∀ᵐ ω ∂P₀, ∀ i j, |probe (ω.1 i) (ω.2 j)| ≤ G := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) i)
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) j)).ae hg
  have hcm (i j : Fin n) : Measurable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      k * cost (ω.1 i) (ω.2 j)) :=
    (D.measurable_cost.comp (show Measurable (fun ω : (Fin n → X) × (Fin n → Y) ↦
      (ω.1 i, ω.2 j)) from by fun_prop)).const_mul k
  have h := expected_optimalFractional_base_energy hn
    (fun ω i j ↦ k * cost (ω.1 i) (ω.2 j)) (fun ω i j ↦ probe (ω.1 i) (ω.2 j)) W
    τ G (k * D.globalBound) hcm hWm hopt
    (hraw.mono (fun _ hω i j ↦ mul_nonneg hk (hω i j).1))
    (hraw.mono (fun _ hω i j ↦ mul_le_mul_of_nonneg_left (hω i j).2 hk)) hprobe
  have hzero := D.original_scaled_pressure_uniform hq hn hπ
  exact ⟨h.1, h.2.trans (add_le_add hzero.2 le_rfl)⟩

end PopulationTypedCostData
end OTSelector.Reconstruction
