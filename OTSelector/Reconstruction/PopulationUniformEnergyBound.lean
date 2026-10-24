import OTSelector.Reconstruction.PopulationTypedOptimalEnergy

/-!
# The original whole-face energy bound as a reusable population property

The property quantifies over every sample size, bounded probe and measurable
fractional optimum. Actual typed population data produce it with one constant.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Uniform normalized original-sample pressure and base energy for the entire
fractional tilted optimal face, under the unchanged two-color iid law. -/
def PopulationUniformEnergyBound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (q : ℕ) (cost : X → Y → ℝ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    let P := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    let c := fun ξ : (Fin n → X) × (Fin n → Y) ↦
      fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ξ.1 i) (ξ.2 j);
    (Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) 0 0 / n) P ∧
      (∫ ξ, perturbedAssignmentValue (c ξ) 0 0 / n ∂P) ≤ C) ∧
    ∀ (probe : X → Y → ℝ) (τ G : ℝ),
      (∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G) →
      ∀ W : ((Fin n → X) × (Fin n → Y)) → Matrix (Fin n) (Fin n) ℝ,
        (∀ i j, Measurable (fun ξ ↦ W ξ i j)) →
        (∀ᵐ ξ ∂P, OptimalFractionalAssignment
          (perturbedEdgeCost (c ξ) (fun i j ↦ probe (ξ.1 i) (ξ.2 j)) τ) (W ξ)) →
        Integrable (fun ξ ↦ fractionalAssignmentCost (c ξ) (W ξ) / n) P ∧
        (∫ ξ, fractionalAssignmentCost (c ξ) (W ξ) / n ∂P) ≤ C + 2 * |τ| * G

/-- Enlarging the single population constant preserves all sample-size and
whole-optimal-face quantifiers. -/
theorem PopulationUniformEnergyBound.mono
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {q : ℕ} {cost : X → Y → ℝ} {C D : ℝ}
    (h : PopulationUniformEnergyBound μ ν q cost C) (hCD : C ≤ D) :
    PopulationUniformEnergyBound μ ν q cost D := by
  intro n hn
  obtain ⟨h0, ht⟩ := h n hn
  refine ⟨⟨h0.1, h0.2.trans hCD⟩, ?_⟩
  intro probe τ G hg W hW hopt
  have hb := ht probe τ G hg W hW hopt
  exact ⟨hb.1, hb.2.trans (add_le_add hCD le_rfl)⟩

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)

/-- The original finite atlas produces the reusable uniform energy property. -/
theorem population_uniform_energy_bound (hq : 4 < q) (hπ : Vlasov.IsCoupling π μ ν) :
    PopulationUniformEnergyBound μ ν q cost
      (D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card (Option T))) := by
  intro n hn
  exact ⟨D.original_scaled_pressure_uniform hq hn hπ,
    D.original_tilted_optimal_energy_uniform hq hn hπ⟩

include D in
/-- One strictly positive constant is fixed before all sample sizes and probe tilts. -/
theorem exists_population_uniform_energy_bound (hq : 4 < q)
    (hπ : Vlasov.IsCoupling π μ ν) :
    ∃ C : ℝ, 0 < C ∧ PopulationUniformEnergyBound μ ν q cost C := by
  have h := D.population_uniform_energy_bound hq hπ
  let C := D.quadraticConstant * dyadicMatchingConstant q *
    (Fintype.card (Option T) : ℝ) ^ (2 / (q : ℝ)) +
    D.globalBound * Real.sqrt (2 * Fintype.card (Option T))
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (mul_nonneg D.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg D.bound_nonneg (Real.sqrt_nonneg _))
  exact ⟨C + 1, by linarith, h.mono (by dsimp [C]; linarith)⟩

end PopulationTypedCostData
end OTSelector.Reconstruction
