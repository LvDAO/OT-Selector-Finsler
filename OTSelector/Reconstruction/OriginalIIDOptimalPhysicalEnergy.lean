import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.PopulationUniformEnergyBound

/-! The existing original population energy bound controls the actual physical
plan from the original two-color iid experiment, with one unchanged constant. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The original zero-tilt finite minimizer spends at most the same global
population energy constant, before restriction to any atlas piece. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_cost_uniform
    (μ : Measure X) (ν : Measure Y) {q : ℕ}
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (hcost0 : ∀ x y, 0 ≤ cost x y) {C : ℝ}
    (henergy : PopulationUniformEnergyBound μ ν q cost C)
    {n : ℕ} (hn : 0 < n) :
    (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((n : ℝ) ^ (2 / (q : ℝ)) * cost p.1 p.2)
      ∂originalIIDOptimalPhysicalPlan cost ((n : ℝ) ^ (2 / (q : ℝ))) ξ
      ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ≤
      ENNReal.ofReal C := by
  let _ : NeZero n := ⟨hn.ne'⟩
  have hk : 0 ≤ (n : ℝ) ^ (2 / (q : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have heq (ξ : (Fin n → X) × (Fin n → Y)) :=
    lintegral_originalIIDOptimalPhysicalPlan_cost cost hcost hcost0 hk ξ
  have hb := (henergy n hn).1
  calc
    _ = ∫⁻ ξ, ENNReal.ofReal (perturbedAssignmentValue
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ξ.1 i) (ξ.2 j)) 0 0 / n)
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)) :=
      lintegral_congr heq
    _ = ENNReal.ofReal (∫ ξ, perturbedAssignmentValue
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ξ.1 i) (ξ.2 j)) 0 0 / n
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) := by
      apply (ofReal_integral_eq_lintegral_ofReal hb.1 _).symm
      apply Filter.Eventually.of_forall
      intro ξ
      change 0 ≤ perturbedAssignmentValue
        (show Matrix (Fin n) (Fin n) ℝ from
          fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ξ.1 i) (ξ.2 j)) 0 0 / n
      rw [← integral_originalIIDOptimalPhysicalPlan_cost cost hcost _ ξ]
      exact integral_nonneg (fun p ↦ mul_nonneg hk (hcost0 p.1 p.2))
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hb.2

/-- Disjoint source restrictions of the actual iid optimal plan spend the
global energy once, including a countably infinite collection of pieces. -/
theorem tsum_originalIIDOptimalPhysicalPlan_sourceEnergy_uniform
    (μ : Measure X) (ν : Measure Y) {q : ℕ}
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (hcost0 : ∀ x y, 0 ≤ cost x y) {C : ℝ}
    (henergy : PopulationUniformEnergyBound μ ν q cost C)
    {n : ℕ} (hn : 0 < n)
    (H : ℕ → Set X) (hH : ∀ j, MeasurableSet (H j))
    (hdisj : Pairwise (Disjoint on H)) :
    (∑' j, ∫⁻ ξ, ∫⁻ p in H j ×ˢ (univ : Set Y),
      ENNReal.ofReal ((n : ℝ) ^ (2 / (q : ℝ)) * cost p.1 p.2)
      ∂originalIIDOptimalPhysicalPlan cost ((n : ℝ) ^ (2 / (q : ℝ))) ξ
      ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ≤
      ENNReal.ofReal C := by
  let k : ℝ := (n : ℝ) ^ (2 / (q : ℝ))
  let e : X × Y → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (k * cost p.1 p.2)
  let Γ := originalIIDOptimalPhysicalPlan (n := n) cost k
  have hm : Measurable Γ := measurable_originalIIDOptimalPhysicalPlan cost hcost k
  have he : Measurable e := (hcost.const_mul k).ennreal_ofReal
  have hprod (j : ℕ) : MeasurableSet (H j ×ˢ (univ : Set Y)) :=
    (hH j).prod MeasurableSet.univ
  have hi (j : ℕ) : Measurable
      (fun ξ ↦ ∫⁻ p in H j ×ˢ (univ : Set Y), e p ∂Γ ξ) := by
    simp_rw [← lintegral_indicator (hprod j)]
    exact (Measure.measurable_lintegral (he.indicator (hprod j))).comp hm
  have hd : Pairwise (Disjoint on (fun j ↦ H j ×ˢ (univ : Set Y))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact Set.disjoint_left.mp (hdisj hij) hpi.1 hpj.1
  change (∑' j, ∫⁻ ξ, ∫⁻ p in H j ×ˢ (univ : Set Y), e p ∂Γ ξ
    ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ≤ _
  rw [← lintegral_tsum (fun j ↦ (hi j).aemeasurable)]
  calc
    _ ≤ ∫⁻ ξ, ∫⁻ p, e p ∂Γ ξ
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)) := by
      apply lintegral_mono
      intro ξ
      change (∑' j, ∫⁻ p in H j ×ˢ (univ : Set Y), e p ∂Γ ξ) ≤ ∫⁻ p, e p ∂Γ ξ
      rw [← lintegral_iUnion hprod hd e]
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ENNReal.ofReal C :=
      lintegral_originalIIDOptimalPhysicalPlan_cost_uniform μ ν cost hcost hcost0 henergy hn

end OTSelector.Reconstruction
