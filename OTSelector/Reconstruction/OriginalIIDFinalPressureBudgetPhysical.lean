import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalEnergy

/-! The actual tilted original iid plan spends the whole-fractional-face population energy budget. -/
open Set Function Filter MeasureTheory Matrix
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The fixed measurable exact assignment rule is a member of the whole fractional
optimal face, so its actual physical base-energy integral inherits the same global budget.
Every original observation and its particle index is retained. -/
theorem lintegral_originalIID_tiltedPhysicalPlan_base_energy_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {q : ℕ}
    (cost : X → Y → ℝ) (hcost : Measurable (Function.uncurry cost))
    (hcost0 : ∀ x y, 0 ≤ cost x y) {C : ℝ}
    (henergy : PopulationUniformEnergyBound μ ν q cost C)
    (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ) (hG : ∀ x y, |probe x y| ≤ G) (t : ℝ) (n : ℕ) :
    let k := ((n+1 : ℕ) : ℝ) ^ (2/(q : ℝ))
    let tilted := fun x y ↦ k*cost x y+t*probe x y
    (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (k*cost p.1 p.2)
      ∂originalIIDOptimalPhysicalPlan (n := n+1) tilted 1 ξ
      ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤
      ENNReal.ofReal (C+2 * |t| * G) := by
  classical
  intro k tilted
  let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))
  let c : ((Fin (n+1) → X) × (Fin (n+1) → Y)) → Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun ξ ↦
    fun i j ↦ k*cost (ξ.1 i) (ξ.2 j)
  let g : ((Fin (n+1) → X) × (Fin (n+1) → Y)) → Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun ξ ↦
    fun i j ↦ probe (ξ.1 i) (ξ.2 j)
  let σ := fun ξ : (Fin (n+1) → X) × (Fin (n+1) → Y) ↦
    firstOptimalAssignment (perturbedEdgeCost (c ξ) (g ξ) t)
  let W := fun ξ ↦ (σ ξ).permMatrix ℝ
  let : MeasurableSpace (Assignment (n+1)) := ⊤
  have hσ : Measurable σ := by
    apply measurable_firstOptimalAssignment
    intro i j
    have hpair : Measurable (fun ξ : (Fin (n+1) → X) × (Fin (n+1) → Y) ↦ (ξ.1 i,ξ.2 j)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)
    exact ((hcost.comp hpair).const_mul k).add ((hprobe.comp hpair).const_mul t)
  have hW (i j : Fin (n+1)) : Measurable (fun ξ ↦ W ξ i j) :=
    (measurable_of_countable (fun τ : Assignment (n+1) ↦ (τ.permMatrix ℝ) i j)).comp hσ
  have hopt (ξ) : OptimalFractionalAssignment (perturbedEdgeCost (c ξ) (g ξ) t) (W ξ) := by
    refine ⟨permMatrix_mem_doublyStochastic, ?_⟩
    intro Q hQ
    rw [fractionalAssignmentCost_permMatrix]
    exact assignmentCost_le_fractionalAssignmentCost _ Q (σ ξ) (firstOptimalAssignment_isOptimal _) hQ
  have hb := (henergy (n+1) (Nat.succ_pos _)).2 probe t G
    (Eventually.of_forall (fun p ↦ hG p.1 p.2)) W hW (Eventually.of_forall hopt)
  have hreal (ξ : (Fin (n+1) → X) × (Fin (n+1) → Y)) :
      (∫ p, k*cost p.1 p.2 ∂originalIIDOptimalPhysicalPlan (n := n+1) tilted 1 ξ) =
        fractionalAssignmentCost (c ξ) (W ξ) / ((n+1 : ℕ) : ℝ) := by
    unfold originalIIDOptimalPhysicalPlan
    rw [integral_empiricalMeasure (f := fun p : X × Y ↦ k*cost p.1 p.2) _ (hcost.const_mul k).stronglyMeasurable,
      fractionalAssignmentCost_permMatrix]
    simp only [tilted, c, g, σ, one_mul, assignmentCost, div_eq_mul_inv, mul_comm]
    rfl
  have hk : 0 ≤ k := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnn (ξ : (Fin (n+1) → X) × (Fin (n+1) → Y)) :
      0 ≤ fractionalAssignmentCost (c ξ) (W ξ) / ((n+1 : ℕ) : ℝ) := by
    rw [← hreal ξ]
    exact integral_nonneg (fun p ↦ mul_nonneg hk (hcost0 p.1 p.2))
  calc
    _ = ∫⁻ ξ, ENNReal.ofReal (fractionalAssignmentCost (c ξ) (W ξ)/((n+1 : ℕ) : ℝ)) ∂law := by
      apply lintegral_congr
      intro ξ
      rw [← ofReal_integral_eq_lintegral_ofReal (f := fun p : X × Y ↦ k*cost p.1 p.2)
        (integrable_originalIIDOptimalPhysicalPlan tilted 1 ξ (hcost.const_mul k).stronglyMeasurable)
        (Eventually.of_forall (fun p ↦ mul_nonneg hk (hcost0 p.1 p.2))), hreal ξ]
    _ = ENNReal.ofReal (∫ ξ, fractionalAssignmentCost (c ξ) (W ξ)/((n+1 : ℕ) : ℝ) ∂law) :=
      (ofReal_integral_eq_lintegral_ofReal hb.1 (Eventually.of_forall hnn)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb.2

end OTSelector.Reconstruction
