import OTSelector.Transport.Semidiscrete.DirichletReadout
import OTSelector.Analysis.Convex.InfimumComparison

/-!
# Actual semidiscrete values and the iid finite minimum

The semidiscrete value is the infimum over all feasible fractional allocations for
the prescribed masses. It is finite on the simplex. Actual cavity calibration attains
this infimum almost surely, giving the value identity for atomless cost differences.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- The actual primal semidiscrete value at the given target-label masses. -/
def semidiscreteValue (μ : Measure S) (c : S → Fin (m + 1) → ℝ)
    (p : Fin (m + 1) → ℝ) : ℝ :=
  sInf (semidiscreteAllocationCost μ c '' {a | IsSemidiscreteAllocation μ p a})

/-- Every feasible allocation has a uniform integrable-cost bound. -/
theorem IsSemidiscreteAllocation.norm_cost_le {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ) :
    ‖semidiscreteAllocationCost μ c a‖ ≤ ∑ j, ∫ s, ‖c s j‖ ∂μ := by
  have hi := integrable_finsetSum Finset.univ (fun j _ ↦ ha.integrable_mul c hc j)
  calc
    _ ≤ ∫ s, ‖∑ j, a s j * c s j‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ s, ∑ j, ‖c s j‖ ∂μ := by
      apply integral_mono_ae hi.norm (integrable_finsetSum _ (fun j _ ↦ (hc j).norm))
      filter_upwards [ha.nonneg, ha.ae_le_one] with s hn hu
      calc
        _ ≤ ∑ j, ‖a s j * c s j‖ := norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn j)]
          exact (mul_le_mul_of_nonneg_right (hu j) (norm_nonneg _)).trans_eq (one_mul _)
    _ = _ := integral_finsetSum _ (fun j _ ↦ (hc j).norm)

/-- Every simplex vector is feasible, using constant allocation weights. -/
theorem isSemidiscreteAllocation_const (μ : Measure S) [IsProbabilityMeasure μ]
    (p : Fin (m + 1) → ℝ) (hp : p ∈ stdSimplex ℝ (Fin (m + 1))) :
    IsSemidiscreteAllocation μ p (fun _ ↦ p) := by
  refine ⟨fun j ↦ integrable_const (p j), Eventually.of_forall (fun _ ↦ hp.1),
    Eventually.of_forall (fun _ ↦ hp.2), ?_⟩
  intro j
  simp

/-- Integrable costs bound the full feasible objective set below. -/
theorem bddBelow_semidiscrete_costs (μ : Measure S)
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (p : Fin (m + 1) → ℝ) :
    BddBelow (semidiscreteAllocationCost μ c '' {a | IsSemidiscreteAllocation μ p a}) := by
  refine ⟨-(∑ j, ∫ s, ‖c s j‖ ∂μ), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using ha.norm_cost_le c hc)).1

/-- The feasible fractional-allocation value is a real infimum, without attainment. -/
theorem isGLB_semidiscreteValue (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (p : Fin (m + 1) → ℝ) (hp : p ∈ stdSimplex ℝ (Fin (m + 1))) :
    IsGLB (semidiscreteAllocationCost μ c '' {a | IsSemidiscreteAllocation μ p a})
      (semidiscreteValue μ c p) :=
  isGLB_csInf ⟨_, ⟨fun _ ↦ p, isSemidiscreteAllocation_const μ p hp, rfl⟩⟩
    (bddBelow_semidiscrete_costs μ c hc p)

/-- The primal value is no larger than any actual feasible objective. -/
theorem semidiscreteValue_le_cost (μ : Measure S)
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (p : Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) :
    semidiscreteValue μ c p ≤ semidiscreteAllocationCost μ c a :=
  csInf_le (bddBelow_semidiscrete_costs μ c hc p) ⟨a, ha, rfl⟩

/-- An actual optimal allocation attains the defined primal infimum. -/
theorem semidiscreteValue_eq_cost_of_optimal (μ : Measure S)
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (p : Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (hopt : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ c a ≤ semidiscreteAllocationCost μ c b) :
    semidiscreteValue μ c p = semidiscreteAllocationCost μ c a := by
  refine le_antisymm (semidiscreteValue_le_cost μ c hc p a ha)
    (le_csInf ⟨_, ⟨a, ha, rfl⟩⟩ ?_)
  rintro _ ⟨b, hb, rfl⟩
  exact hopt b hb

/-- All simplex values obey the same finite bound, whether or not their infimum is attained. -/
theorem norm_semidiscreteValue_le (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (p : Fin (m + 1) → ℝ) (hp : p ∈ stdSimplex ℝ (Fin (m + 1))) :
    ‖semidiscreteValue μ c p‖ ≤ ∑ j, ∫ s, ‖c s j‖ ∂μ := by
  rw [Real.norm_eq_abs, abs_le]
  have hconst := isSemidiscreteAllocation_const μ p hp
  have hne : (semidiscreteAllocationCost μ c '' {a | IsSemidiscreteAllocation μ p a}).Nonempty :=
    ⟨_, ⟨fun _ ↦ p, hconst, rfl⟩⟩
  constructor
  · change -(∑ j, ∫ s, ‖c s j‖ ∂μ) ≤
      sInf (semidiscreteAllocationCost μ c '' {a | IsSemidiscreteAllocation μ p a})
    apply le_csInf hne
    rintro _ ⟨a, ha, rfl⟩
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using ha.norm_cost_le c hc)).1
  · exact (semidiscreteValue_le_cost μ c hc p _ hconst).trans
      (abs_le.mp (by simpa only [Real.norm_eq_abs] using hconst.norm_cost_le c hc)).2

/-- Under the actual atomless cost hypothesis, the original finite minimum has exactly
the Dirichlet average of the primal semidiscrete values. Both sides are integrable. -/
theorem integral_iid_assignmentValue_eq_dirichlet_semidiscreteValue
    [StandardBorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hci : ∀ j, Integrable (c j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    Integrable (semidiscreteValue μ (fun s j ↦ c j s)) (dirichletOne m) ∧
    Integrable (fun x : Fin (m + 1) → S ↦
      perturbedAssignmentValue (fun i j ↦ c j (x i)) 0 0 / (m + 1 : ℕ))
      (Measure.pi (fun _ : Fin (m + 1) ↦ μ)) ∧
    (∫ x : Fin (m + 1) → S,
      perturbedAssignmentValue (fun i j ↦ c j (x i)) 0 0 / (m + 1 : ℕ)
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ)) =
      ∫ p, semidiscreteValue μ (fun s j ↦ c j s) p ∂dirichletOne m := by
  classical
  obtain ⟨G, hG, hrep, hmean⟩ := exists_dirichlet_semidiscrete_mean_readout
    μ c hc hci hatom (fun s j ↦ c j s) hc hci
  have heq : G =ᵐ[dirichletOne m] semidiscreteValue μ (fun s j ↦ c j s) := by
    filter_upwards [hrep] with p hp
    obtain ⟨a, ha, hopt, hGa⟩ := hp
    exact hGa.trans (semidiscreteValue_eq_cost_of_optimal μ _ hci p a ha
      (fun b hb ↦ (hopt b hb).1)).symm
  have hsd : Integrable (semidiscreteValue μ (fun s j ↦ c j s)) (dirichletOne m) := by
    apply (integrable_const (∑ j, ∫ s, ‖c j s‖ ∂μ)).mono'
      (hG.aestronglyMeasurable.congr heq)
    exact (ae_mem_stdSimplex_dirichletOne m).mono fun p hp ↦
      norm_semidiscreteValue_le μ _ hci p hp
  choose A hA using fun x : Fin (m + 1) → S ↦
    exists_optimalFractionalAssignment (fun i j ↦ c j (x i))
  have hcost (x : Fin (m + 1) → S) :
      perturbedAssignmentValue (fun i j ↦ c j (x i)) 0 0 =
        ∑ i, ∑ j, A x i j * c j (x i) := by
    let C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j ↦ c j (x i)
    change perturbedAssignmentValue C 0 0 = fractionalAssignmentCost C (A x)
    have hopt : OptimalFractionalAssignment (perturbedEdgeCost C 0 0) (A x) := by
      rw [perturbedEdgeCost_zero]
      exact hA x
    simpa only [perturbedEdgeCost_zero] using
      perturbedAssignmentValue_eq_of_optimalFractional C 0 (A x) 0 hopt
  have hrow := integral_iid_optimalFractional_mean_eq_canonical_cavity
    μ c hc hatom A (Eventually.of_forall hA) (fun s j ↦ c j s) hci
  refine ⟨hsd, ?_, ?_⟩
  · simpa only [hcost] using hrow.1
  · simp_rw [hcost]
    exact (hmean A (Eventually.of_forall hA)).trans (integral_congr_ae heq)

end OTSelector.Probability
