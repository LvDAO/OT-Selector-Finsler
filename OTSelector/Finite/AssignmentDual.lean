import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.Assignment
import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.FractionalGauge
import OTSelector.Finite.FractionalOptimal
import OTSelector.Finite.PerturbedValue

/-!
# Finite.AssignmentDual

**Conditions:** Finite real costs; repeated-slot quota versions have positive integer quotas of the indicated total.

**Objects:** One common attained finite dual and its tight-edge characterization of every permutation/fractional optimum.

**Proof detail:** Normalize by actual cavity values, use optimal cross exchanges to build feasible potentials, sum their tight equalities along optimizers, and project repeated slots to quota labels.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Proposition 2.4 states finite Kantorovich duality and complementary slackness. The source constructs the dual explicitly from cavity values and proves simultaneous attainment for all deleted targets; those formulas are local refinements.
-/

/-!
# Actual common duals for finite assignments

Deleted-row cavity prices construct a single feasible assignment dual attaining the actual
minimum. Every optimal permutation and every fractional optimum is characterized by tight
edges for this same dual, including all ties. The same potentials attain every target vacancy
sharing the removed row. Repeated slots then give actual label duals with integer-capacity
weighted objectives. No target-tree or probability-law assertion is made here.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

private theorem sum_cost_update (cost : Fin n → Fin n → ℝ) (f : Fin n → Fin n)
    (i j : Fin n) :
    (∑ k, cost k (Function.update f i j k)) =
      (∑ k, cost k (f k)) - cost i (f i) + cost i j := by
  have heq : (fun k ↦ cost k (Function.update f i j k)) =
      Function.update (fun k ↦ cost k (f k)) i (cost i j) :=
    funext (Function.apply_update cost f i j)
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add Finset.univ (fun k ↦ cost k (f k)) (Finset.mem_univ i)
  linarith

/-- Edges in any two optimal permutations satisfy the same two-edge exchange inequality. -/
theorem optimalAssignment_cross_exchange (cost : Fin n → Fin n → ℝ)
    (σ τ : Assignment n) (hσ : OptimalAssignment cost σ) (hτ : OptimalAssignment cost τ)
    (i k : Fin n) :
    cost i (σ i) + cost k (τ k) ≤ cost i (τ k) + cost k (σ i) := by
  let a := Function.update (σ : Fin n → Fin n) i (τ k)
  let b := Function.update (τ : Fin n → Fin n) k (σ i)
  let Q : Matrix (Fin n) (Fin n) ℝ :=
    fun r s ↦ ((if a r = s then 1 else 0) + (if b r = s then 1 else 0)) / 2
  have hQ : Q ∈ doublyStochastic ℝ (Fin n) := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro r s
      dsimp [Q]
      positivity
    · intro r
      change (∑ s, (((if a r = s then 1 else 0) +
        (if b r = s then 1 else 0)) : ℝ) / 2) = 1
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp
    · intro s
      have hσsum : (∑ r : Fin n, if σ r = s then (1 : ℝ) else 0) = 1 := by
        simpa [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply] using
          sum_col_of_mem_doublyStochastic (permMatrix_mem_doublyStochastic (R := ℝ) (σ := σ)) s
      have hτsum : (∑ r : Fin n, if τ r = s then (1 : ℝ) else 0) = 1 := by
        simpa [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply] using
          sum_col_of_mem_doublyStochastic (permMatrix_mem_doublyStochastic (R := ℝ) (σ := τ)) s
      have ha := sum_cost_update (fun _ t ↦ if t = s then (1 : ℝ) else 0) σ i (τ k)
      have hb := sum_cost_update (fun _ t ↦ if t = s then (1 : ℝ) else 0) τ k (σ i)
      change (∑ r, (((if a r = s then 1 else 0) +
        (if b r = s then 1 else 0)) : ℝ) / 2) = 1
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      change ((∑ r, if Function.update (σ : Fin n → Fin n) i (τ k) r = s then 1 else 0) +
        (∑ r, if Function.update (τ : Fin n → Fin n) k (σ i) r = s then 1 else 0)) / 2 = 1
      rw [ha, hb, hσsum, hτsum]
      ring
  have hcost : fractionalAssignmentCost cost Q =
      ((∑ r, cost r (a r)) + ∑ r, cost r (b r)) / 2 := by
    simp only [fractionalAssignmentCost, Q, add_div, add_mul, div_mul_eq_mul_div,
      Finset.sum_add_distrib, ← Finset.sum_div]
    simp
  have hle := assignmentCost_le_fractionalAssignmentCost cost Q σ hσ hQ
  rw [hcost] at hle
  have ha := sum_cost_update cost σ i (τ k)
  have hb := sum_cost_update cost τ k (σ i)
  change (∑ r, cost r (σ r)) ≤
    ((∑ r, cost r (Function.update (σ : Fin n → Fin n) i (τ k) r)) +
      ∑ r, cost r (Function.update (τ : Fin n → Fin n) k (σ i) r)) / 2 at hle
  rw [ha, hb] at hle
  have heq : assignmentCost cost σ = assignmentCost cost τ := le_antisymm (hσ τ) (hτ σ)
  unfold assignmentCost at heq
  linarith

/-- The row potential constructed from one common deleted-row vacancy problem. -/
noncomputable def cavityRowPotential (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ i : Fin (n + 1)) : ℝ :=
  ⨅ j, cost i j + assignmentCavityValue cost i₀ j

/-- The column potential is the negative of the actual deleted-row vacancy price. -/
noncomputable def cavityColumnPotential (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ j : Fin (n + 1)) : ℝ := -assignmentCavityValue cost i₀ j

/-- The constructed row and column potentials satisfy every original dual constraint. -/
theorem cavityPotentials_feasible (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ i j : Fin (n + 1)) :
    cavityRowPotential cost i₀ i + cavityColumnPotential cost i₀ j ≤ cost i j := by
  have hb : BddBelow (Set.range (fun j ↦ cost i j + assignmentCavityValue cost i₀ j)) :=
    (Set.finite_range _).bddBelow
  have h := ciInf_le hb j
  change cavityRowPotential cost i₀ i ≤ cost i j + assignmentCavityValue cost i₀ j at h
  unfold cavityColumnPotential
  linarith

private noncomputable def cavityNormalizedCost (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (n + 1)) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  Function.update cost i₀ (fun j ↦ -assignmentCavityValue cost i₀ j)

private theorem cavityNormalizedCost_envelope (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ j : Fin (n + 1)) :
    assignmentRowEnvelope (cavityNormalizedCost cost i₀) i₀ j = 0 := by
  simp [assignmentRowEnvelope, cavityNormalizedCost]

private theorem cavityNormalizedCost_cavity (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ j : Fin (n + 1)) :
    assignmentCavityCost (cavityNormalizedCost cost i₀) i₀ j =
      assignmentCavityCost cost i₀ j := by
  apply assignmentCavityCost_congr_off_row
  intro k hk l
  simp [cavityNormalizedCost, Function.update_of_ne hk]

private theorem cavityNormalizedCost_optimal (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (n + 1)) (σ : Assignment (n + 1))
    (hσ : OptimalAssignment (assignmentCavityCost cost i₀ (σ i₀))
      (restrictAssignment σ i₀)) :
    OptimalAssignment (cavityNormalizedCost cost i₀) σ := by
  apply (optimalAssignment_iff_cavity _ σ i₀).mpr
  refine ⟨?_, ?_⟩
  · rw [cavityNormalizedCost_cavity]
    exact hσ
  · intro j
    rw [cavityNormalizedCost_envelope, cavityNormalizedCost_envelope]

private theorem cavityNormalizedCost_exists_partner
    (cost : Fin (n + 1) → Fin (n + 1) → ℝ) (i₀ j : Fin (n + 1)) :
    ∃ σ : Assignment (n + 1), OptimalAssignment (cavityNormalizedCost cost i₀) σ ∧
      σ i₀ = j := by
  apply (exists_optimalAssignment_partner_iff _ i₀ j).mpr
  intro k
  rw [cavityNormalizedCost_envelope, cavityNormalizedCost_envelope]

/-- Every edge of every retained optimum is tight for the same vacancy-price potentials. -/
theorem cavityPotentials_tight_of_restrict_optimal
    (cost : Fin (n + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
    (σ : Assignment (n + 1))
    (hσ : OptimalAssignment (assignmentCavityCost cost i₀ (σ i₀))
      (restrictAssignment σ i₀)) (i : Fin (n + 1)) (hi : i ≠ i₀) :
    cavityRowPotential cost i₀ i + cavityColumnPotential cost i₀ (σ i) = cost i (σ i) := by
  have hmin : ∀ j, cost i (σ i) + assignmentCavityValue cost i₀ (σ i) ≤
      cost i j + assignmentCavityValue cost i₀ j := by
    intro j
    obtain ⟨τ, hτ, hτi⟩ := cavityNormalizedCost_exists_partner cost i₀ j
    have h := optimalAssignment_cross_exchange (cavityNormalizedCost cost i₀) σ τ
      (cavityNormalizedCost_optimal cost i₀ σ hσ) hτ i i₀
    simp only [hτi, cavityNormalizedCost, Function.update_self, Function.update_of_ne hi] at h
    linarith
  have hα : cavityRowPotential cost i₀ i =
      cost i (σ i) + assignmentCavityValue cost i₀ (σ i) := by
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (σ i)
    · exact le_ciInf hmin
  rw [hα, cavityColumnPotential]
  ring

/-- A single cavity dual calibrates every optimum of the original square assignment problem. -/
theorem cavityPotentials_tight_of_optimal
    (cost : Fin (n + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
    (σ : Assignment (n + 1)) (hσ : OptimalAssignment cost σ) (i : Fin (n + 1)) :
    cavityRowPotential cost i₀ i + cavityColumnPotential cost i₀ (σ i) = cost i (σ i) := by
  by_cases hi : i = i₀
  · subst i
    have hmin := ((optimalAssignment_iff_cavity cost σ i₀).mp hσ).2
    have hα : cavityRowPotential cost i₀ i₀ = assignmentRowEnvelope cost i₀ (σ i₀) := by
      apply le_antisymm
      · exact ciInf_le (Set.finite_range _).bddBelow (σ i₀)
      · exact le_ciInf hmin
    rw [hα]
    simp [assignmentRowEnvelope, cavityColumnPotential]
  · exact cavityPotentials_tight_of_restrict_optimal cost i₀ σ
      (optimalAssignment_restrictAssignment cost σ hσ i₀) i hi

/-- Every feasible pair of potentials gives the usual lower bound on each actual assignment. -/
theorem assignment_dual_value_le (cost : Fin n → Fin n → ℝ) (α β : Fin n → ℝ)
    (hfeas : ∀ i j, α i + β j ≤ cost i j) (σ : Assignment n) :
    (∑ i, α i) + ∑ j, β j ≤ assignmentCost cost σ := by
  rw [← Equiv.sum_comp σ β, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ ↦ hfeas i (σ i))

/-- A permutation supported on tight edges attains the potential sums exactly. -/
theorem assignmentCost_eq_dual_value_of_tight (cost : Fin n → Fin n → ℝ)
    (α β : Fin n → ℝ) (σ : Assignment n) (htight : ∀ i, α i + β (σ i) = cost i (σ i)) :
    assignmentCost cost σ = (∑ i, α i) + ∑ j, β j := by
  unfold assignmentCost
  simp_rw [← htight]
  rw [Finset.sum_add_distrib, Equiv.sum_comp σ β]

/-- The same potentials attain every deleted-row, deleted-target minimum simultaneously. -/
theorem cavityPotentials_attain_each_vacancy
    (cost : Fin (n + 1) → Fin (n + 1) → ℝ) (i₀ j : Fin (n + 1)) :
    assignmentCavityValue cost i₀ j =
      (∑ k : Fin n, cavityRowPotential cost i₀ (i₀.succAbove k)) +
        ∑ l : Fin n, cavityColumnPotential cost i₀ (j.succAbove l) := by
  obtain ⟨σ, hσ, hσi⟩ := cavityNormalizedCost_exists_partner cost i₀ j
  have hrest := optimalAssignment_restrictAssignment _ σ hσ i₀
  rw [cavityNormalizedCost_cavity] at hrest
  have ht (k : Fin n) :
      cavityRowPotential cost i₀ (i₀.succAbove k) +
        cavityColumnPotential cost i₀ ((σ i₀).succAbove (restrictAssignment σ i₀ k)) =
      assignmentCavityCost cost i₀ (σ i₀) k (restrictAssignment σ i₀ k) := by
    simpa only [assignmentCavityCost, restrictAssignment_succAbove] using
      cavityPotentials_tight_of_restrict_optimal cost i₀ σ hrest (i₀.succAbove k)
        (i₀.succAbove_ne k)
  have hsum := assignmentCost_eq_dual_value_of_tight
    (assignmentCavityCost cost i₀ (σ i₀))
    (fun k ↦ cavityRowPotential cost i₀ (i₀.succAbove k))
    (fun l ↦ cavityColumnPotential cost i₀ ((σ i₀).succAbove l))
    (restrictAssignment σ i₀) ht
  have hval := perturbedAssignmentValue_eq_of_optimal
    (assignmentCavityCost cost i₀ (σ i₀)) 0 0 (restrictAssignment σ i₀)
    (by rw [perturbedEdgeCost_zero (assignmentCavityCost cost i₀ (σ i₀)) 0]; exact hrest)
  rw [perturbedEdgeCost_zero (assignmentCavityCost cost i₀ (σ i₀)) 0] at hval
  have h := hval.trans hsum
  change assignmentCavityValue cost i₀ (σ i₀) = _ at h
  simpa only [hσi] using h

/-- The actual cavity potentials attain the original finite minimum, without a dual premise. -/
theorem cavityPotentials_attain (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (n + 1)) :
    (∑ i, cavityRowPotential cost i₀ i) + ∑ j, cavityColumnPotential cost i₀ j =
      perturbedAssignmentValue cost 0 0 := by
  let σ := optimalAssignment cost
  have ht := assignmentCost_eq_dual_value_of_tight cost _ _ σ
    (cavityPotentials_tight_of_optimal cost i₀ σ (optimalAssignment_isOptimal cost))
  have hv := perturbedAssignmentValue_eq_of_optimal cost 0 0 σ
    (by rw [perturbedEdgeCost_zero cost 0]; exact optimalAssignment_isOptimal cost)
  rw [perturbedEdgeCost_zero cost 0] at hv
  exact ht.symm.trans hv.symm

/-- The entire optimal permutation set is exactly the tight-edge assignment set
of one cavity dual. -/
theorem optimalAssignment_iff_cavityPotentials_tight
    (cost : Fin (n + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
    (σ : Assignment (n + 1)) :
    OptimalAssignment cost σ ↔ ∀ i,
      cavityRowPotential cost i₀ i + cavityColumnPotential cost i₀ (σ i) = cost i (σ i) := by
  constructor
  · exact fun hσ ↦ cavityPotentials_tight_of_optimal cost i₀ σ hσ
  · intro ht τ
    rw [assignmentCost_eq_dual_value_of_tight cost _ _ σ ht]
    exact assignment_dual_value_le cost _ _ (cavityPotentials_feasible cost i₀) τ

/-- Arbitrary finite real costs admit a common attaining dual, including the empty problem. -/
theorem exists_assignment_dual (cost : Fin n → Fin n → ℝ) :
    ∃ α β : Fin n → ℝ, (∀ i j, α i + β j ≤ cost i j) ∧
      (∑ i, α i) + ∑ j, β j = perturbedAssignmentValue cost 0 0 ∧
      ∀ σ : Assignment n, OptimalAssignment cost σ ↔
        ∀ i, α i + β (σ i) = cost i (σ i) := by
  cases n with
  | zero =>
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · have hv := perturbedAssignmentValue_eq_of_optimal cost 0 0 (optimalAssignment cost)
        (by rw [perturbedEdgeCost_zero cost 0]; exact optimalAssignment_isOptimal cost)
      simpa [assignmentCost] using hv.symm
    · intro σ
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _ τ
        simp [assignmentCost]
  | succ n =>
    exact ⟨cavityRowPotential cost 0, cavityColumnPotential cost 0,
      cavityPotentials_feasible cost 0, cavityPotentials_attain cost 0,
      optimalAssignment_iff_cavityPotentials_tight cost 0⟩

/-- Positive integer capacities admit one actual label dual calibrating all optimal allocations.
The capacity vector consists of finite counts; no condition on population marginals is imposed. -/
theorem exists_capacity_assignment_dual {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → ℕ) (htotal : ∑ j, r j = n + 1) (hr : ∀ j, 0 < r j)
    (cost : Fin (n + 1) → α → ℝ) :
    ∃ (u : Fin (n + 1) → ℝ) (v : α → ℝ),
      (∀ i j, u i + v j ≤ cost i j) ∧
      (∀ a, OptimalCapacityAssignment r cost a ↔
        CapacityFeasible r a ∧ ∀ i, u i + v (a i) = cost i (a i)) ∧
      ∃ a, OptimalCapacityAssignment r cost a ∧
        capacityAssignmentCost cost a = (∑ i, u i) + ∑ j, (r j : ℝ) * v j := by
  let target := capacitySlotLabel r htotal
  have ht : CapacityFeasible r target := capacitySlotLabel_feasible r htotal
  let c := fun i s ↦ cost i (target s)
  let u := cavityRowPotential c 0
  let v := fun j ↦ -capacityVacancyPrice r htotal cost 0 j (hr j)
  have hv (s : Fin (n + 1)) : cavityColumnPotential c 0 s = v (target s) := by
    unfold cavityColumnPotential
    apply congrArg Neg.neg
    exact assignmentCavityValue_eq_of_same_label r cost target ht 0 s
      (capacityLabelSlot r htotal (target s) (hr _))
      (capacitySlotLabel_labelSlot r htotal (target s) (hr _)).symm
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro i j
    have h := cavityPotentials_feasible c 0 i (capacityLabelSlot r htotal j (hr j))
    rw [hv] at h
    simpa only [c, target, capacitySlotLabel_labelSlot] using h
  · intro a
    constructor
    · intro ha
      obtain ⟨σ, hσ⟩ := (capacityFeasible_iff_exists_perm r target a ht).mp ha.1
      have heq : a = target ∘ σ := (funext hσ).symm
      have hopt := (optimalCapacityAssignment_iff r cost target ht σ).mp (heq ▸ ha)
      refine ⟨ha.1, ?_⟩
      intro i
      have h := cavityPotentials_tight_of_optimal c 0 σ hopt i
      rw [hv] at h
      simpa only [c, hσ] using h
    · rintro ⟨ha, htight⟩
      obtain ⟨σ, hσ⟩ := (capacityFeasible_iff_exists_perm r target a ht).mp ha
      have hopt : OptimalAssignment c σ := by
        apply (optimalAssignment_iff_cavityPotentials_tight c 0 σ).mpr
        intro i
        rw [hv]
        simpa only [c, hσ] using htight i
      have heq : a = target ∘ σ := (funext hσ).symm
      rw [heq]
      exact (optimalCapacityAssignment_iff r cost target ht σ).mpr hopt
  · let σ := optimalAssignment c
    refine ⟨target ∘ σ,
      (optimalCapacityAssignment_iff r cost target ht σ).mpr (optimalAssignment_isOptimal c), ?_⟩
    have hsum : (∑ s, v (target s)) = ∑ j, (r j : ℝ) * v j := by
      calc
        _ = ∑ p : (Σ j, Fin (r j)), v p.1 :=
          Equiv.sum_comp (capacitySlotEquiv r htotal) (fun p ↦ v p.1)
        _ = _ := by simp [Fintype.sum_sigma]
    change assignmentCost c σ = _
    rw [assignmentCost_eq_dual_value_of_tight c u (cavityColumnPotential c 0) σ
      (cavityPotentials_tight_of_optimal c 0 σ (optimalAssignment_isOptimal c))]
    simp_rw [hv]
    rw [hsum]

/-- Complementary slackness for the full fractional optimal face of the constructed cavity dual. -/
theorem optimalFractionalAssignment_iff_cavityPotentials_tight
    (cost P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i₀ : Fin (n + 1)) :
    OptimalFractionalAssignment cost P ↔
      P ∈ doublyStochastic ℝ (Fin (n + 1)) ∧ ∀ i j, 0 < P i j →
        cavityRowPotential cost i₀ i + cavityColumnPotential cost i₀ j = cost i j := by
  let α := cavityRowPotential cost i₀
  let β := cavityColumnPotential cost i₀
  let slack := fun i j ↦ cost i j - α i - β j
  have hsnonneg (i j) : 0 ≤ slack i j := by
    have h := cavityPotentials_feasible cost i₀ i j
    dsimp [slack, α, β]
    linarith
  constructor
  · intro hP
    have hperm (σ : Assignment (n + 1)) (hσ : OptimalAssignment cost σ) :
        assignmentCost slack σ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have h := cavityPotentials_tight_of_optimal cost i₀ σ hσ i
      dsimp [slack, α, β]
      linarith
    have hz := optimalFractionalAssignment_readout_eq cost slack P hP 0 hperm
    have hn (i j) : 0 ≤ P i j * slack i j := mul_nonneg (hP.1.1 i j) (hsnonneg i j)
    refine ⟨hP.1, ?_⟩
    intro i j hij
    have hrow : (∑ j, P i j * slack i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦
        Finset.sum_nonneg (fun l _ ↦ hn k l))).mp hz i (Finset.mem_univ i)
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ ↦ hn i l)).mp hrow j
      (Finset.mem_univ j)
    have hzero := (mul_eq_zero.mp he).resolve_left (ne_of_gt hij)
    dsimp [slack, α, β] at hzero
    linarith
  · rintro ⟨hP, htight⟩
    have hz : fractionalAssignmentCost slack P = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      by_cases hij : P i j = 0
      · rw [hij, zero_mul]
      · have h := htight i j (lt_of_le_of_ne (hP.1 i j) (Ne.symm hij))
        have hs : slack i j = 0 := by dsimp [slack, α, β]; linarith
        rw [hs, mul_zero]
    have hg := fractionalAssignmentCost_scale_add_rowColumn cost P 1 (fun i ↦ -α i)
      (fun j ↦ -β j) hP
    have hge : fractionalAssignmentCost slack P =
        fractionalAssignmentCost cost P - (∑ i, α i) - ∑ j, β j := by
      simpa only [slack, one_mul, sub_eq_add_neg, Finset.sum_neg_distrib] using hg
    have hv := cavityPotentials_attain cost i₀
    have heq : fractionalAssignmentCost cost P = perturbedAssignmentValue cost 0 0 := by
      dsimp only [α, β] at hge
      linarith
    refine ⟨hP, ?_⟩
    intro Q hQ
    rw [heq]
    simpa only [perturbedEdgeCost_zero cost 0] using
      perturbedAssignmentValue_le_fractional cost 0 Q 0 hQ

end OTSelector
