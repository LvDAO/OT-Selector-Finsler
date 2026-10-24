import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.Assignment

/-!
# Finite.FractionalOptimal

**Conditions:** Finite real square matrices have unit row and column sums; all optimizer ties are retained.

**Objects:** Doubly stochastic matrices, their assignment cost, and the entire fractional optimal face.

**Proof detail:** Apply Birkhoff’s convex decomposition into permutation matrices; linearity identifies the cost and forces every positively weighted permutation to be optimal, then average any common readout bound.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Peyré–Cuturi Proposition 2.1 and its proof state the Birkhoff/assignment principle. The support-on-optimal-permutations and whole-face readout statements follow locally from nonnegative weighted gaps.
-/

/-!
# The full fractional optimal face of a finite assignment problem

Matrices here have row and column sums one. Their linear costs are total assignment costs;
for positive n, empirical probability couplings and readouts divide both by n.
Mathlib's Birkhoff theorem supplies an actual permutation decomposition. Optimality forces
every positive-weight permutation to minimize the original cost. Thus a linear readout bound
on all optimal permutations holds on the whole fractional optimal face.

This is a finite algebraic ingredient; it asserts no geometric or asymptotic selector theorem.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- The total linear cost of a matrix with unit row and column capacities. -/
def fractionalAssignmentCost (cost P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, P i j * cost i j

/-- Minimization is over the entire doubly-stochastic polytope, without a support assumption. -/
def OptimalFractionalAssignment (cost P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P ∈ doublyStochastic ℝ (Fin n) ∧
    ∀ Q ∈ doublyStochastic ℝ (Fin n),
      fractionalAssignmentCost cost P ≤ fractionalAssignmentCost cost Q

private def fractionalCostLinearMap (cost : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun := fractionalAssignmentCost cost
  map_add' P Q := by
    simp [fractionalAssignmentCost, add_mul, Finset.sum_add_distrib]
  map_smul' a P := by
    simp [fractionalAssignmentCost, Finset.mul_sum, mul_assoc]

@[simp]
theorem fractionalAssignmentCost_permMatrix (cost : Matrix (Fin n) (Fin n) ℝ)
    (σ : Assignment n) :
    fractionalAssignmentCost cost (σ.permMatrix ℝ) = assignmentCost cost σ := by
  simp [fractionalAssignmentCost, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, assignmentCost]

/-- A Birkhoff decomposition preserves every linear paired readout. -/
theorem fractionalAssignmentCost_sum_perm (cost : Matrix (Fin n) (Fin n) ℝ)
    (w : Assignment n → ℝ) :
    fractionalAssignmentCost cost (∑ σ, w σ • σ.permMatrix ℝ) =
      ∑ σ, w σ * assignmentCost cost σ := by
  change fractionalCostLinearMap cost (∑ σ, w σ • σ.permMatrix ℝ) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun σ _ ↦ congrArg (w σ * ·)
    (fractionalAssignmentCost_permMatrix cost σ)

/-- A minimizing permutation already bounds below every feasible fractional matrix. -/
theorem assignmentCost_le_fractionalAssignmentCost
    (cost P : Matrix (Fin n) (Fin n) ℝ) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ) (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    assignmentCost cost σ ≤ fractionalAssignmentCost cost P := by
  obtain ⟨w, hw, hsum, hdecomp⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  rw [← hdecomp, fractionalAssignmentCost_sum_perm]
  calc
    assignmentCost cost σ = (∑ τ, w τ) * assignmentCost cost σ := by rw [hsum, one_mul]
    _ = ∑ τ, w τ * assignmentCost cost σ := Finset.sum_mul _ _ _
    _ ≤ ∑ τ, w τ * assignmentCost cost τ :=
      Finset.sum_le_sum fun τ _ ↦ mul_le_mul_of_nonneg_left (hσ τ) (hw τ)

/-- Every finite cost matrix has a minimizing doubly-stochastic matrix. -/
theorem exists_optimalFractionalAssignment (cost : Matrix (Fin n) (Fin n) ℝ) :
    ∃ P, OptimalFractionalAssignment cost P := by
  obtain ⟨σ, hσ⟩ := exists_optimalAssignment cost
  refine ⟨σ.permMatrix ℝ, permMatrix_mem_doublyStochastic, ?_⟩
  intro Q hQ
  rw [fractionalAssignmentCost_permMatrix]
  exact assignmentCost_le_fractionalAssignmentCost cost Q σ hσ hQ

/-- Fractional and permutation optima have exactly the same unnormalized minimum value. -/
theorem optimalFractionalAssignment_cost_eq (cost P : Matrix (Fin n) (Fin n) ℝ)
    (hP : OptimalFractionalAssignment cost P) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ) :
    fractionalAssignmentCost cost P = assignmentCost cost σ := by
  apply le_antisymm
  · simpa only [fractionalAssignmentCost_permMatrix] using
      hP.2 (σ.permMatrix ℝ) permMatrix_mem_doublyStochastic
  · exact assignmentCost_le_fractionalAssignmentCost cost P σ hσ hP.1

/-- Every fractional optimum decomposes into optimal permutations on the original cost matrix. -/
theorem optimalFractionalAssignment_decomposition (cost P : Matrix (Fin n) (Fin n) ℝ)
    (hP : OptimalFractionalAssignment cost P) :
    ∃ w : Assignment n → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∑ σ, w σ • σ.permMatrix ℝ = P) ∧
      ∀ σ, 0 < w σ → OptimalAssignment cost σ := by
  obtain ⟨σ₀, hσ₀⟩ := exists_optimalAssignment cost
  obtain ⟨w, hw, hsum, hdecomp⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP.1
  refine ⟨w, hw, hsum, hdecomp, ?_⟩
  have hcost : ∑ σ, w σ * assignmentCost cost σ = assignmentCost cost σ₀ := by
    rw [← fractionalAssignmentCost_sum_perm, hdecomp]
    exact optimalFractionalAssignment_cost_eq cost P hP σ₀ hσ₀
  have hzero : ∑ σ, w σ * (assignmentCost cost σ - assignmentCost cost σ₀) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hcost, ← Finset.sum_mul, hsum, one_mul, sub_self]
  have hnonneg (σ : Assignment n) :
      0 ≤ w σ * (assignmentCost cost σ - assignmentCost cost σ₀) :=
    mul_nonneg (hw σ) (sub_nonneg.mpr (hσ₀ σ))
  intro σ hpos τ
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun κ _ ↦ hnonneg κ)).mp hzero σ
    (Finset.mem_univ σ)
  have heq : assignmentCost cost σ = assignmentCost cost σ₀ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt hpos))
  rw [heq]
  exact hσ₀ τ

/-- Simultaneous readout bounds on optimal permutations hold on every fractional optimum. -/
theorem optimalFractionalAssignment_readout_bounds
    (cost readout P : Matrix (Fin n) (Fin n) ℝ)
    (hP : OptimalFractionalAssignment cost P) (lower upper : ℝ)
    (hbound : ∀ σ, OptimalAssignment cost σ →
      lower ≤ assignmentCost readout σ ∧ assignmentCost readout σ ≤ upper) :
    lower ≤ fractionalAssignmentCost readout P ∧
      fractionalAssignmentCost readout P ≤ upper := by
  obtain ⟨w, hw, hsum, hdecomp, hopt⟩ := optimalFractionalAssignment_decomposition cost P hP
  have hterm (σ : Assignment n) :
      w σ * lower ≤ w σ * assignmentCost readout σ ∧
        w σ * assignmentCost readout σ ≤ w σ * upper := by
    by_cases hz : w σ = 0
    · simp [hz]
    · have hp : 0 < w σ := lt_of_le_of_ne (hw σ) (Ne.symm hz)
      exact ⟨mul_le_mul_of_nonneg_left (hbound σ (hopt σ hp)).1 (hw σ),
        mul_le_mul_of_nonneg_left (hbound σ (hopt σ hp)).2 (hw σ)⟩
  rw [← hdecomp, fractionalAssignmentCost_sum_perm]
  constructor
  · calc
      lower = ∑ σ, w σ * lower := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ σ, w σ * assignmentCost readout σ := Finset.sum_le_sum fun σ _ ↦ (hterm σ).1
  · calc
      ∑ σ, w σ * assignmentCost readout σ ≤ ∑ σ, w σ * upper :=
        Finset.sum_le_sum fun σ _ ↦ (hterm σ).2
      _ = upper := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A common readout value on optimal permutations is common to the full fractional face. -/
theorem optimalFractionalAssignment_readout_eq
    (cost readout P : Matrix (Fin n) (Fin n) ℝ)
    (hP : OptimalFractionalAssignment cost P) (value : ℝ)
    (hvalue : ∀ σ, OptimalAssignment cost σ → assignmentCost readout σ = value) :
    fractionalAssignmentCost readout P = value := by
  have h := optimalFractionalAssignment_readout_bounds cost readout P hP value value
    (fun σ hσ ↦ by rw [hvalue σ hσ]; exact ⟨le_rfl, le_rfl⟩)
  exact le_antisymm h.2 h.1

end OTSelector
