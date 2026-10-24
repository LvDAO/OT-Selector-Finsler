import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Analysis.Convex.InfimumComparison
import OTSelector.Finite.Assignment
import OTSelector.Finite.FractionalOptimal

/-!
# Finite.PerturbedValue

**Conditions:** Arbitrary finite real cost/probe matrices; empirical normalization assumes positive n where explicitly required.

**Objects:** The attained minimum of total assignment costs c+t g and its affine comparison with every original optimal permutation or fractional matrix.

**Proof detail:** Attain the finite minimum, identify its GLB, distribute the tilt through the objective, and evaluate at the unperturbed optimizer; divide the resulting inequality by the sample size for empirical averages.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95), Section 3.2.3, pp. 80–81 (p. 81 also states the concave infimum version).

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# The finite perturbed minimum and its whole-face affine comparison

For real edge matrices `cost` and `probe`, the perturbed value is the attained minimum of the
total assignment cost for `cost + t * probe`. Every unperturbed optimal permutation, and every
unperturbed optimal doubly-stochastic matrix, gives the exact affine upper bound on this value.
The comparison is derived from finite optimization, not assumed as a pressure hypothesis.

Fractional matrices have row and column sums one, so all costs and readouts are totals. The final
lemmas divide both the value and readout by `n`, assuming `0 < n`, to obtain empirical averages.
No geometric pressure limit or empirical selector convergence is asserted here.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- The actual edge matrix obtained by adding a scalar multiple of a paired probe. -/
def perturbedEdgeCost (cost probe : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ cost i j + t * probe i j

@[simp]
theorem perturbedEdgeCost_zero (cost probe : Matrix (Fin n) (Fin n) ℝ) :
    perturbedEdgeCost cost probe 0 = cost := by
  funext i j
  simp [perturbedEdgeCost]

/-- The value is the attained total minimum, defined using the existing finite optimizer. -/
noncomputable def perturbedAssignmentValue (cost probe : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) : ℝ :=
  assignmentCost (perturbedEdgeCost cost probe t)
    (optimalAssignment (perturbedEdgeCost cost probe t))

/-- The perturbed objective at each permutation has its exact affine expansion. -/
theorem assignmentCost_perturbedEdgeCost (cost probe : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (σ : Assignment n) :
    assignmentCost (perturbedEdgeCost cost probe t) σ =
      assignmentCost cost σ + t * assignmentCost probe σ := by
  simp [assignmentCost, perturbedEdgeCost, Finset.sum_add_distrib, Finset.mul_sum]

/-- The same affine expansion holds for every fractional matrix. -/
theorem fractionalAssignmentCost_perturbedEdgeCost
    (cost probe P : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    fractionalAssignmentCost (perturbedEdgeCost cost probe t) P =
      fractionalAssignmentCost cost P + t * fractionalAssignmentCost probe P := by
  simp [fractionalAssignmentCost, perturbedEdgeCost, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_left_comm]

/-- The defining finite minimum is attained at an actually optimal permutation. -/
theorem perturbedAssignmentValue_attained (cost probe : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) :
    ∃ σ, OptimalAssignment (perturbedEdgeCost cost probe t) σ ∧
      perturbedAssignmentValue cost probe t =
        assignmentCost (perturbedEdgeCost cost probe t) σ :=
  ⟨optimalAssignment (perturbedEdgeCost cost probe t), optimalAssignment_isOptimal _, rfl⟩

/-- The attained value is bounded by the objective of every competing permutation. -/
theorem perturbedAssignmentValue_le (cost probe : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (σ : Assignment n) :
    perturbedAssignmentValue cost probe t ≤ assignmentCost (perturbedEdgeCost cost probe t) σ :=
  optimalAssignment_isOptimal (perturbedEdgeCost cost probe t) σ

/-- The actual permutation minimum is the real infimum of all assignment objectives. -/
theorem isGLB_perturbedAssignmentValue (cost probe : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    IsGLB ((fun σ : Assignment n ↦ assignmentCost (perturbedEdgeCost cost probe t) σ) ''
      Set.univ) (perturbedAssignmentValue cost probe t) := by
  apply Analysis.Convex.isGLB_image_of_le_of_attained
  · exact fun σ _ ↦ perturbedAssignmentValue_le cost probe t σ
  · obtain ⟨σ, _, hσ⟩ := perturbedAssignmentValue_attained cost probe t
    exact ⟨σ, Set.mem_univ _, hσ.symm⟩

/-- Every optimal permutation realizes the same perturbed minimum, including ties. -/
theorem perturbedAssignmentValue_eq_of_optimal (cost probe : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (σ : Assignment n) (hσ : OptimalAssignment (perturbedEdgeCost cost probe t) σ) :
    perturbedAssignmentValue cost probe t = assignmentCost (perturbedEdgeCost cost probe t) σ :=
  le_antisymm (perturbedAssignmentValue_le cost probe t σ)
    (hσ (optimalAssignment (perturbedEdgeCost cost probe t)))

/-- Birkhoff's theorem bounds the same minimum by every feasible fractional objective. -/
theorem perturbedAssignmentValue_le_fractional (cost probe P : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    perturbedAssignmentValue cost probe t ≤
      fractionalAssignmentCost (perturbedEdgeCost cost probe t) P :=
  assignmentCost_le_fractionalAssignmentCost _ P _ (optimalAssignment_isOptimal _) hP

/-- Every optimal fractional matrix attains the actual permutation minimum. -/
theorem perturbedAssignmentValue_eq_of_optimalFractional
    (cost probe P : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hP : OptimalFractionalAssignment (perturbedEdgeCost cost probe t) P) :
    perturbedAssignmentValue cost probe t =
      fractionalAssignmentCost (perturbedEdgeCost cost probe t) P :=
  (optimalFractionalAssignment_cost_eq _ P hP _ (optimalAssignment_isOptimal _)).symm

/-- Every zero-tilt optimal permutation supplies the affine upper comparison at every tilt. -/
theorem perturbedAssignmentValue_le_of_optimal (cost probe : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (σ : Assignment n) (hσ : OptimalAssignment cost σ) :
    perturbedAssignmentValue cost probe t ≤
      perturbedAssignmentValue cost probe 0 + t * assignmentCost probe σ := by
  have hzero : perturbedAssignmentValue cost probe 0 = assignmentCost cost σ := by
    simpa only [perturbedEdgeCost_zero] using
      perturbedAssignmentValue_eq_of_optimal cost probe 0 σ (by simpa using hσ)
  rw [hzero]
  exact (perturbedAssignmentValue_le cost probe t σ).trans_eq
    (assignmentCost_perturbedEdgeCost cost probe t σ)

/-- The affine comparison holds on the entire unperturbed fractional optimal face. -/
theorem perturbedAssignmentValue_le_of_optimalFractional
    (cost probe P : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hP : OptimalFractionalAssignment cost P) :
    perturbedAssignmentValue cost probe t ≤
      perturbedAssignmentValue cost probe 0 + t * fractionalAssignmentCost probe P := by
  have hzero : perturbedAssignmentValue cost probe 0 = fractionalAssignmentCost cost P := by
    simpa only [perturbedEdgeCost_zero] using
      perturbedAssignmentValue_eq_of_optimalFractional cost probe P 0 (by simpa using hP)
  rw [hzero]
  exact (perturbedAssignmentValue_le_fractional cost probe P t hP.1).trans_eq
    (fractionalAssignmentCost_perturbedEdgeCost cost probe P t)

/-- Positive empirical normalization divides both the minimum and permutation readout by n. -/
theorem perturbedAssignmentValue_div_le_of_optimal (hn : 0 < n)
    (cost probe : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ) :
    perturbedAssignmentValue cost probe t / (n : ℝ) ≤
      perturbedAssignmentValue cost probe 0 / (n : ℝ) +
        t * (assignmentCost probe σ / (n : ℝ)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  simpa only [add_div, mul_div_assoc] using
    div_le_div_of_nonneg_right (perturbedAssignmentValue_le_of_optimal cost probe t σ hσ)
      hn'.le

/-- The same normalized affine bound holds for every optimal empirical fractional coupling. -/
theorem perturbedAssignmentValue_div_le_of_optimalFractional (hn : 0 < n)
    (cost probe P : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hP : OptimalFractionalAssignment cost P) :
    perturbedAssignmentValue cost probe t / (n : ℝ) ≤
      perturbedAssignmentValue cost probe 0 / (n : ℝ) +
        t * (fractionalAssignmentCost probe P / (n : ℝ)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  simpa only [add_div, mul_div_assoc] using
    div_le_div_of_nonneg_right
      (perturbedAssignmentValue_le_of_optimalFractional cost probe P t hP) hn'.le

end OTSelector
