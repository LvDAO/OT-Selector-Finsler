import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.Assignment
import OTSelector.Finite.FractionalOptimal
import OTSelector.Finite.PerturbedValue

/-!
# Finite.AssignmentCavity

**Conditions:** Every finite real square cost matrix, without uniqueness; deletion fixes a source row and target column.

**Objects:** Restricted/reinserted permutations, actual deleted assignment values, and the row-plus-vacancy envelope.

**Proof detail:** Construct inverse insertion/restriction maps and split their costs exactly; minimizing each side proves the cavity envelope and all optimal-partner equivalences, while the deleted-row value is unchanged by modifying that row.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The finite assignment variational problem is the classical foundation; these exact deleted-row identities and partner characterizations are local finite optimization consequences, not a textbook claim about a random tree or its law.
-/

/-!
# Exact finite assignment cavities

Deleting a specified source and a specified target gives an actual smaller assignment problem.
Its attained total value is the vacancy price. Reinserting the source yields the exact minimum
of the row cost plus those prices, and characterizes every optimal partner, including ties.
The prices do not depend on the deleted source row. These identities apply to every real cost
matrix without genericity, a selected optimizer, or a special geometric model.

The results are finite algebraic inputs to cavity disintegration. No random-tree assertion or
Dirichlet law is asserted here.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- Complete a smaller permutation by assigning the removed source to the vacant target. -/
def insertAssignment (i j : Fin (n + 1)) (τ : Assignment n) : Assignment (n + 1) :=
  (finSuccEquiv' i).trans ((Equiv.optionCongr τ).trans (finSuccEquiv' j).symm)

@[simp]
theorem insertAssignment_at (i j : Fin (n + 1)) (τ : Assignment n) :
    insertAssignment i j τ i = j := by
  simp [insertAssignment, Equiv.trans_apply]

@[simp]
theorem insertAssignment_succAbove (i j : Fin (n + 1)) (τ : Assignment n) (k : Fin n) :
    insertAssignment i j τ (i.succAbove k) = j.succAbove (τ k) := by
  simp [insertAssignment, Equiv.trans_apply]

/-- Restrict any permutation to the complements of a source and its actual partner. -/
def restrictAssignment (σ : Assignment (n + 1)) (i : Fin (n + 1)) : Assignment n :=
  (finSuccAboveEquiv i).trans
    ((σ.subtypeEquiv (p := fun k ↦ k ≠ i) (q := fun k ↦ k ≠ σ i)
      (fun _ ↦ σ.injective.ne_iff.symm)).trans (finSuccAboveEquiv (σ i)).symm)

@[simp]
theorem restrictAssignment_succAbove (σ : Assignment (n + 1)) (i : Fin (n + 1))
    (k : Fin n) :
    (σ i).succAbove (restrictAssignment σ i k) = σ (i.succAbove k) := by
  let x : {x : Fin (n + 1) // x ≠ σ i} :=
    ⟨σ (i.succAbove k), σ.injective.ne (i.succAbove_ne k)⟩
  exact congrArg Subtype.val ((finSuccAboveEquiv (σ i)).apply_symm_apply x)

@[simp]
theorem insertAssignment_restrictAssignment (σ : Assignment (n + 1)) (i : Fin (n + 1)) :
    insertAssignment i (σ i) (restrictAssignment σ i) = σ := by
  apply Equiv.ext
  intro k
  refine Fin.succAboveCases i ?_ (fun l ↦ ?_) k
  · exact insertAssignment_at i (σ i) _
  · simp


/-- The cost matrix after removing row `i` and target `j`, using increasing complement labels. -/
def assignmentCavityCost (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) : Fin n → Fin n → ℝ :=
  fun k l ↦ cost (i.succAbove k) (j.succAbove l)

/-- The actual total optimum with source `i` deleted and target `j` left vacant. -/
noncomputable def assignmentCavityValue (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) : ℝ :=
  perturbedAssignmentValue (assignmentCavityCost cost i j) 0 0

/-- The full row envelope at a possible partner, with the remainder optimized exactly. -/
noncomputable def assignmentRowEnvelope (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) : ℝ :=
  cost i j + assignmentCavityValue cost i j

private theorem zeroValue_le (cost : Fin n → Fin n → ℝ) (σ : Assignment n) :
    perturbedAssignmentValue cost 0 0 ≤ assignmentCost cost σ := by
  have h := perturbedAssignmentValue_le cost 0 0 σ
  rw [perturbedEdgeCost_zero cost 0] at h
  exact h

private theorem zeroValue_eq (cost : Fin n → Fin n → ℝ) (σ : Assignment n)
    (hσ : OptimalAssignment cost σ) :
    perturbedAssignmentValue cost 0 0 = assignmentCost cost σ := by
  have hσ' : OptimalAssignment (perturbedEdgeCost cost 0 0) σ := by
    rw [perturbedEdgeCost_zero cost 0]
    exact hσ
  have h := perturbedAssignmentValue_eq_of_optimal cost 0 0 σ hσ'
  rw [perturbedEdgeCost_zero cost 0] at h
  exact h

/-- The punctured matrix forgets the removed source row completely. -/
theorem assignmentCavityCost_congr_off_row (cost other : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (h : ∀ k, k ≠ i → ∀ l, cost k l = other k l)
    (j : Fin (n + 1)) :
    assignmentCavityCost cost i j = assignmentCavityCost other i j := by
  funext k l
  exact h (i.succAbove k) (i.succAbove_ne k) (j.succAbove l)

/-- Vacancy prices are functions of the retained rows alone, even when optimizers tie. -/
theorem assignmentCavityValue_congr_off_row (cost other : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (h : ∀ k, k ≠ i → ∀ l, cost k l = other k l)
    (j : Fin (n + 1)) :
    assignmentCavityValue cost i j = assignmentCavityValue other i j := by
  unfold assignmentCavityValue
  rw [assignmentCavityCost_congr_off_row cost other i h j]


/-- Insertion splits the total cost into the inserted edge and the complete smaller assignment. -/
theorem assignmentCost_insertAssignment (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (τ : Assignment n) :
    assignmentCost cost (insertAssignment i j τ) =
      cost i j + assignmentCost (assignmentCavityCost cost i j) τ := by
  unfold assignmentCost
  rw [Fin.sum_univ_succAbove _ i]
  simp only [insertAssignment_at, insertAssignment_succAbove, assignmentCavityCost]

/-- Every permutation has an exact deleted-row cost decomposition, regardless of optimality. -/
theorem assignmentCost_restrictAssignment (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (σ : Assignment (n + 1)) (i : Fin (n + 1)) :
    assignmentCost cost σ = cost i (σ i) +
      assignmentCost (assignmentCavityCost cost i (σ i)) (restrictAssignment σ i) := by
  unfold assignmentCost assignmentCavityCost
  rw [Fin.sum_univ_succAbove _ i]
  simp only [restrictAssignment_succAbove]

/-- Completing a minimizing vacancy gives an upper bound on the full attained minimum. -/
theorem assignmentValue_le_rowEnvelope (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    perturbedAssignmentValue cost 0 0 ≤ assignmentRowEnvelope cost i j := by
  let τ := optimalAssignment (assignmentCavityCost cost i j)
  have hτ := zeroValue_eq _ τ (optimalAssignment_isOptimal _)
  have h := zeroValue_le cost (insertAssignment i j τ)
  rw [assignmentCost_insertAssignment] at h
  simpa only [assignmentRowEnvelope, assignmentCavityValue, hτ] using h

/-- A permutation's chosen partner has row envelope no larger than its full cost. -/
theorem rowEnvelope_le_assignmentCost (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (σ : Assignment (n + 1)) (i : Fin (n + 1)) :
    assignmentRowEnvelope cost i (σ i) ≤ assignmentCost cost σ := by
  rw [assignmentCost_restrictAssignment cost σ i]
  unfold assignmentRowEnvelope assignmentCavityValue
  linarith [zeroValue_le (assignmentCavityCost cost i (σ i)) (restrictAssignment σ i)]

/-- Restricting any full optimum gives an actual optimum for its target vacancy. -/
theorem optimalAssignment_restrictAssignment (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (σ : Assignment (n + 1)) (hσ : OptimalAssignment cost σ) (i : Fin (n + 1)) :
    OptimalAssignment (assignmentCavityCost cost i (σ i)) (restrictAssignment σ i) := by
  intro τ
  have h := hσ (insertAssignment i (σ i) τ)
  rw [assignmentCost_restrictAssignment cost σ i, assignmentCost_insertAssignment] at h
  exact (add_le_add_iff_left _).mp h

/-- Every optimal partner attains the same full minimum in the row envelope. -/
theorem rowEnvelope_eq_value_of_optimal (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (σ : Assignment (n + 1)) (hσ : OptimalAssignment cost σ) (i : Fin (n + 1)) :
    assignmentRowEnvelope cost i (σ i) = perturbedAssignmentValue cost 0 0 := by
  apply le_antisymm
  · exact (rowEnvelope_le_assignmentCost cost σ i).trans_eq (zeroValue_eq cost σ hσ).symm
  · exact assignmentValue_le_rowEnvelope cost i (σ i)

/-- The full finite value is exactly the minimum over all vacancy envelopes. -/
theorem assignmentValue_eq_iInf_rowEnvelope (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    perturbedAssignmentValue cost 0 0 = ⨅ j, assignmentRowEnvelope cost i j := by
  apply le_antisymm
  · exact le_ciInf (assignmentValue_le_rowEnvelope cost i)
  · have hb : BddBelow (Set.range (assignmentRowEnvelope cost i)) :=
      ⟨perturbedAssignmentValue cost 0 0, by
        rintro _ ⟨j, rfl⟩
        exact assignmentValue_le_rowEnvelope cost i j⟩
    exact (ciInf_le hb ((optimalAssignment cost) i)).trans_eq
      (rowEnvelope_eq_value_of_optimal cost _ (optimalAssignment_isOptimal cost) i)

/-- Every minimizing envelope can be completed with every minimizing vacancy assignment. -/
theorem optimalAssignment_insertAssignment (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (τ : Assignment n)
    (hτ : OptimalAssignment (assignmentCavityCost cost i j) τ)
    (hj : ∀ k, assignmentRowEnvelope cost i j ≤ assignmentRowEnvelope cost i k) :
    OptimalAssignment cost (insertAssignment i j τ) := by
  have heq : assignmentCost cost (insertAssignment i j τ) =
      assignmentRowEnvelope cost i j := by
    rw [assignmentCost_insertAssignment]
    exact congrArg (cost i j + ·) (zeroValue_eq _ τ hτ).symm
  intro σ
  rw [heq]
  exact (hj (σ i)).trans (rowEnvelope_le_assignmentCost cost σ i)

/-- All full optimizers are exactly a minimizing row envelope and a minimizing remainder. -/
theorem optimalAssignment_iff_cavity (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (σ : Assignment (n + 1)) (i : Fin (n + 1)) :
    OptimalAssignment cost σ ↔
      OptimalAssignment (assignmentCavityCost cost i (σ i)) (restrictAssignment σ i) ∧
        ∀ j, assignmentRowEnvelope cost i (σ i) ≤ assignmentRowEnvelope cost i j := by
  constructor
  · intro hσ
    refine ⟨optimalAssignment_restrictAssignment cost σ hσ i, ?_⟩
    intro j
    rw [rowEnvelope_eq_value_of_optimal cost σ hσ i]
    exact assignmentValue_le_rowEnvelope cost i j
  · rintro ⟨hτ, hj⟩
    have h := optimalAssignment_insertAssignment cost i (σ i) (restrictAssignment σ i) hτ hj
    simpa only [insertAssignment_restrictAssignment] using h

/-- A target occurs as the chosen partner in some optimum exactly when its envelope minimizes.
This statement includes every tied minimizing partner and does not fix a permutation tie rule. -/
theorem exists_optimalAssignment_partner_iff (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    (∃ σ : Assignment (n + 1), OptimalAssignment cost σ ∧ σ i = j) ↔
      ∀ k, assignmentRowEnvelope cost i j ≤ assignmentRowEnvelope cost i k := by
  constructor
  · rintro ⟨σ, hσ, hji⟩
    simpa only [hji] using ((optimalAssignment_iff_cavity cost σ i).mp hσ).2
  · intro hj
    let τ := optimalAssignment (assignmentCavityCost cost i j)
    exact ⟨insertAssignment i j τ,
      optimalAssignment_insertAssignment cost i j τ (optimalAssignment_isOptimal _) hj,
      insertAssignment_at i j τ⟩


/-- Replacing the inserted row leaves every vacancy price unchanged. -/
@[simp]
theorem assignmentCavityValue_update_row (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (row : Fin (n + 1) → ℝ) :
    assignmentCavityValue (Function.update cost i row) i j = assignmentCavityValue cost i j := by
  apply assignmentCavityValue_congr_off_row
  intro k hk l
  simp only [Function.update_of_ne hk]

/-- An arbitrary new source row is optimized against the same punctured-input prices. -/
theorem assignmentValue_update_row (cost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (row : Fin (n + 1) → ℝ) :
    perturbedAssignmentValue (Function.update cost i row) 0 0 =
      ⨅ j, row j + assignmentCavityValue cost i j := by
  rw [assignmentValue_eq_iInf_rowEnvelope _ i]
  congr 1
  funext j
  simp [assignmentRowEnvelope]

/-- A nonminimizing vacancy cannot receive mass from its removed row in any fractional optimum. -/
theorem optimalFractionalAssignment_zero_of_not_cavity_min
    (cost P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hP : OptimalFractionalAssignment cost P) (i j : Fin (n + 1))
    (hj : ¬ ∀ k, assignmentRowEnvelope cost i j ≤ assignmentRowEnvelope cost i k) :
    P i j = 0 := by
  classical
  let readout : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun r s ↦ if r = i then if s = j then 1 else 0 else 0
  have hvalue (σ : Assignment (n + 1)) (hσ : OptimalAssignment cost σ) :
      assignmentCost readout σ = 0 := by
    have hne : σ i ≠ j := by
      intro heq
      exact hj ((exists_optimalAssignment_partner_iff cost i j).mp ⟨σ, hσ, heq⟩)
    simp [assignmentCost, readout, hne]
  have h := optimalFractionalAssignment_readout_eq cost readout P hP 0 hvalue
  simpa [fractionalAssignmentCost, readout, mul_ite] using h

/-- Every positive fractional partner lies in the same exact row-envelope minimum set. -/
theorem optimalFractionalAssignment_pos_cavity_min
    (cost P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hP : OptimalFractionalAssignment cost P) (i j : Fin (n + 1)) (hij : 0 < P i j) :
    ∀ k, assignmentRowEnvelope cost i j ≤ assignmentRowEnvelope cost i k := by
  by_contra hj
  have hz := optimalFractionalAssignment_zero_of_not_cavity_min cost P hP i j hj
  linarith

/-- The partner support of the entire fractional optimal face equals the vacancy argmin set. -/
theorem exists_optimalFractionalAssignment_pos_iff
    (cost : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    (∃ P, OptimalFractionalAssignment cost P ∧ 0 < P i j) ↔
      ∀ k, assignmentRowEnvelope cost i j ≤ assignmentRowEnvelope cost i k := by
  constructor
  · rintro ⟨P, hP, hij⟩
    exact optimalFractionalAssignment_pos_cavity_min cost P hP i j hij
  · intro hj
    obtain ⟨σ, hσ, heq⟩ := (exists_optimalAssignment_partner_iff cost i j).mpr hj
    refine ⟨σ.permMatrix ℝ, ⟨permMatrix_mem_doublyStochastic, ?_⟩, ?_⟩
    · intro Q hQ
      rw [fractionalAssignmentCost_permMatrix]
      exact assignmentCost_le_fractionalAssignmentCost cost Q σ hσ hQ
    · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, heq]


private theorem zeroValue_eq_iInf (cost : Fin n → Fin n → ℝ) :
    perturbedAssignmentValue cost 0 0 = ⨅ σ : Assignment n, assignmentCost cost σ := by
  apply le_antisymm
  · exact le_ciInf (zeroValue_le cost)
  · have hb : BddBelow (Set.range (assignmentCost cost)) :=
      ⟨perturbedAssignmentValue cost 0 0, by
        rintro _ ⟨σ, rfl⟩
        exact zeroValue_le cost σ⟩
    exact (ciInf_le hb (optimalAssignment cost)).trans_eq
      (zeroValue_eq cost _ (optimalAssignment_isOptimal cost)).symm

/-- Measurable retained edge costs give measurable exact vacancy prices, including at ties. -/
theorem measurable_assignmentCavityValue {Ω : Type*} [MeasurableSpace Ω]
    (cost : Ω → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hcost : ∀ k l, Measurable (fun ω ↦ cost ω k l)) (i j : Fin (n + 1)) :
    Measurable (fun ω ↦ assignmentCavityValue (cost ω) i j) := by
  simp only [assignmentCavityValue, zeroValue_eq_iInf]
  apply Measurable.iInf
  intro σ
  exact Finset.measurable_sum _ (fun k _ ↦ hcost (i.succAbove k) (j.succAbove (σ k)))

end OTSelector
