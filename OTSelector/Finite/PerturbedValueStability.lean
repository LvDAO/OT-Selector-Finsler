import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.Assignment
import OTSelector.Finite.PerturbedValue

/-!
# Finite.PerturbedValueStability

**Conditions:** Two finite tilted matrices differ entrywise by at most the explicit real bound B.

**Objects:** An nB bound for every permutation objective and for the actual perturbed minimum.

**Proof detail:** Sum absolute edge errors along the n permutation entries, then evaluate the two attained minima at one another’s optimizers.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Entrywise stability of the perturbed assignment value

If two tilted edge matrices differ entrywise by at most `B`, then the least total
cost over permutations differs by at most `n * B`: both optimizers can be
evaluated against the other matrix.  This is the finite deterministic input of
the comparison between the actual physical cost matrix and the frozen marked-cube
cost matrix.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

variable {n : ℕ}

/-- Summing an entrywise bound gives an `n * B` bound on every assignment cost. -/
theorem abs_assignmentCost_sub_le (d₁ d₂ : Matrix (Fin n) (Fin n) ℝ) {B : ℝ}
    (h : ∀ i j, |d₁ i j - d₂ i j| ≤ B) (σ : Assignment n) :
    |assignmentCost d₁ σ - assignmentCost d₂ σ| ≤ n * B := by
  unfold assignmentCost
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (d₁ i (σ i) - d₂ i (σ i))|
      ≤ ∑ i, |d₁ i (σ i) - d₂ i (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ ↦ h i (σ i)
    _ = n * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Entrywise stability of the perturbed assignment value.**  Tilted matrices
that differ entrywise by at most `B` have least permutation costs differing by at
most `n * B`. -/
theorem abs_perturbedAssignmentValue_sub_le
    (c₁ g₁ c₂ g₂ : Matrix (Fin n) (Fin n) ℝ) (t B : ℝ)
    (h : ∀ i j, |(c₁ i j + t * g₁ i j) - (c₂ i j + t * g₂ i j)| ≤ B) :
    |perturbedAssignmentValue c₁ g₁ t - perturbedAssignmentValue c₂ g₂ t| ≤ n * B := by
  exact Analysis.Convex.abs_sub_le_of_isGLB_image
    (isGLB_perturbedAssignmentValue c₁ g₁ t) (isGLB_perturbedAssignmentValue c₂ g₂ t)
    (fun σ _ ↦ abs_assignmentCost_sub_le _ _ h σ)

end OTSelector
