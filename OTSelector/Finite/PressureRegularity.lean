import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.Assignment
import OTSelector.Finite.PerturbedValue
import OTSelector.Finite.PerturbedValueStability

/-!
# Finite.PressureRegularity

**Conditions:** Finite real cost/probe matrices, explicit entrywise bounds, and positive n for normalized pressure.

**Objects:** Concavity, Lipschitz continuity and uniform perturbation bounds for the normalized finite assignment value.

**Proof detail:** Use the common feasible infimum of affine objectives for concavity, bound each permutation slope by nG, and compare objectives at opposing minimizers before dividing by n.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95), Section 3.2.3, pp. 80–81 (p. 81 also states the concave infimum version); [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Finite assignment pressure regularity

The attained minimum of affine assignment objectives is concave in the tilt parameter.
An entrywise bound on the probe gives the same Lipschitz constant for the value divided by
sample size. Entrywise perturbations of both cost and probe also give a direct uniform stability
bound. These are finite optimization statements; no limiting pressure or differentiability is
assumed or concluded. All ties and arbitrary real cost matrices are allowed.
-/

open scoped BigOperators NNReal

namespace OTSelector
variable {n : ℕ}

/-- The actual finite pressure is concave because each competing assignment is affine. -/
theorem concaveOn_perturbedAssignmentValue (cost probe : Matrix (Fin n) (Fin n) ℝ) :
    ConcaveOn ℝ Set.univ (perturbedAssignmentValue cost probe) := by
  apply Analysis.Convex.concaveOn_of_isGLB_image convex_univ
    (fun t _ ↦ isGLB_perturbedAssignmentValue cost probe t)
  intro σ _
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [assignmentCost_perturbedEdgeCost, smul_eq_mul]
  have h : a * assignmentCost cost σ + b * assignmentCost cost σ = assignmentCost cost σ := by
    rw [← add_mul, hab, one_mul]
  nlinarith

/-- Dividing total pressure by sample size preserves concavity. -/
theorem concaveOn_perturbedAssignmentValue_div (cost probe : Matrix (Fin n) (Fin n) ℝ) :
    ConcaveOn ℝ Set.univ (fun t ↦ perturbedAssignmentValue cost probe t / (n : ℝ)) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (concaveOn_perturbedAssignmentValue cost probe).smul
      (inv_nonneg.mpr (Nat.cast_nonneg n : (0 : ℝ) ≤ n))

/-- The two attained finite minima differ by at most the summed entrywise objective error. -/
theorem perturbedAssignmentValue_abs_sub_le_of_edge_bound
    (cost probe cost' probe' : Matrix (Fin n) (Fin n) ℝ) (s t G : ℝ)
    (h : ∀ i j, |perturbedEdgeCost cost probe s i j -
      perturbedEdgeCost cost' probe' t i j| ≤ G) :
    |perturbedAssignmentValue cost probe s - perturbedAssignmentValue cost' probe' t| ≤
      (n : ℝ) * G := by
  exact Analysis.Convex.abs_sub_le_of_isGLB_image
    (isGLB_perturbedAssignmentValue cost probe s)
    (isGLB_perturbedAssignmentValue cost' probe' t)
    (fun σ _ ↦ abs_assignmentCost_sub_le _ _ h σ)

/-- After empirical normalization the entrywise error itself bounds the value error. -/
theorem perturbedAssignmentValue_div_abs_sub_le_of_edge_bound (hn : 0 < n)
    (cost probe cost' probe' : Matrix (Fin n) (Fin n) ℝ) (s t G : ℝ)
    (h : ∀ i j, |perturbedEdgeCost cost probe s i j -
      perturbedEdgeCost cost' probe' t i j| ≤ G) :
    |perturbedAssignmentValue cost probe s / (n : ℝ) -
      perturbedAssignmentValue cost' probe' t / (n : ℝ)| ≤ G := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← sub_div, abs_div, abs_of_pos hn']
  apply (div_le_iff₀ hn').mpr
  simpa only [mul_comm] using
    perturbedAssignmentValue_abs_sub_le_of_edge_bound cost probe cost' probe' s t G h

/-- A uniform probe bound gives exactly that Lipschitz constant for the normalized pressure. -/
theorem lipschitzWith_perturbedAssignmentValue_div (hn : 0 < n)
    (cost probe : Matrix (Fin n) (Fin n) ℝ) (G : ℝ≥0)
    (hprobe : ∀ i j, |probe i j| ≤ G) :
    LipschitzWith G (fun t ↦ perturbedAssignmentValue cost probe t / (n : ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [Real.dist_eq]
  apply perturbedAssignmentValue_div_abs_sub_le_of_edge_bound hn cost probe cost probe
  intro i j
  calc
    |perturbedEdgeCost cost probe s i j - perturbedEdgeCost cost probe t i j| =
        |s - t| * |probe i j| := by
          rw [← abs_mul]
          congr 1
          simp only [perturbedEdgeCost]
          ring
    _ ≤ |s - t| * G := mul_le_mul_of_nonneg_left (hprobe i j) (abs_nonneg _)
    _ = (G : ℝ) * |s - t| := mul_comm _ _

/-- Cost and probe perturbations are stable in their entrywise bounds at every fixed tilt. -/
theorem perturbedAssignmentValue_div_abs_sub_le (hn : 0 < n)
    (cost probe cost' probe' : Matrix (Fin n) (Fin n) ℝ) (t A B : ℝ)
    (hcost : ∀ i j, |cost i j - cost' i j| ≤ A)
    (hprobe : ∀ i j, |probe i j - probe' i j| ≤ B) :
    |perturbedAssignmentValue cost probe t / (n : ℝ) -
      perturbedAssignmentValue cost' probe' t / (n : ℝ)| ≤ A + |t| * B := by
  apply perturbedAssignmentValue_div_abs_sub_le_of_edge_bound hn cost probe cost' probe'
  intro i j
  calc
    |perturbedEdgeCost cost probe t i j - perturbedEdgeCost cost' probe' t i j| =
        |(cost i j - cost' i j) + t * (probe i j - probe' i j)| := by
          congr 1
          simp only [perturbedEdgeCost]
          ring
    _ ≤ |cost i j - cost' i j| + |t * (probe i j - probe' i j)| := abs_add_le _ _
    _ ≤ A + |t| * B := by rw [abs_mul]; gcongr; exact hcost i j; exact hprobe i j

end OTSelector
