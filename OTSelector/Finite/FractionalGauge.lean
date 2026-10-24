import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.FractionalOptimal
import OTSelector.Finite.PerturbedValue

/-!
# Finite.FractionalGauge

**Conditions:** A doubly stochastic finite matrix and positive objective scale; the potential is arbitrary for invariance and one-Lipschitz for slack nonnegativity.

**Objects:** Endpoint-potential gauge changes and the unchanged entire fractional optimal face.

**Proof detail:** Sum row and column additions against their unit marginals to obtain a fixed additive objective constant; positive scaling preserves order, and the Lipschitz inequality makes the distance slack nonnegative.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Exact potential subtraction on the full finite fractional face

Subtracting endpoint potentials from a distance cost changes every feasible objective by the
same marginal-dependent constant. Positive scaling therefore preserves the entire fractional
optimal set. A one-Lipschitz potential makes the distance slack nonnegative, but this property
is not needed for invariance. No optimum or limiting selector is chosen.

Matrices have unit row and column sums. Dividing their costs by the positive sample size gives
the empirical-probability normalization used in the pressure construction.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- On a feasible fractional matrix, row and column additions contribute fixed marginal sums. -/
theorem fractionalAssignmentCost_scale_add_rowColumn
    (cost P : Matrix (Fin n) (Fin n) ℝ) (k : ℝ) (row column : Fin n → ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    fractionalAssignmentCost (fun i j ↦ k * cost i j + row i + column j) P =
      k * fractionalAssignmentCost cost P + ∑ i, row i + ∑ j, column j := by
  have hrow : (∑ i, ∑ j, P i j * row i) = ∑ i, row i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP i, one_mul]
  have hcolumn : (∑ i, ∑ j, P i j * column j) = ∑ j, column j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hP j, one_mul]
  have hscale : (∑ i, ∑ j, P i j * (k * cost i j)) =
      k * fractionalAssignmentCost cost P := by
    simp only [fractionalAssignmentCost, Finset.mul_sum, mul_left_comm]
  simp only [fractionalAssignmentCost, mul_add, Finset.sum_add_distrib]
  rw [hrow, hcolumn, hscale]
  rfl

/-- Positive scaling and endpoint additions preserve every fractional minimizer, including ties. -/
theorem optimalFractionalAssignment_posScale_add_rowColumn_iff
    (cost P : Matrix (Fin n) (Fin n) ℝ) (k : ℝ) (hk : 0 < k)
    (row column : Fin n → ℝ) :
    OptimalFractionalAssignment (fun i j ↦ k * cost i j + row i + column j) P ↔
      OptimalFractionalAssignment cost P := by
  constructor
  · rintro ⟨hP, hmin⟩
    refine ⟨hP, fun Q hQ ↦ ?_⟩
    have h := hmin Q hQ
    rw [fractionalAssignmentCost_scale_add_rowColumn cost P k row column hP,
      fractionalAssignmentCost_scale_add_rowColumn cost Q k row column hQ] at h
    simpa only [add_le_add_iff_right, mul_le_mul_iff_right₀ hk] using h
  · rintro ⟨hP, hmin⟩
    refine ⟨hP, fun Q hQ ↦ ?_⟩
    rw [fractionalAssignmentCost_scale_add_rowColumn cost P k row column hP,
      fractionalAssignmentCost_scale_add_rowColumn cost Q k row column hQ]
    simpa only [add_le_add_iff_right, mul_le_mul_iff_right₀ hk] using hmin Q hQ

section Distance

variable {M : Type*} [PseudoMetricSpace M]

/-- The true distance minus the increase in a potential, evaluated on two sample lists. -/
def distanceSlackEdgeCost (X Y : Fin n → M) (φ : M → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ dist (X i) (Y j) - φ (Y j) + φ (X i)

/-- The distance slack of a one-Lipschitz potential is nonnegative on every sampled pair. -/
theorem distanceSlackEdgeCost_nonneg (X Y : Fin n → M) (φ : M → ℝ)
    (hφ : LipschitzWith 1 φ) (i j : Fin n) :
    0 ≤ distanceSlackEdgeCost X Y φ i j := by
  have h := hφ.le_add_mul (Y j) (X i)
  simp only [NNReal.coe_one, one_mul, dist_comm (Y j) (X i)] at h
  dsimp only [distanceSlackEdgeCost]
  linarith

/-- The gauged and positively rescaled distance problem has exactly the original fractional face.
No calibration, optimality, or regularity premise on the potential is needed for this identity. -/
theorem optimalFractionalAssignment_distanceSlack_iff
    (X Y : Fin n → M) (φ : M → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (k : ℝ) (hk : 0 < k) :
    OptimalFractionalAssignment (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) P ↔
      OptimalFractionalAssignment (fun i j ↦ dist (X i) (Y j)) P := by
  have hcost : (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) =
      (fun i j ↦ k * dist (X i) (Y j) + k * φ (X i) + (-k * φ (Y j))) := by
    funext i j
    dsimp only [distanceSlackEdgeCost]
    ring
  rw [hcost]
  exact optimalFractionalAssignment_posScale_add_rowColumn_iff _ P k hk _ _

/-- The actual normalized slack pressure compares against every original distance optimum.
This supplies the affine premise used in the pressure selector, with the empirical readout
normalized by the sample size. No convergence of the pressure is assumed or concluded. -/
theorem perturbedDistanceSlackValue_div_le_of_optimalFractional
    (hn : 0 < n) (X Y : Fin n → M) (φ : M → ℝ)
    (probe P : Matrix (Fin n) (Fin n) ℝ) (k : ℝ) (hk : 0 < k) (t : ℝ)
    (hP : OptimalFractionalAssignment (fun i j ↦ dist (X i) (Y j)) P) :
    perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) probe t /
        (n : ℝ) ≤
      perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) probe 0 /
        (n : ℝ) + t * (fractionalAssignmentCost probe P / (n : ℝ)) :=
  perturbedAssignmentValue_div_le_of_optimalFractional hn _ probe P t
    ((optimalFractionalAssignment_distanceSlack_iff X Y φ P k hk).mpr hP)

end Distance

end OTSelector
