import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching

/-!
# Finite.MaxCardValueRegularity

**Conditions:** Finite real base and probe costs; uniform absolute probe/cost bounds are given explicitly.

**Objects:** Tilted maximum-cardinality value, a concave Lipschitz lower envelope of affine matching objectives.

**Proof detail:** Represent the value by the common feasible infimum; finite sums bound every matching slope, and evaluation at opposing minimizers transfers the uniform objective error to the minima.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95), Section 3.2.3, pp. 80–81 (p. 81 also states the concave infimum version); [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Regularity of the maximum-cardinality value in the tilt

For a fixed base cost `c` and probe `g`, the tilted value
`t ↦ maxCardValue (c + t g)` is concave (a minimum of affine functions), is
Lipschitz with constant `min m n * ‖g‖`, and is bounded by the maximum
cardinality times the largest edge cost.  These are the analytic inputs of the
finite-volume pressure limit in the tilt variable.

The costs here are signed, so the comparison lemmas do not assume nonnegativity;
boundedness below of the finite value set is proved directly.
-/

open scoped BigOperators Pointwise

noncomputable section
namespace OTSelector

namespace PartialMatching

variable {m n : ℕ}

/-- The maximum-cardinality value is concave in the tilt. -/
theorem concaveOn_maxCardValue_perturbed (c g : Fin m → Fin n → ℝ) :
    ConcaveOn ℝ Set.univ
      (fun t ↦ maxCardValue (fun i j ↦ c i j + t * g i j)) := by
  apply Analysis.Convex.concaveOn_of_isGLB_image convex_univ
    (fun t _ ↦ isGLB_maxCardValue (fun i j ↦ c i j + t * g i j))
  intro σ _
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  simp only [smul_eq_mul, cost]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro e _
  have h : (a + b) * c e.1 e.2 = c e.1 e.2 := by rw [hab, one_mul]
  nlinarith

/-- The probe cost of a maximum-cardinality matching is bounded by the maximum
cardinality times the uniform probe bound. -/
theorem abs_cost_le_card_mul {g : Fin m → Fin n → ℝ} {G : ℝ}
    (hg : ∀ i j, |g i j| ≤ G) (σ : PartialMatching m n) :
    |σ.cost g| ≤ (σ.card : ℝ) * G := by
  unfold cost
  calc |∑ e ∈ σ.edges, g e.1 e.2| ≤ ∑ e ∈ σ.edges, |g e.1 e.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ σ.edges, G := Finset.sum_le_sum fun e _ ↦ hg e.1 e.2
    _ = (σ.card : ℝ) * G := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [card]

set_option linter.unusedVariables false in
/-- Lipschitz dependence of the value on the tilt. -/
theorem abs_maxCardValue_perturbed_sub_le (c g : Fin m → Fin n → ℝ) {G t u : ℝ}
    (hg : ∀ i j, |g i j| ≤ G) (hG0 : 0 ≤ G) :
    |maxCardValue (fun i j ↦ c i j + t * g i j) -
        maxCardValue (fun i j ↦ c i j + u * g i j)| ≤
      |t - u| * ((min m n : ℕ) : ℝ) * G := by
  apply abs_maxCardValue_sub_le_of_cost_bound
  intro σ hσ
  have hcost : σ.cost (fun i j ↦ c i j + t * g i j) -
      σ.cost (fun i j ↦ c i j + u * g i j) = (t - u) * σ.cost g := by
    simp only [cost, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hcost, abs_mul]
  calc
    |t - u| * |σ.cost g| ≤ |t - u| * ((σ.card : ℝ) * G) :=
      mul_le_mul_of_nonneg_left (abs_cost_le_card_mul hg σ) (abs_nonneg _)
    _ = |t - u| * ((min m n : ℕ) : ℝ) * G := by rw [hσ]; ring

/-- Uniform boundedness of the tilted value by the maximum cardinality times the
largest edge cost. -/
theorem abs_maxCardValue_perturbed_le (c g : Fin m → Fin n → ℝ) {Bc G t : ℝ}
    (hc : ∀ i j, |c i j| ≤ Bc) (hBc0 : 0 ≤ Bc) (hg : ∀ i j, |g i j| ≤ G)
    (hG0 : 0 ≤ G) :
    |maxCardValue (fun i j ↦ c i j + t * g i j)| ≤
      ((min m n : ℕ) : ℝ) * (Bc + |t| * G) := by
  obtain ⟨σ, hσ, hσc⟩ := exists_cost_eq_maxCardValue
    (fun i j ↦ c i j + t * g i j)
  have hedge : ∀ i j, |c i j + t * g i j| ≤ Bc + |t| * G := by
    intro i j
    calc |c i j + t * g i j| ≤ |c i j| + |t * g i j| := abs_add_le _ _
      _ = |c i j| + |t| * |g i j| := by rw [abs_mul]
      _ ≤ Bc + |t| * G := by
          have := mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg t)
          linarith [hc i j]
  have hcard : ((σ.card : ℕ) : ℝ) ≤ ((min m n : ℕ) : ℝ) := by rw [hσ]
  rw [← hσc]
  calc |σ.cost (fun i j ↦ c i j + t * g i j)| ≤
        ∑ e ∈ σ.edges, |c e.1 e.2 + t * g e.1 e.2| := by
        unfold cost
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ σ.edges, (Bc + |t| * G) := Finset.sum_le_sum fun e _ ↦ hedge e.1 e.2
    _ = (σ.card : ℝ) * (Bc + |t| * G) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [card]
    _ ≤ ((min m n : ℕ) : ℝ) * (Bc + |t| * G) :=
        mul_le_mul_of_nonneg_right hcard (by
          have := abs_nonneg t
          nlinarith [abs_nonneg t, hG0, hBc0])

end PartialMatching

end OTSelector
