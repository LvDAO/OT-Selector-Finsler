import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Finite.MaxCardValueScaling
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching

/-!
# Finite.MaxCardValueRelativeStability

**Conditions:** Nonnegative base costs, 0≤δ≤1, and entrywise relative error; tilted variants additionally have an absolute probe bound.

**Objects:** Monotone matching values and the relative kinetic perturbation of the tilted value.

**Proof detail:** Compare every feasible cost to (1±δ) times the original cost, use monotonicity and nonnegative homogeneity, and absorb the tilt through its uniform cardinality bound.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Relative stability of maximum-cardinality matching

Two elementary facts about the least maximum-cardinality cost:

* it is monotone in the edge costs;
* multiplying every nonnegative edge cost by a factor between `1 - delta` and
  `1 + delta` changes the value by at most `delta` times its size.

The second statement is the finite kernel-perturbation estimate: a relative
perturbation of the kinetic kernel perturbs the matching value relatively, with
no dependence on the number of points.  It is the algebraic input for comparing
a frozen physical kernel with the ideal local marked kernel.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector
namespace PartialMatching

variable {m n : ℕ}

/-- Monotonicity of the least maximum-cardinality cost in the edge costs. -/
theorem maxCardValue_mono {c d : Fin m → Fin n → ℝ} (h : ∀ i j, c i j ≤ d i j) :
    maxCardValue c ≤ maxCardValue d := by
  classical
  obtain ⟨σ, hσ, hσd⟩ := exists_cost_eq_maxCardValue d
  have h1 : maxCardValue c ≤ σ.cost c := maxCardValue_le_of_card c hσ
  have h2 : σ.cost c ≤ σ.cost d := by
    unfold cost
    exact Finset.sum_le_sum fun e _ => h e.1 e.2
  rw [hσd] at h2
  exact h1.trans h2

/-- **Relative stability for nonnegative costs.**  If each entry of `d` differs
from the nonnegative entry of `c` by at most a relative `delta <= 1`, the least
maximum-cardinality costs differ by at most `delta` times the size of the
value. -/
theorem abs_maxCardValue_sub_le_of_relative_nonneg {c d : Fin m → Fin n → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc : ∀ i j, 0 ≤ c i j)
    (h : ∀ i j, |d i j - c i j| ≤ δ * c i j) :
    |maxCardValue d - maxCardValue c| ≤ δ * maxCardValue c := by
  have hcM : 0 ≤ maxCardValue c := by
    obtain ⟨σ, hσ, hσc⟩ := exists_cost_eq_maxCardValue c
    rw [← hσc]
    unfold cost
    exact Finset.sum_nonneg fun e _ => hc e.1 e.2
  have hup : maxCardValue d ≤ (1 + δ) * maxCardValue c := by
    have hmono : maxCardValue d ≤ maxCardValue (fun i j => (1 + δ) * c i j) :=
      maxCardValue_mono fun i j => by
        have := (abs_le.mp (h i j)).2
        nlinarith [hc i j]
    rwa [maxCardValue_const_mul c (by linarith)] at hmono
  have hlow : (1 - δ) * maxCardValue c ≤ maxCardValue d := by
    have hmono : maxCardValue (fun i j => (1 - δ) * c i j) ≤ maxCardValue d :=
      maxCardValue_mono fun i j => by
        have := (abs_le.mp (h i j)).1
        nlinarith
    rwa [maxCardValue_const_mul c (by linarith)] at hmono
  rw [abs_le]
  constructor <;> nlinarith

/-- **Relative kinetic perturbation of the tilted value.**  If the nonnegative
kinetic matrix `c'` differs relatively by at most `delta <= 1` from `c`, and the
probe is bounded by `G`, then the tilted least costs differ by at most `delta`
times the tilted size plus the shift `|t| G` per matched pair. -/
theorem abs_maxCardValue_perturbed_sub_le_of_relative_kinetic
    {c c' g : Fin m → Fin n → ℝ} {t G δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hG0 : 0 ≤ G)
    (hc : ∀ i j, 0 ≤ c i j) (hg : ∀ i j, |g i j| ≤ G)
    (h : ∀ i j, |c' i j - c i j| ≤ δ * c i j) :
    |maxCardValue (fun i j => c' i j + t * g i j) -
        maxCardValue (fun i j => c i j + t * g i j)| ≤
      δ * (maxCardValue (fun i j => c i j + t * g i j) +
        (min m n : ℝ) * |t| * G) := by
  set K : ℝ := |t| * G with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg t) hG0
  have htg : ∀ i j, -(K) ≤ t * g i j := by
    intro i j
    have h1 : |t * g i j| ≤ K := by
      rw [abs_mul, hK]
      exact mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg t)
    exact (abs_le.mp h1).1
  have hnonneg : ∀ i j, 0 ≤ c i j + t * g i j + K := by
    intro i j
    linarith [hc i j, htg i j]
  have hrel : ∀ i j,
      |(c' i j + t * g i j + K) - (c i j + t * g i j + K)| ≤
        δ * (c i j + t * g i j + K) := by
    intro i j
    have h1 := h i j
    have hshift : 0 ≤ t * g i j + K := by linarith [htg i j]
    calc |(c' i j + t * g i j + K) - (c i j + t * g i j + K)|
        = |c' i j - c i j| := by ring_nf
      _ ≤ δ * c i j := h1
      _ ≤ δ * (c i j + t * g i j + K) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hδ0
  have hmain := abs_maxCardValue_sub_le_of_relative_nonneg hδ0 hδ1 hnonneg hrel
  have hm1 : maxCardValue (fun i j => c' i j + t * g i j + K) =
      maxCardValue (fun i j => c' i j + t * g i j) + (min m n : ℝ) * K :=
    maxCardValue_add_const (fun i j => c' i j + t * g i j) K
  have hm2 : maxCardValue (fun i j => c i j + t * g i j + K) =
      maxCardValue (fun i j => c i j + t * g i j) + (min m n : ℝ) * K :=
    maxCardValue_add_const (fun i j => c i j + t * g i j) K
  rw [hm1, hm2] at hmain
  have habs : |(maxCardValue (fun i j => c' i j + t * g i j) + (min m n : ℝ) * K) -
      (maxCardValue (fun i j => c i j + t * g i j) + (min m n : ℝ) * K)| =
      |maxCardValue (fun i j => c' i j + t * g i j) -
        maxCardValue (fun i j => c i j + t * g i j)| := by
    congr 1
    ring
  rw [habs] at hmain
  calc |maxCardValue (fun i j => c' i j + t * g i j) -
        maxCardValue (fun i j => c i j + t * g i j)|
      ≤ δ * (maxCardValue (fun i j => c i j + t * g i j) + (min m n : ℝ) * K) := hmain
    _ = δ * (maxCardValue (fun i j => c i j + t * g i j) +
          (min m n : ℝ) * |t| * G) := by
        rw [hK]
        ring

end PartialMatching
end OTSelector
