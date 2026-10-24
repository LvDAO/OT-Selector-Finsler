import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import OTSelector.Analysis.Convex.InfimumComparison
import OTSelector.Finite.PartialMatching


/-!
## Lemma skeleton

* **Conditions:** m,n are arbitrary finite cardinalities, including zero. c and d are arbitrary signed real edge-cost matrices. Value stability by cost_bound assumes a uniform bound on the cost difference for every maximum-cardinality feasible matching. The entrywise corollary assumes abs(c(i,j)-d(i,j)) <= B for all edges and multiplies B by min m n.
* **Objects:** maximum-cardinality feasible set: partial matchings of cardinality min m n; it is nonempty by the diagonal construction; maxCardValue: real sInf of the finite costs of that common feasible set; finite cost bound: an explicit lower bound derived from the finite sum of absolute edge costs; IsGLB certificate: the attained value is the greatest lower bound of the feasible objective image
* **Proof detail:** Bound every edge cost below by minus the sum of all absolute matrix entries, and every matching cardinality by m. Enumerate candidate finite edge sets, use a finite minimum of their costs, and reconstruct its matching certificate. Combine attainedness with the lower-bound and sInf rules to identify the IsGLB. Invoke the common-feasible-set infimum comparison and then bound the finite sum of edgewise differences.

## Mathematical sources

* Sheldon Axler, *Supplement for Measure, Integration & Real Analysis*, Section C, Definitions 0.32 and 0.35, pp. 18–19.
  https://measure.axler.net/SupplementMIRA.pdf#page=18
* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** Finite feasible costs attain a minimum; its GLB characterization and uniform-objective stability are elementary order consequences. The matching-specific cardinality factors and signed lower bound are derived locally.
-/

/-!
# The maximum-cardinality value for signed edge costs

`maxCardValue` is the infimum of the costs of maximum-cardinality matchings.
For arbitrary signed edge costs the value set is still bounded below (it is a
finite set), so any maximum-cardinality matching bounds the value from above.
These signed-cost comparison lemmas are used by the block decomposition and by
the tilt regularity, where the tilted costs are not nonnegative.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector

namespace PartialMatching

variable {m n : ℕ}

/-- The set of maximum-cardinality matching costs is bounded below, for arbitrary
signed edge costs. -/
theorem bddBelow_maxCardValue (c : Fin m → Fin n → ℝ) :
    BddBelow {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c} := by
  classical
  let K : ℝ := ∑ p : Fin m × Fin n, |c p.1 p.2|
  have hK : 0 ≤ K := Finset.sum_nonneg fun p _ ↦ abs_nonneg _
  refine ⟨-((m : ℝ) * K), ?_⟩
  rintro v ⟨σ, -, rfl⟩
  have hcard : ((σ.card : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast σ.card_le.trans (min_le_left m n)
  calc -((m : ℝ) * K) ≤ -(((σ.card : ℕ) : ℝ) * K) := by nlinarith
    _ = ∑ _e ∈ σ.edges, (-K) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [card]
      ring
    _ ≤ ∑ e ∈ σ.edges, c e.1 e.2 := by
      refine Finset.sum_le_sum fun e _ ↦ ?_
      have h1 : -|c e.1 e.2| ≤ c e.1 e.2 := neg_abs_le _
      have h2 : |c e.1 e.2| ≤ K := by
        have h := Finset.single_le_sum (s := Finset.univ)
          (f := fun p : Fin m × Fin n ↦ |c p.1 p.2|) (fun p _ ↦ abs_nonneg _)
          (Finset.mem_univ e)
        simpa only [K] using h
      linarith

/-- The value at any maximum-cardinality matching bounds the least value, for
arbitrary signed edge costs. -/
theorem maxCardValue_le_of_card (c : Fin m → Fin n → ℝ) {σ : PartialMatching m n}
    (hσ : σ.card = min m n) :
    maxCardValue c ≤ σ.cost c := by
  classical
  unfold maxCardValue
  exact csInf_le (bddBelow_maxCardValue c) ⟨σ, hσ, rfl⟩

/-- The least cost of m maximum-cardinality matching is attained. -/
theorem exists_cost_eq_maxCardValue (c : Fin m → Fin n → ℝ) :
    ∃ σ : PartialMatching m n, σ.card = min m n ∧ σ.cost c = maxCardValue c := by
  classical
  let costOf : Finset (Fin m × Fin n) → ℝ := fun e ↦ ∑ p ∈ e, c p.1 p.2
  let cand : Finset (Finset (Fin m × Fin n)) :=
    Finset.univ.filter fun e ↦ ∃ σ : PartialMatching m n, σ.edges = e ∧ σ.card = min m n
  have hcand : cand.Nonempty := by
    refine ⟨(diagonal m n).edges, ?_⟩
    simp only [cand, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨diagonal m n, rfl, card_diagonal m n⟩
  let e0 : ℝ := (cand.image costOf).min' (hcand.image costOf)
  have he0mem : e0 ∈ cand.image costOf := Finset.min'_mem _ _
  obtain ⟨e, he, he0⟩ := Finset.mem_image.mp he0mem
  obtain ⟨σ, hedges, hcard⟩ := (Finset.mem_filter.mp he).2
  have hcost : σ.cost c = e0 := by
    rw [← he0]
    unfold PartialMatching.cost costOf
    rw [hedges]
  refine ⟨σ, hcard, hcost.trans ?_⟩
  -- `e0` is m lower bound of the set of maximum-cardinality costs, and is itself one.
  have hSne : {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c}.Nonempty :=
    ⟨_, σ, hcard, rfl⟩
  have hlow : ∀ v ∈ {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c},
      e0 ≤ v := by
    rintro v ⟨τ, hτ, rfl⟩
    apply Finset.min'_le
    apply Finset.mem_image.mpr
    refine ⟨τ.edges, ?_, rfl⟩
    simp only [cand, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨τ, rfl, hτ⟩
  have hlowmem : e0 ∈ {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c} :=
    ⟨σ, hcard, hcost.symm⟩
  unfold PartialMatching.maxCardValue
  exact le_antisymm (le_csInf hSne hlow) (csInf_le ⟨e0, hlow⟩ hlowmem)


/-- The real infimum of the common maximum-cardinality feasible set. -/
theorem isGLB_maxCardValue (c : Fin m → Fin n → ℝ) :
    IsGLB ((fun σ : PartialMatching m n ↦ σ.cost c) '' {σ | σ.card = min m n})
      (maxCardValue c) := by
  apply Analysis.Convex.isGLB_image_of_le_of_attained
  · exact fun σ hσ ↦ maxCardValue_le_of_card c hσ
  · obtain ⟨σ, hσ, hcost⟩ := exists_cost_eq_maxCardValue c
    exact ⟨σ, hσ, hcost⟩

/-- A uniform error on complete feasible objectives bounds the matching value error. -/
theorem abs_maxCardValue_sub_le_of_cost_bound (c d : Fin m → Fin n → ℝ) {B : ℝ}
    (hbound : ∀ σ : PartialMatching m n, σ.card = min m n →
      |σ.cost c - σ.cost d| ≤ B) : |maxCardValue c - maxCardValue d| ≤ B :=
  Analysis.Convex.abs_sub_le_of_isGLB_image
    (isGLB_maxCardValue c) (isGLB_maxCardValue d) hbound


/-- Uniform edge errors bound the matching-value error by the number of matched edges. -/
theorem abs_maxCardValue_sub_le_of_entrywise {m n : ℕ} (c d : Fin m → Fin n → ℝ) {B : ℝ}
    (hB : ∀ i j, |c i j - d i j| ≤ B) :
    |maxCardValue c - maxCardValue d| ≤ ((min m n : ℕ) : ℝ) * B := by
  apply abs_maxCardValue_sub_le_of_cost_bound
  intro σ hσ
  unfold cost
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ e ∈ σ.edges, (c e.1 e.2 - d e.1 e.2)| ≤
        ∑ e ∈ σ.edges, |c e.1 e.2 - d e.1 e.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ σ.edges, B := Finset.sum_le_sum fun e _ ↦ hB e.1 e.2
    _ = ((min m n : ℕ) : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simpa only [card] using congrArg (fun k : ℕ ↦ (k : ℝ) * B) hσ

end PartialMatching

end OTSelector
