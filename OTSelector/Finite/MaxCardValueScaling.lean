import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic
import OTSelector.Finite.PartialMatching

/-!
# Finite.MaxCardValueScaling

**Conditions:** Finite rectangular matchings; multiplicative scale is nonnegative for the value identity, and geometric rescaling is strictly positive.

**Objects:** Signed matching cost, least maximum-cardinality cost, and degree-two homogeneous edge kernels.

**Proof detail:** Distribute finite sums through multiplication and constant addition; all feasible full-cardinality matchings have min(m,n) edges, so the same transformations pass through the attained minimum.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Scaling and translation of maximum-cardinality matching values

The finite-volume pressure is compared across scales through two elementary
operations on the cost matrix: multiplying every edge cost by a nonnegative
constant, and adding the same constant to every edge.  Both act on
`maxCardValue` exactly, the first by homogeneity and the second through the
maximum cardinality `min m n`.

The final lemmas record the self-similar identity of a two-homogeneous edge
kernel, which is the algebraic content of the scaling step in the pressure
recursion.
-/

open scoped BigOperators Pointwise

noncomputable section
namespace OTSelector

namespace PartialMatching

variable {m n : ℕ}

/-- Multiplying every edge cost by a constant multiplies the total cost. -/
theorem cost_const_mul (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n) (a : ℝ) :
    σ.cost (fun i j ↦ a * c i j) = a * σ.cost c := by
  unfold cost
  rw [Finset.mul_sum]

/-- Adding a constant to every edge adds the cardinality times that constant. -/
theorem cost_add_const (c : Fin m → Fin n → ℝ) (σ : PartialMatching m n) (B : ℝ) :
    σ.cost (fun i j ↦ c i j + B) = σ.cost c + (σ.card : ℝ) * B := by
  unfold cost card
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

/-- The least maximum-cardinality cost is homogeneous for nonnegative scaling. -/
theorem maxCardValue_const_mul (c : Fin m → Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    maxCardValue (fun i j ↦ a * c i j) = a * maxCardValue c := by
  classical
  let S : Set ℝ := {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c}
  let K : ℝ := ∑ p : Fin m × Fin n, |c p.1 p.2|
  have hK : 0 ≤ K := Finset.sum_nonneg fun p _ ↦ abs_nonneg _
  have hne : S.Nonempty := ⟨_, diagonal m n, card_diagonal m n, rfl⟩
  have hbdd : BddBelow S := by
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
  have hset : {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧
      v = σ.cost (fun i j ↦ a * c i j)} = (fun v ↦ a * v) '' S := by
    ext v
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ.cost c, ⟨σ, hσ, rfl⟩, by simp only [cost_const_mul]⟩
    · rintro ⟨w, ⟨σ, hσ, rfl⟩, rfl⟩
      exact ⟨σ, hσ, by simp only [cost_const_mul]⟩
  have hmv : maxCardValue (fun i j ↦ a * c i j) = sInf ((fun v ↦ a * v) '' S) := by
    unfold maxCardValue
    exact congrArg sInf hset
  have hS'ne : ((fun v ↦ a * v) '' S).Nonempty := hne.image _
  have hbdd' : BddBelow ((fun v ↦ a * v) '' S) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨a * b, by
      rintro w ⟨v, hv, rfl⟩
      exact mul_le_mul_of_nonneg_left (hb hv) ha⟩
  have hmv' : maxCardValue c = sInf S := rfl
  rw [hmv, hmv']
  apply le_antisymm
  · rcases eq_or_lt_of_le ha with ha0 | hapos
    · have haeq : a = 0 := ha0.symm
      rw [haeq]
      have himg : (fun v ↦ (0 : ℝ) * v) '' S = {0} := by
        ext w
        constructor
        · rintro ⟨v, -, rfl⟩
          simp
        · intro hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          exact ⟨hne.some, hne.some_mem, by simp⟩
      rw [himg]
      simp
    · have hdiv : sInf ((fun v ↦ a * v) '' S) / a ≤ sInf S := by
        apply le_csInf hne
        intro v hv
        have h1 := csInf_le hbdd' ⟨v, hv, rfl⟩
        exact (div_le_iff₀ hapos).mpr (by simpa only [mul_comm] using h1)
      simpa only [mul_comm] using (div_le_iff₀ hapos).mp hdiv
  · apply le_csInf hS'ne
    rintro w ⟨v, hv, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd hv) ha

/-- Adding a constant to every edge shifts the least maximum-cardinality cost by the
maximum cardinality times that constant. -/
theorem maxCardValue_add_const (c : Fin m → Fin n → ℝ) (B : ℝ) :
    maxCardValue (fun i j ↦ c i j + B) = maxCardValue c + (min m n : ℝ) * B := by
  classical
  let S : Set ℝ := {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c}
  let K : ℝ := ∑ p : Fin m × Fin n, |c p.1 p.2|
  have hK : 0 ≤ K := Finset.sum_nonneg fun p _ ↦ abs_nonneg _
  have hne : S.Nonempty := ⟨_, diagonal m n, card_diagonal m n, rfl⟩
  have hbdd : BddBelow S := by
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
  have hset : {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧
      v = σ.cost (fun i j ↦ c i j + B)} =
      (fun v ↦ v + (min m n : ℝ) * B) '' S := by
    ext v
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨σ.cost c, ⟨σ, hσ, rfl⟩, ?_⟩
      rw [cost_add_const, hσ]
      simp only [Nat.cast_min]
    · rintro ⟨w, ⟨σ, hσ, rfl⟩, rfl⟩
      refine ⟨σ, hσ, ?_⟩
      rw [cost_add_const, hσ]
      simp only [Nat.cast_min]
  have hne' : ((fun v ↦ v + (min m n : ℝ) * B) '' S).Nonempty := hne.image _
  have hbdd' : BddBelow ((fun v ↦ v + (min m n : ℝ) * B) '' S) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨b + (min m n : ℝ) * B, by
      rintro w ⟨v, hv, rfl⟩
      linarith [hb hv]⟩
  unfold maxCardValue
  rw [hset]
  have h1 : sInf ((fun v ↦ v + (min m n : ℝ) * B) '' S) ≤ sInf S + (min m n : ℝ) * B := by
    have : sInf ((fun v ↦ v + (min m n : ℝ) * B) '' S) - (min m n : ℝ) * B ≤ sInf S := by
      apply le_csInf hne
      intro v hv
      have := csInf_le hbdd' ⟨v, hv, rfl⟩
      linarith
    linarith
  have h2 : sInf S + (min m n : ℝ) * B ≤ sInf ((fun v ↦ v + (min m n : ℝ) * B) '' S) := by
    apply le_csInf hne'
    rintro w ⟨v, hv, rfl⟩
    have := csInf_le hbdd hv
    linarith
  linarith

end PartialMatching

section HomogeneousKernel

variable {E : Type*} [SMul ℝ E]

/-- A two-homogeneous edge kernel: scaling the displacement by `a > 0` scales the
cost by `a ^ 2`. -/
def HomogeneousTwo (k : E → ℝ) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ z : E, k (a • z) = a ^ 2 * k z

/-- The self-similar edge identity: scaling positions by `c > 0` and the tilt by
`c ^ 2` leaves the tilted edge cost equal to `c ^ 2` times the scaled cost. -/
theorem homogeneousTwo_edge_scaling {k : E → ℝ} (hk : HomogeneousTwo k)
    {c t g : ℝ} (hc : 0 < c) (z : E) :
    k (c • z) + t * g = c ^ 2 * (k z + (t / c ^ 2) * g) := by
  rw [hk c hc z]
  field_simp

/-- Inverse form used in the pressure recursion: shrinking the displacement by
`c` scales the cost by `c⁻²`. -/
theorem homogeneousTwo_inv_edge_scaling {k : E → ℝ} (hk : HomogeneousTwo k)
    {c t g : ℝ} (hc : 0 < c) (z : E) :
    k (c⁻¹ • z) + t * g = c⁻¹ ^ 2 * (k z + (t * c ^ 2) * g) := by
  have hinv : 0 < c⁻¹ := inv_pos.mpr hc
  rw [hk c⁻¹ hinv z]
  field_simp

end HomogeneousKernel

end OTSelector
