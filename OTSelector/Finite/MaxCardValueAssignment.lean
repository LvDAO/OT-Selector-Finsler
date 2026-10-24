import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import OTSelector.Finite.Assignment
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching
import OTSelector.Finite.PerturbedValue

/-!
# Finite.MaxCardValueAssignment

**Conditions:** Finite square costs and full-cardinality partial matchings.

**Objects:** Equivalence of permutation assignment and maximum-cardinality partial-matching objective values.

**Proof detail:** Map a permutation to its graph; conversely row and column injectivity with n edges makes the endpoint correspondence bijective, and finite-sum transport preserves the objective and hence its least value.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# The maximum-cardinality value equals the assignment value

On an `n × n` matrix the maximum-cardinality partial matchings are exactly the
graphs of permutations.  Hence the least cost over maximum-cardinality matchings,
`maxCardValue`, coincides with the least cost over permutations used by
`perturbedAssignmentValue`.

This identifies the physical Dirichlet semidiscrete assignment problem with the
marked-cube pressure value `markedFixedValue`, whose local models are analysed by
the Poisson/tile machinery.
-/

open scoped BigOperators

noncomputable section
namespace OTSelector
namespace PartialMatching

variable {n : ℕ}

/-- A permutation as a maximum-cardinality partial matching. -/
def ofAssignment (σ : Assignment n) : PartialMatching n n where
  edges := Finset.univ.image (fun i : Fin n => (i, σ i))
  row_inj := by
    intro e he e' he' hrow
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp he'
    simp only [Prod.mk.injEq] at hrow
    subst hrow
    rfl
  col_inj := by
    intro e he e' he' hcol
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp he'
    simp only [Prod.mk.injEq] at hcol
    rw [σ.injective hcol]

@[simp]
theorem edges_ofAssignment (σ : Assignment n) :
    (ofAssignment σ).edges = Finset.univ.image (fun i : Fin n => (i, σ i)) := rfl

/-- The matching of a permutation has maximum cardinality. -/
theorem card_ofAssignment (σ : Assignment n) : (ofAssignment σ).card = n := by
  rw [card, edges_ofAssignment,
    Finset.card_image_of_injective _ (fun i j h => σ.injective (Prod.mk.inj h).2),
    Finset.card_univ, Fintype.card_fin]

/-- The matching cost of a permutation agrees with its assignment cost. -/
theorem cost_ofAssignment (c : Fin n → Fin n → ℝ) (σ : Assignment n) :
    (ofAssignment σ).cost c = assignmentCost c σ := by
  unfold cost assignmentCost
  rw [edges_ofAssignment, Finset.sum_image]
  · intro i _ j _ h
    exact σ.injective (Prod.mk.inj h).2

/-- Every maximum-cardinality matching on `Fin n × Fin n` is the graph of a
permutation with the same total cost. -/
theorem exists_assignment_cost_eq (c : Fin n → Fin n → ℝ) {σ : PartialMatching n n}
    (hσ : σ.card = min n n) :
    ∃ τ : Assignment n, assignmentCost c τ = σ.cost c := by
  classical
  have hcard : σ.card = n := by simpa using hσ
  have hrows : σ.rows = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [card_rows, hcard, Fintype.card_fin]
  have hex : ∀ i : Fin n, ∃ j : Fin n, (i, j) ∈ σ.edges := by
    intro i
    have hi : i ∈ σ.rows := by rw [hrows]; exact Finset.mem_univ i
    rw [rows, Finset.mem_image] at hi
    obtain ⟨p, hp, hp1⟩ := hi
    rcases p with ⟨a, b⟩
    simp only [Prod.fst] at hp1
    exact ⟨b, hp1 ▸ hp⟩
  let τf : Fin n → Fin n := fun i => Classical.choose (hex i)
  have hτf : ∀ i, (i, τf i) ∈ σ.edges := fun i => Classical.choose_spec (hex i)
  have hτinj : Function.Injective τf := by
    intro i j h
    have hcol : (i, τf i).2 = (j, τf j).2 := by rw [h]
    have he := σ.col_inj _ (hτf i) _ (hτf j) hcol
    exact (Prod.mk.inj he).1
  let τ : Assignment n := Equiv.ofBijective τf (Finite.injective_iff_bijective.mp hτinj)
  have himage_subset :
      Finset.univ.image (fun i : Fin n => (i, τf i)) ⊆ σ.edges := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hτf i
  have himage_card :
      (Finset.univ.image (fun i : Fin n => (i, τf i))).card = σ.edges.card := by
    rw [Finset.card_image_of_injective (f := fun i : Fin n => (i, τf i)) _
      (fun i j h => hτinj (Prod.mk.inj h).2),
      Finset.card_univ, Fintype.card_fin]
    have hc2 : σ.edges.card = n := hcard
    omega
  have himage_eq : Finset.univ.image (fun i : Fin n => (i, τf i)) = σ.edges :=
    Finset.eq_of_subset_of_card_le himage_subset (le_of_eq himage_card.symm)
  refine ⟨τ, ?_⟩
  calc assignmentCost c τ = ∑ i, c i (τf i) := rfl
    _ = ∑ p ∈ Finset.univ.image (fun i : Fin n => (i, τf i)), c p.1 p.2 := by
        rw [Finset.sum_image]
        · intro i _ j _ h
          exact hτinj (Prod.mk.inj h).2
    _ = σ.cost c := by
        unfold cost
        rw [← himage_eq]

/-- **Maximum-cardinality value = assignment value.**  The least cost over
maximum-cardinality matchings of an `n × n` tilted matrix is the least cost over
permutations. -/
theorem maxCardValue_eq_perturbedAssignmentValue (c g : Fin n → Fin n → ℝ) (t : ℝ) :
    maxCardValue (perturbedEdgeCost c g t) = perturbedAssignmentValue c g t := by
  apply le_antisymm
  · calc maxCardValue (perturbedEdgeCost c g t)
        ≤ (ofAssignment (optimalAssignment (perturbedEdgeCost c g t))).cost
            (perturbedEdgeCost c g t) :=
          maxCardValue_le_of_card _ (by rw [card_ofAssignment]; exact (min_self n).symm)
      _ = assignmentCost (perturbedEdgeCost c g t)
            (optimalAssignment (perturbedEdgeCost c g t)) := cost_ofAssignment _ _
      _ = perturbedAssignmentValue c g t := rfl
  · obtain ⟨σ, hσ, hσc⟩ := exists_cost_eq_maxCardValue (perturbedEdgeCost c g t)
    obtain ⟨τ, hτ⟩ := exists_assignment_cost_eq (perturbedEdgeCost c g t) hσ
    unfold perturbedAssignmentValue
    rw [← hσc]
    exact (optimalAssignment_isOptimal (perturbedEdgeCost c g t) τ).trans_eq hτ

end PartialMatching
end OTSelector
