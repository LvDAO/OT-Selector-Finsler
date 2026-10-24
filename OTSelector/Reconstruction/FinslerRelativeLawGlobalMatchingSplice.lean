import OTSelector.Finite.MatchingUnion
import OTSelector.Finite.MaxCardValueAssignment

/-! Disjoint original population cells assemble on their unchanged indices.
Only the literal missing cardinality is completed by bounded physical edges. -/

open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Union actual cell matchings whose endpoints carry that same original cell
label. The label may include the one residual flag as an extra cell. -/
def populationCellMatchingUnion {C : Type*} [Fintype C] [DecidableEq C] {m n : ℕ}
    (xs : Fin m → C) (ys : Fin n → C) (σ : C → OTSelector.PartialMatching m n)
    (hσ : ∀ c e, e ∈ (σ c).edges → xs e.1 = c ∧ ys e.2 = c) : OTSelector.PartialMatching m n where
  edges := Finset.univ.biUnion (fun c ↦ (σ c).edges)
  row_inj := by
    intro e he e' he' hrow
    obtain ⟨c, hc, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨d, hd, he'⟩ := Finset.mem_biUnion.mp he'
    have hcd : c = d := (hσ c e he).1.symm.trans ((congrArg xs hrow).trans (hσ d e' he').1)
    subst d
    exact (σ c).row_inj e he e' he' hrow
  col_inj := by
    intro e he e' he' hcol
    obtain ⟨c, hc, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨d, hd, he'⟩ := Finset.mem_biUnion.mp he'
    have hcd : c = d := (hσ c e he).2.symm.trans ((congrArg ys hcol).trans (hσ d e' he').2)
    subst d
    exact (σ c).col_inj e he e' he' hcol

theorem populationCellMatchingUnion_disjoint {C : Type*} [Fintype C] [DecidableEq C] {m n : ℕ}
    (xs : Fin m → C) (ys : Fin n → C) (σ : C → OTSelector.PartialMatching m n)
    (hσ : ∀ c e, e ∈ (σ c).edges → xs e.1 = c ∧ ys e.2 = c) :
    Pairwise (fun c d ↦ Disjoint (σ c).edges (σ d).edges) := by
  intro c d hcd
  apply Finset.disjoint_left.mpr
  intro e he hd
  exact hcd ((hσ c e he).1.symm.trans (hσ d e hd).1)

theorem card_populationCellMatchingUnion {C : Type*} [Fintype C] [DecidableEq C] {m n : ℕ}
    (xs : Fin m → C) (ys : Fin n → C) (σ : C → OTSelector.PartialMatching m n)
    (hσ : ∀ c e, e ∈ (σ c).edges → xs e.1 = c ∧ ys e.2 = c) :
    (populationCellMatchingUnion xs ys σ hσ).card = ∑ c, (σ c).card := by
  unfold OTSelector.PartialMatching.card populationCellMatchingUnion
  rw [Finset.card_biUnion]
  exact fun c hc d hd hcd ↦ populationCellMatchingUnion_disjoint xs ys σ hσ hcd

theorem cost_populationCellMatchingUnion {C : Type*} [Fintype C] [DecidableEq C] {m n : ℕ}
    (xs : Fin m → C) (ys : Fin n → C) (σ : C → OTSelector.PartialMatching m n)
    (hσ : ∀ c e, e ∈ (σ c).edges → xs e.1 = c ∧ ys e.2 = c)
    (cost : Fin m → Fin n → ℝ) :
    (populationCellMatchingUnion xs ys σ hσ).cost cost = ∑ c, (σ c).cost cost := by
  unfold OTSelector.PartialMatching.cost populationCellMatchingUnion
  rw [Finset.sum_biUnion]
  exact fun c hc d hd hcd ↦ populationCellMatchingUnion_disjoint xs ys σ hσ hcd

/-- Actual retained and residual pieces yield a full assignment. Completion
cost is charged only to their true missing cardinality. -/
theorem exists_full_assignment_of_population_cells
    {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (xs ys : Fin n → C) (σ : C → OTSelector.PartialMatching n n)
    (hσ : ∀ c e, e ∈ (σ c).edges → xs e.1 = c ∧ ys e.2 = c)
    (cost : Fin n → Fin n → ℝ) (B : ℝ) (hB : ∀ i j, cost i j ≤ B) :
    ∃ τ : Assignment n, assignmentCost cost τ ≤
      (∑ c, (σ c).cost cost) + ((n - ∑ c, (σ c).card : ℕ) : ℝ) * B := by
  let U := populationCellMatchingUnion xs ys σ hσ
  obtain ⟨ρ, hcard, hcost⟩ := U.exists_maxCardinality_cost_le cost hB
  obtain ⟨τ, hτ⟩ := ρ.exists_assignment_cost_eq cost hcard
  refine ⟨τ, hτ.trans_le ?_⟩
  simpa only [min_self, U, cost_populationCellMatchingUnion, card_populationCellMatchingUnion] using hcost

end OTSelector.Reconstruction
