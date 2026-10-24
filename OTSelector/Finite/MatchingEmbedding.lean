import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import OTSelector.Finite.PartialMatching


/-!
## Lemma skeleton

* **Conditions:** Finite row and column index types may have different sizes, including zero. e : Fin a embeds injectively into Fin m and f : Fin b embeds injectively into Fin n. For the inverse and exact restriction identities, every ambient edge must have its endpoints in range e and range f. Costs are arbitrary real functions, with no sign assumption.
* **Objects:** mapEmbedding: image of every edge under the pair of index embeddings; comapEmbedding: the edges in the small rectangle whose embedded pair belongs to the ambient matching; support condition: each actual ambient edge lies in both embedded endpoint ranges
* **Proof detail:** Injectivity of the two endpoint maps preserves row and column injectivity and makes the edge map injective. Apply finite-set image cardinality and finite-sum reindexing. For restriction, choose preimages only for endpoints known to lie in the embedding ranges; compare edge membership in both directions. Deduce the inverse cardinality and cost identities from the exact edge equality.

## Mathematical sources

* Reinhard Diestel, *Graph Theory, 4th electronic edition (2010), corrected reprint 2012*, Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
  https://diestel-graph-theory.com/Sample.pdf#page=2
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** Embedding/comap, range certificates and dependent finite-index costs are finite-reindexing adapters. Restriction preserves cardinality only with the stated endpoint-range condition.
-/

/-! Exact embedding and restriction of finite matchings, including empty clouds. -/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {a b m n : ℕ}

/-- Embed both original finite index sets without adding any matching edges. -/
def mapEmbedding (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (σ : PartialMatching a b) : PartialMatching m n where
  edges := σ.edges.image fun p ↦ (e p.1, f p.2)
  row_inj := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg (fun p ↦ (e p.1, f p.2))
      (σ.row_inj u hu v hv (e.injective hxy))
  col_inj := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg (fun p ↦ (e p.1, f p.2))
      (σ.col_inj u hu v hv (f.injective hxy))

theorem card_mapEmbedding (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (σ : PartialMatching a b) : (mapEmbedding e f σ).card = σ.card := by
  classical
  exact Finset.card_image_of_injective _ (fun _ _ h ↦
    Prod.ext (e.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h)))

theorem cost_mapEmbedding (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (σ : PartialMatching a b) (c : Fin m → Fin n → ℝ) :
    (mapEmbedding e f σ).cost c = σ.cost (fun i j ↦ c (e i) (f j)) := by
  classical
  exact Finset.sum_image (fun _ _ _ _ h ↦
    Prod.ext (e.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h)))

/-- Pull back exactly the ambient edges whose endpoints lie in the two
embedded index sets. No choice of an inverse at an unused index is needed. -/
def comapEmbedding (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (σ : PartialMatching m n) : PartialMatching a b where
  edges := Finset.univ.filter fun p ↦ (e p.1, f p.2) ∈ σ.edges
  row_inj := by
    intro u hu v hv hrow
    have he := σ.row_inj _ (Finset.mem_filter.mp hu).2 _
      (Finset.mem_filter.mp hv).2 (congrArg e hrow)
    exact Prod.ext hrow (f.injective (congrArg Prod.snd he))
  col_inj := by
    intro u hu v hv hcol
    have he := σ.col_inj _ (Finset.mem_filter.mp hu).2 _
      (Finset.mem_filter.mp hv).2 (congrArg f hcol)
    exact Prod.ext (e.injective (congrArg Prod.fst he)) hcol

/-- Restriction followed by embedding recovers every edge of a matching
carried by the actual embedded row and column sets. -/
theorem map_comapEmbedding_edges (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (σ : PartialMatching m n)
    (hσ : ∀ p ∈ σ.edges, p.1 ∈ range e ∧ p.2 ∈ range f) :
    (mapEmbedding e f (comapEmbedding e f σ)).edges = σ.edges := by
  classical
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hu).2
  · intro p hp
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hσ p hp
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa only [hi, hj, Prod.mk.eta] using hp
    · exact Prod.ext hi hj

theorem card_comapEmbedding (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (σ : PartialMatching m n)
    (hσ : ∀ p ∈ σ.edges, p.1 ∈ range e ∧ p.2 ∈ range f) :
    (comapEmbedding e f σ).card = σ.card := by
  rw [← card_mapEmbedding e f, card, map_comapEmbedding_edges e f σ hσ]
  rfl

theorem cost_comapEmbedding (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (σ : PartialMatching m n)
    (hσ : ∀ p ∈ σ.edges, p.1 ∈ range e ∧ p.2 ∈ range f)
    (c : Fin m → Fin n → ℝ) :
    (comapEmbedding e f σ).cost (fun i j ↦ c (e i) (f j)) = σ.cost c := by
  rw [← cost_mapEmbedding e f, cost, map_comapEmbedding_edges e f σ hσ]
  rfl

end OTSelector.PartialMatching
