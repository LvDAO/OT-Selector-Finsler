import OTSelector.Finite.MaxCardValueMeasurable
import OTSelector.Finite.MaxCardValueRegularity
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalFinite.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalFinite`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.MarkedStationaryValueLegalFinite

**Conditions:** An arbitrary finite bipartite legal edge set and signed real costs, with no complete-graph feasibility assumption.

**Objects:** Maximum feasible legal cardinality and the minimum cost among its legal maximizing matchings.

**Proof detail:** The empty matching ensures nonemptiness; finite extrema give cardinality and cost attainment, finite iInf gives measurability, and summing bounded costs yields the stated absolute value bounds.

**Sources:** [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Maximum-cardinality values on a finite legal graph

A finite interleaved marked cloud need not admit a matching of the smaller color
count.  The admissible graph is therefore part of the minimization problem.
`legalMaximumCard` is the largest cardinality of a matching whose edges belong to
that graph; `legalMaximumValue` minimizes the signed cost at that cardinality.
No unmatched penalty or complete-bipartite completion is used.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction
namespace PartialMatching

variable {m n : ℕ}

/-- A partial matching with no edges, available for every legal graph. -/
def empty : OTSelector.PartialMatching m n where
  edges := ∅
  row_inj := by simp
  col_inj := by simp

/-- All retained edges belong to the specified finite legal graph. -/
def IsLegal (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n) : Prop :=
  σ.edges ⊆ allowed

/-- The actual maximum cardinality allowed by the finite legal graph. -/
def legalMaximumCard (allowed : Finset (Fin m × Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (IsLegal allowed)).sup OTSelector.PartialMatching.card

/-- Every legal matching has cardinality at most the legal maximum. -/
theorem card_le_legalMaximumCard {allowed : Finset (Fin m × Fin n)}
    {σ : OTSelector.PartialMatching m n} (hσ : IsLegal allowed σ) :
    σ.card ≤ legalMaximumCard allowed := by
  classical
  exact Finset.le_sup (by simp [hσ])

/-- A legal maximum-cardinality matching always exists, including when the graph is empty. -/
theorem exists_legalMaximumCard (allowed : Finset (Fin m × Fin n)) :
    ∃ σ : OTSelector.PartialMatching m n,
      IsLegal allowed σ ∧ σ.card = legalMaximumCard allowed := by
  classical
  have hne : (Finset.univ.filter (IsLegal allowed)).Nonempty := by
    refine ⟨empty, ?_⟩
    simp [IsLegal, empty]
  obtain ⟨σ, hσ, hcard⟩ := Finset.exists_mem_eq_sup _ hne
    OTSelector.PartialMatching.card
  exact ⟨σ, (Finset.mem_filter.mp hσ).2, hcard.symm⟩

/-- The legal maximum may be smaller than the smaller color count. -/
theorem legalMaximumCard_le_min (allowed : Finset (Fin m × Fin n)) :
    legalMaximumCard allowed ≤ min m n := by
  obtain ⟨σ, -, hσ⟩ := exists_legalMaximumCard allowed
  exact hσ ▸ σ.card_le

/-- The finite type of legal maximum-cardinality matchings. -/
def LegalMaximumMatching (allowed : Finset (Fin m × Fin n)) :=
  {σ : OTSelector.PartialMatching m n //
    IsLegal allowed σ ∧ σ.card = legalMaximumCard allowed}

instance (allowed : Finset (Fin m × Fin n)) : Fintype (LegalMaximumMatching allowed) := by
  classical
  unfold LegalMaximumMatching
  infer_instance

instance (allowed : Finset (Fin m × Fin n)) : Nonempty (LegalMaximumMatching allowed) := by
  obtain ⟨σ, hσ, hcard⟩ := exists_legalMaximumCard allowed
  exact ⟨⟨σ, hσ, hcard⟩⟩

/-- The signed minimum over the actual legal maximum-cardinality class. -/
def legalMaximumValue (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) : ℝ :=
  sInf (Set.range (fun σ : LegalMaximumMatching allowed ↦ σ.val.cost c))

/-- The legal cost set is bounded below by finiteness, with no sign condition on costs. -/
theorem bddBelow_legalMaximumValue (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) :
    BddBelow (Set.range (fun σ : LegalMaximumMatching allowed ↦ σ.val.cost c)) :=
  (Set.finite_range _).bddBelow

/-- Every legal maximum-cardinality comparator bounds the signed optimum. -/
theorem legalMaximumValue_le {allowed : Finset (Fin m × Fin n)}
    (c : Fin m → Fin n → ℝ) {σ : OTSelector.PartialMatching m n}
    (hlegal : IsLegal allowed σ) (hcard : σ.card = legalMaximumCard allowed) :
    legalMaximumValue allowed c ≤ σ.cost c :=
  csInf_le (bddBelow_legalMaximumValue allowed c) ⟨⟨σ, hlegal, hcard⟩, rfl⟩

/-- The signed legal maximum-cardinality minimum is attained. -/
theorem exists_cost_eq_legalMaximumValue (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) :
    ∃ σ : OTSelector.PartialMatching m n,
      IsLegal allowed σ ∧ σ.card = legalMaximumCard allowed ∧
        σ.cost c = legalMaximumValue allowed c := by
  classical
  let costs := (Finset.univ : Finset (LegalMaximumMatching allowed)).image
    (fun σ ↦ σ.val.cost c)
  have hne : costs.Nonempty := Finset.univ_nonempty.image _
  obtain ⟨σ, -, hcost⟩ := Finset.mem_image.mp (Finset.min'_mem costs hne)
  refine ⟨σ.val, σ.property.1, σ.property.2, ?_⟩
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro v ⟨τ, rfl⟩
    rw [hcost]
    exact Finset.min'_le costs _ (Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, rfl⟩)
  · exact legalMaximumValue_le _ σ.property.1 σ.property.2

/-- The legal value is a finite infimum, suitable for measurable parameters. -/
theorem legalMaximumValue_eq_iInf (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) :
    legalMaximumValue allowed c = ⨅ σ : LegalMaximumMatching allowed, σ.val.cost c := rfl

/-- For a fixed legal graph, measurable edge costs give a measurable minimum. -/
theorem measurable_legalMaximumValue_fixed {Ω : Type*} [MeasurableSpace Ω]
    (allowed : Finset (Fin m × Fin n)) (c : Ω → Fin m → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ω ↦ c ω i j)) :
    Measurable (fun ω ↦ legalMaximumValue allowed (c ω)) := by
  classical
  simp only [legalMaximumValue_eq_iInf]
  apply Measurable.iInf
  intro σ
  exact Finset.measurable_sum _ (fun e _ ↦ hc e.1 e.2)

/-- Measurability also permits a random legal graph with measurable finite graph events. -/
theorem measurable_legalMaximumValue {Ω : Type*} [MeasurableSpace Ω]
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ E, MeasurableSet {ω | allowed ω = E})
    (c : Ω → Fin m → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ω ↦ c ω i j)) :
    Measurable (fun ω ↦ legalMaximumValue (allowed ω) (c ω)) := by
  classical
  have hrepr : (fun ω ↦ legalMaximumValue (allowed ω) (c ω)) = fun ω ↦
      ∑ E : Finset (Fin m × Fin n),
        if allowed ω = E then legalMaximumValue E (c ω) else 0 := by
    funext ω
    simp
  rw [hrepr]
  exact Finset.measurable_sum _ (fun E _ ↦
    (measurable_legalMaximumValue_fixed E c hc).ite (hallowed E) measurable_const)

/-- Uniform absolute edge bounds control the legal minimum at its actual cardinality. -/
theorem abs_legalMaximumValue_le (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB : ∀ i j, |c i j| ≤ B) :
    |legalMaximumValue allowed c| ≤ (legalMaximumCard allowed : ℝ) * B := by
  obtain ⟨σ, -, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed c
  rw [← hcost, ← hcard]
  exact OTSelector.PartialMatching.abs_cost_le_card_mul hB σ

/-- A bound by the smaller color count remains valid without Hall feasibility. -/
theorem abs_legalMaximumValue_le_min (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    |legalMaximumValue allowed c| ≤ ((min m n : ℕ) : ℝ) * B := by
  refine (abs_legalMaximumValue_le allowed c hB).trans ?_
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (legalMaximumCard_le_min allowed)) hB0

/-- The complete legal graph has precisely the usual maximum cardinality. -/
@[simp]
theorem legalMaximumCard_univ :
    legalMaximumCard (Finset.univ : Finset (Fin m × Fin n)) = min m n := by
  apply le_antisymm (legalMaximumCard_le_min _)
  simpa [OTSelector.PartialMatching.card_diagonal] using
    (card_le_legalMaximumCard (σ := OTSelector.PartialMatching.diagonal m n)
      (allowed := Finset.univ) (by exact Finset.subset_univ _))

/-- The complete graph recovers the existing signed maximum-cardinality pressure. -/
@[simp]
theorem legalMaximumValue_univ (c : Fin m → Fin n → ℝ) :
    legalMaximumValue Finset.univ c = OTSelector.PartialMatching.maxCardValue c := by
  obtain ⟨σ, hlegal, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue Finset.univ c
  obtain ⟨τ, hτcard, hτcost⟩ := OTSelector.PartialMatching.exists_cost_eq_maxCardValue c
  apply le_antisymm
  · rw [← hτcost]
    exact legalMaximumValue_le _ (Finset.subset_univ _) (by simpa using hτcard)
  · rw [← hcost]
    exact OTSelector.PartialMatching.maxCardValue_le_of_card _ (by simpa using hcard)

/-- An empty legal graph has no edges, independently of the color counts. -/
@[simp]
theorem legalMaximumCard_empty :
    legalMaximumCard (∅ : Finset (Fin m × Fin n)) = 0 := by
  obtain ⟨σ, hlegal, hcard⟩ := exists_legalMaximumCard (∅ : Finset (Fin m × Fin n))
  have hempty : σ.edges = ∅ := Finset.subset_empty.mp hlegal
  rw [← hcard, OTSelector.PartialMatching.card, hempty, Finset.card_empty]

end PartialMatching
end OTSelector.Reconstruction

end
end
