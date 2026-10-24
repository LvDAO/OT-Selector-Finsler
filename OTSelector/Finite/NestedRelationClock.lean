import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite.NestedRelationClock

## Lemma skeleton

* **Conditions:** Finite source and target types; row neighborhoods are linearly ordered by inclusion.

* **Objects:** Strict real source/target clocks encoding the exact adjacency relation, with a uniform half-integer gap.

* **Proof detail:** Use minus the row cardinality as the source clock and a half-integer built from the smallest incident row size as each target threshold. Nestedness converts cardinality comparison to membership; integer parity gives the gap. Empty rows and columns use the explicit fallback.

## Mathematical sources

- [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2): Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): An explicit local representation of nested bipartite neighborhoods, derived from finite inclusion/cardinality facts; the sources supply graph and finite-order foundations, not this formula.
-/

/-!
# Exact strict-clock coding of finite nested row neighborhoods

The coding preserves the original finite indices and adjacency. Source clocks
are negative row sizes; each target clock is a half-integer threshold. Empty
rows and columns are included, and every source/target pair has gap at least 1/2.
-/
noncomputable section
namespace OTSelector.FiniteRelation
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

/-- Sizes of the original rows incident to the given target. -/
def incidentRowSizes (row : I → Finset J) (j : J) : Finset ℕ :=
  (Finset.univ.filter fun i ↦ j ∈ row i).image fun i ↦ (row i).card

/-- The minimum incident row size; an unincident column lies past all row sizes. -/
def rowClockThreshold (row : I → Finset J) (j : J) : ℕ :=
  if h : (incidentRowSizes row j).Nonempty then (incidentRowSizes row j).min' h
  else Fintype.card J + 1

/-- Integer-valued source clocks keep each original row index. -/
def rowSourceClock (row : I → Finset J) (i : I) : ℝ := -((row i).card : ℝ)

/-- Half-integer target clocks keep each original target index. -/
def rowTargetClock (row : I → Finset J) (j : J) : ℝ :=
  -(rowClockThreshold row j : ℝ) + 1 / 2

omit [Fintype J] in
theorem card_mem_incidentRowSizes {row : I → Finset J} {i : I} {j : J}
    (hij : j ∈ row i) : (row i).card ∈ incidentRowSizes row j := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩

theorem rowClockThreshold_le_of_mem {row : I → Finset J} {i : I} {j : J}
    (hij : j ∈ row i) : rowClockThreshold row j ≤ (row i).card := by
  have hm := card_mem_incidentRowSizes hij
  have hne : (incidentRowSizes row j).Nonempty := ⟨_, hm⟩
  simp only [rowClockThreshold, hne, ↓reduceDIte]
  exact Finset.min'_le _ _ hm

theorem exists_incident_row_of_nonempty {row : I → Finset J} {j : J}
    (hne : (incidentRowSizes row j).Nonempty) :
    ∃ i : I, j ∈ row i ∧ (row i).card = rowClockThreshold row j := by
  have hm := Finset.min'_mem (incidentRowSizes row j) hne
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
  refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
  simpa only [rowClockThreshold, hne, ↓reduceDIte] using heq

/-- Nested row neighborhoods are exactly the upper levels of their cardinality
thresholds; no enumeration, positivity, or nonempty-row assumption is used. -/
theorem mem_row_iff_threshold_le (row : I → Finset J)
    (hnested : ∀ i i', row i ⊆ row i' ∨ row i' ⊆ row i) (i : I) (j : J) :
    j ∈ row i ↔ rowClockThreshold row j ≤ (row i).card := by
  constructor
  · exact rowClockThreshold_le_of_mem
  · intro h
    by_cases hne : (incidentRowSizes row j).Nonempty
    · obtain ⟨i₀, hj₀, hcard⟩ := exists_incident_row_of_nonempty hne
      rcases hnested i₀ i with hsub | hsub
      · exact hsub hj₀
      · have hle : (row i₀).card ≤ (row i).card := by simpa only [hcard] using h
        have heq : row i = row i₀ := Finset.eq_of_subset_of_card_le hsub hle
        exact heq.symm ▸ hj₀
    · have hcard : (row i).card ≤ Fintype.card J := Finset.card_le_univ _
      simp only [rowClockThreshold, hne, ↓reduceDIte] at h
      omega

/-- The original finite adjacency is exactly a strict scalar-clock inequality. -/
theorem mem_row_iff_clock_lt (row : I → Finset J)
    (hnested : ∀ i i', row i ⊆ row i' ∨ row i' ⊆ row i) (i : I) (j : J) :
    j ∈ row i ↔ rowSourceClock row i < rowTargetClock row j := by
  rw [mem_row_iff_threshold_le row hnested]
  constructor
  · intro h
    have hreal : (rowClockThreshold row j : ℝ) ≤ (row i).card := Nat.cast_le.mpr h
    dsimp [rowSourceClock, rowTargetClock]
    linarith
  · intro h
    dsimp [rowSourceClock, rowTargetClock] at h
    by_contra hnot
    have hstep : (row i).card + 1 ≤ rowClockThreshold row j := by omega
    have hreal : ((row i).card : ℝ) + 1 ≤ rowClockThreshold row j := by exact_mod_cast hstep
    linarith

/-- Every pair has a uniform absolute half-unit clock gap, including forbidden
pairs and columns incident to no source. -/
theorem row_clock_half_gap (row : I → Finset J) (i : I) (j : J) :
    (1 / 2 : ℝ) ≤ |rowTargetClock row j - rowSourceClock row i| := by
  by_cases h : rowClockThreshold row j ≤ (row i).card
  · have hreal : (rowClockThreshold row j : ℝ) ≤ (row i).card := Nat.cast_le.mpr h
    calc
      (1 / 2 : ℝ) ≤ rowTargetClock row j - rowSourceClock row i := by
        dsimp [rowSourceClock, rowTargetClock]
        linarith
      _ ≤ _ := le_abs_self _
  · have hstep : (row i).card + 1 ≤ rowClockThreshold row j := by omega
    have hreal : ((row i).card : ℝ) + 1 ≤ rowClockThreshold row j := by exact_mod_cast hstep
    calc
      (1 / 2 : ℝ) ≤ -(rowTargetClock row j - rowSourceClock row i) := by
        dsimp [rowSourceClock, rowTargetClock]
        linarith
      _ ≤ |-(rowTargetClock row j - rowSourceClock row i)| := le_abs_self _
      _ = _ := abs_neg _

/-- Exact clock representation on the unchanged original indices. -/
theorem exists_strict_clocks_of_nested_rows (row : I → Finset J)
    (hnested : ∀ i i', row i ⊆ row i' ∨ row i' ⊆ row i) :
    ∃ (s : I → ℝ) (t : J → ℝ),
      (∀ i j, j ∈ row i ↔ s i < t j) ∧
      (∀ i j, (1 / 2 : ℝ) ≤ |t j - s i|) :=
  ⟨rowSourceClock row, rowTargetClock row,
    mem_row_iff_clock_lt row hnested, row_clock_half_gap row⟩


/-- The clock coding stays in one explicit compact interval. -/
theorem rowClockThreshold_le_card_add_one (row : I → Finset J) (j : J) :
    rowClockThreshold row j ≤ Fintype.card J + 1 := by
  by_cases hne : (incidentRowSizes row j).Nonempty
  · obtain ⟨i, _, hcard⟩ := exists_incident_row_of_nonempty hne
    rw [← hcard]
    exact (Finset.card_le_univ _).trans (Nat.le_succ _)
  · simp only [rowClockThreshold, hne, ↓reduceDIte, le_refl]

omit [Fintype I] [DecidableEq J] in
theorem rowSourceClock_bounds (row : I → Finset J) (i : I) :
    -(Fintype.card J : ℝ) ≤ rowSourceClock row i ∧ rowSourceClock row i ≤ 0 := by
  have hcard : ((row i).card : ℝ) ≤ Fintype.card J := Nat.cast_le.mpr (Finset.card_le_univ _)
  have hzero : (0 : ℝ) ≤ (row i).card := Nat.cast_nonneg _
  dsimp [rowSourceClock]
  constructor <;> linarith

theorem rowTargetClock_bounds (row : I → Finset J) (j : J) :
    -((Fintype.card J : ℝ) + 1) ≤ rowTargetClock row j ∧ rowTargetClock row j ≤ 1 := by
  have hcard : (rowClockThreshold row j : ℝ) ≤ (Fintype.card J : ℝ) + 1 := by
    exact_mod_cast rowClockThreshold_le_card_add_one row j
  have hzero : (0 : ℝ) ≤ rowClockThreshold row j := Nat.cast_nonneg _
  dsimp [rowTargetClock]
  constructor <;> linarith

/-- Predicate form of the exact coding, including finite empty source/target
types. The hypothesis refers only to the original finite allowed relation. -/
theorem exists_strict_clocks_of_nested_relation (allowed : I → J → Prop)
    (hnested : ∀ i i', (∀ j, allowed i j → allowed i' j) ∨
      (∀ j, allowed i' j → allowed i j)) :
    ∃ (s : I → ℝ) (t : J → ℝ),
      (∀ i j, allowed i j ↔ s i < t j) ∧
      (∀ i j, (1 / 2 : ℝ) ≤ |t j - s i|) ∧
      (∀ i, -((Fintype.card J : ℝ) + 1) ≤ s i ∧ s i ≤ 1) ∧
      (∀ j, -((Fintype.card J : ℝ) + 1) ≤ t j ∧ t j ≤ 1) := by
  classical
  let row : I → Finset J := fun i ↦ Finset.univ.filter (allowed i)
  have hmem (i : I) (j : J) : j ∈ row i ↔ allowed i j := by simp only [row, Finset.mem_filter, Finset.mem_univ, true_and]
  have hrows : ∀ i i', row i ⊆ row i' ∨ row i' ⊆ row i := by
    intro i i'
    rcases hnested i i' with h | h
    · exact Or.inl (fun j hj ↦ (hmem i' j).mpr (h j ((hmem i j).mp hj)))
    · exact Or.inr (fun j hj ↦ (hmem i j).mpr (h j ((hmem i' j).mp hj)))
  refine ⟨rowSourceClock row, rowTargetClock row, ?_, row_clock_half_gap row, ?_,
    rowTargetClock_bounds row⟩
  · intro i j
    exact (hmem i j).symm.trans (mem_row_iff_clock_lt row hrows i j)
  · intro i
    have h := rowSourceClock_bounds row i
    constructor <;> linarith

end OTSelector.FiniteRelation
