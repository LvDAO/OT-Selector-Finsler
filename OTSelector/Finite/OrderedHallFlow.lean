import Mathlib.Probability.Kernel.Basic
import Mathlib.Tactic

/-!
# Finite.OrderedHallFlow

## Lemma skeleton

* **Conditions:** Finite nonnegative ordered masses with equal total mass; for legality, the allowed relation is monotone in the stated row/column directions and satisfies the supplied weighted Hall cuts.

* **Objects:** An explicit measurable matrix of cumulative-interval overlap masses.

* **Proof detail:** Form cumulative sums, define each entry by overlap length of the two mass intervals, telescope to obtain both marginals, and use the Hall cut at a forbidden ordered pair to show the intervals do not overlap.

## Mathematical sources

- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=39): Section 2.6, Remarks 2.27–2.28, pp. 35–37, equations (2.31)–(2.37).
- [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2): Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Finite interval-overlap form of monotone rearrangement plus a locally proved ordered-Hall legality argument. No abstract measurable selection is invoked.
-/

/-!
Explicit measurable finite clock-bin coupling by overlaps of cumulative mass
intervals. This produces actual residual coupling weights without an abstract
measurable-selection premise.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Cumulative mass of the first `k` clock classes, with a zero extension. -/
def finiteClockPrefix {M : ℕ} (a : Fin M → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, if hi : i < M then a ⟨i, hi⟩ else 0

theorem finiteClockPrefix_zero {M : ℕ} (a : Fin M → ℝ) : finiteClockPrefix a 0 = 0 := by
  simp [finiteClockPrefix]

theorem finiteClockPrefix_total {M : ℕ} (a : Fin M → ℝ) :
    finiteClockPrefix a M = ∑ i, a i := by
  symm
  exact Finset.sum_fin_eq_sum_range a

theorem finiteClockPrefix_nonneg {M : ℕ} (a : Fin M → ℝ) (ha : ∀ i, 0 ≤ a i) (k : ℕ) :
    0 ≤ finiteClockPrefix a k :=
  Finset.sum_nonneg fun i _ ↦ by split_ifs with hi; exact ha _; exact le_refl 0

theorem finiteClockPrefix_mono {M : ℕ} (a : Fin M → ℝ) (ha : ∀ i, 0 ≤ a i)
    {k l : ℕ} (hkl : k ≤ l) : finiteClockPrefix a k ≤ finiteClockPrefix a l := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
  intro i hi hni
  split_ifs with h
  · exact ha _
  · exact le_refl 0

theorem finiteClockPrefix_succ_sub {M : ℕ} (a : Fin M → ℝ) (i : Fin M) :
    finiteClockPrefix a (i.val + 1) - finiteClockPrefix a i.val = a i := by
  unfold finiteClockPrefix
  rw [Finset.sum_range_succ, dite_eq_left i.isLt]
  ring

/-- The overlap of the source and target cumulative-mass intervals. -/
def orderedClockFlow {M L : ℕ} (a : Fin M → ℝ) (b : Fin L → ℝ)
    (i : Fin M) (j : Fin L) : ℝ :=
  min (finiteClockPrefix a (i.val + 1)) (finiteClockPrefix b (j.val + 1)) -
    min (finiteClockPrefix a i.val) (finiteClockPrefix b (j.val + 1)) -
    min (finiteClockPrefix a (i.val + 1)) (finiteClockPrefix b j.val) +
    min (finiteClockPrefix a i.val) (finiteClockPrefix b j.val)

theorem orderedClockFlow_nonneg {M L : ℕ} (a : Fin M → ℝ) (b : Fin L → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (i : Fin M) (j : Fin L) :
    0 ≤ orderedClockFlow a b i j := by
  have hs := finiteClockPrefix_mono a ha (Nat.le_succ i.val)
  have ht := finiteClockPrefix_mono b hb (Nat.le_succ j.val)
  unfold orderedClockFlow
  simp only [min_def]
  split_ifs <;> linarith

/-- Row sums are the unchanged source masses. -/
theorem orderedClockFlow_row_sum {M L : ℕ} (a : Fin M → ℝ) (b : Fin L → ℝ)
    (ha : ∀ i, 0 ≤ a i) (_hb : ∀ j, 0 ≤ b j) (htotal : ∑ i, a i = ∑ j, b j)
    (i : Fin M) : (∑ j, orderedClockFlow a b i j) = a i := by
  let f : ℕ → ℝ := fun k ↦
    min (finiteClockPrefix a (i.val + 1)) (finiteClockPrefix b k) -
    min (finiteClockPrefix a i.val) (finiteClockPrefix b k)
  have hterm (j : Fin L) : orderedClockFlow a b i j = f (j.val + 1) - f j.val := by
    unfold orderedClockFlow f
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ f (k + 1) - f k) L, Finset.sum_range_sub]
  have hs : finiteClockPrefix a (i.val + 1) ≤ ∑ j, b j := by
    rw [← htotal, ← finiteClockPrefix_total]
    exact finiteClockPrefix_mono a ha i.isLt
  have hs' : finiteClockPrefix a i.val ≤ ∑ j, b j :=
    (finiteClockPrefix_mono a ha (Nat.le_succ i.val)).trans hs
  dsimp only [f]
  rw [finiteClockPrefix_zero, finiteClockPrefix_total,
    min_eq_left hs, min_eq_left hs',
    min_eq_right (finiteClockPrefix_nonneg a ha _),
    min_eq_right (finiteClockPrefix_nonneg a ha _)]
  simpa only [sub_self, sub_zero] using finiteClockPrefix_succ_sub a i

/-- Column sums are the unchanged target masses. -/
theorem orderedClockFlow_col_sum {M L : ℕ} (a : Fin M → ℝ) (b : Fin L → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (htotal : ∑ i, a i = ∑ j, b j)
    (j : Fin L) : (∑ i, orderedClockFlow a b i j) = b j := by
  have hswap (i : Fin M) : orderedClockFlow a b i j = orderedClockFlow b a j i := by
    unfold orderedClockFlow
    simp only [min_comm]
    ring
  simp_rw [hswap]
  exact orderedClockFlow_row_sum b a hb ha htotal.symm j

/-- A forbidden pair carries zero mass whenever its target interval ends
before its source interval starts. Ordered Hall inequalities provide exactly
these prefix inequalities for separated clock bins. -/
theorem orderedClockFlow_eq_zero_of_prefix_le
    {M L : ℕ} (a : Fin M → ℝ) (b : Fin L → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (i : Fin M) (j : Fin L)
    (hprefix : finiteClockPrefix b (j.val + 1) ≤ finiteClockPrefix a i.val) :
    orderedClockFlow a b i j = 0 := by
  have hs := finiteClockPrefix_mono a ha (Nat.le_succ i.val)
  have ht := finiteClockPrefix_mono b hb (Nat.le_succ j.val)
  unfold orderedClockFlow
  rw [min_eq_right (hprefix.trans hs), min_eq_right hprefix,
    min_eq_right (ht.trans (hprefix.trans hs)), min_eq_right (ht.trans hprefix)]
  ring

/-- Every coupling weight is measurable in the original profile parameters:
the construction uses only finite sums, minima and differences. -/
theorem measurable_orderedClockFlow
    {Ω : Type*} [MeasurableSpace Ω] {M L : ℕ}
    (a : Ω → Fin M → ℝ) (b : Ω → Fin L → ℝ)
    (ha : ∀ i, Measurable (fun ω ↦ a ω i)) (hb : ∀ j, Measurable (fun ω ↦ b ω j))
    (i : Fin M) (j : Fin L) : Measurable (fun ω ↦ orderedClockFlow (a ω) (b ω) i j) := by
  have hs (k : ℕ) : Measurable (fun ω ↦ finiteClockPrefix (a ω) k) := by
    apply Finset.measurable_sum
    intro l hl
    by_cases h : l < M
    · simpa only [dite_eq_left h] using ha ⟨l, h⟩
    · simpa only [dite_eq_right h] using (measurable_const : Measurable (fun _ : Ω ↦ (0 : ℝ)))
  have ht (k : ℕ) : Measurable (fun ω ↦ finiteClockPrefix (b ω) k) := by
    apply Finset.measurable_sum
    intro l hl
    by_cases h : l < L
    · simpa only [dite_eq_left h] using hb ⟨l, h⟩
    · simpa only [dite_eq_right h] using (measurable_const : Measurable (fun _ : Ω ↦ (0 : ℝ)))
  exact (((hs _).min (ht _)).sub ((hs _).min (ht _))).sub ((hs _).min (ht _)) |>.add ((hs _).min (ht _))

/-- The cumulative mass is the sum on the actual prefix of finite classes. -/
theorem finiteClockPrefix_eq_filter {M : ℕ} (a : Fin M → ℝ) {k : ℕ} (hk : k ≤ M) :
    finiteClockPrefix a k = ∑ i ∈ Finset.univ.filter (fun i : Fin M ↦ i.val < k), a i := by
  classical
  unfold finiteClockPrefix
  rw [Finset.sum_filter, Finset.sum_fin_eq_sum_range]
  trans ∑ l ∈ Finset.range k, if h : l < M then
    (if l < k then a ⟨l, h⟩ else 0) else 0
  · apply Finset.sum_congr rfl
    intro l hl
    have hlk := Finset.mem_range.mp hl
    have hlM := hlk.trans_le hk
    simp only [dite_eq_left hlM, ite_eq_left hlk]
  · apply Finset.sum_subset (Finset.range_mono hk)
    intro l hlM hlk
    have hnot : ¬ l < k := fun h ↦ hlk (Finset.mem_range.mpr h)
    rw [dite_eq_left (Finset.mem_range.mp hlM), ite_eq_right hnot]

/-- Target classes reachable from a finite source cut. -/
def orderedClockNeighbors {M L : ℕ} (allowed : Fin M → Fin L → Prop) (A : Finset (Fin M)) :
    Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun j ↦ ∃ i ∈ A, allowed i j

/-- Hall inequalities imply every prefix separation needed by the explicit
interval-overlap flow, for the ordered graph furnished by scalar clock bins. -/
theorem prefix_le_of_ordered_hall
    {M L : ℕ} (allowed : Fin M → Fin L → Prop)
    (horder : ∀ i i' j j', i ≤ i' → j' ≤ j → allowed i' j' → allowed i j)
    (a : Fin M → ℝ) (b : Fin L → ℝ)
    (hb : ∀ j, 0 ≤ b j) (htotal : ∑ i, a i = ∑ j, b j)
    (hhall : ∀ A : Finset (Fin M), (∑ i ∈ A, a i) ≤
      ∑ j ∈ orderedClockNeighbors allowed A, b j)
    (i : Fin M) (j : Fin L) (hnot : ¬ allowed i j) :
    finiteClockPrefix b (j.val + 1) ≤ finiteClockPrefix a i.val := by
  classical
  let A := Finset.univ.filter fun i' : Fin M ↦ i ≤ i'
  let B := Finset.univ.filter fun j' : Fin L ↦ j < j'
  have hsub : orderedClockNeighbors allowed A ⊆ B := by
    intro j' hj'
    obtain ⟨i', hi', hij⟩ := (Finset.mem_filter.mp hj').2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hle
    exact hnot (horder i i' j j' (Finset.mem_filter.mp hi').2 (le_of_not_gt hle) hij)
  have hhall' := (hhall A).trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j' hj' hnj' ↦ hb j'))
  have hs := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i' : Fin M ↦ i'.val < i.val) a
  have ht := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j' : Fin L ↦ j'.val < j.val + 1) b
  rw [← finiteClockPrefix_eq_filter a i.isLt.le] at hs
  rw [← finiteClockPrefix_eq_filter b j.isLt] at ht
  have hAS : (Finset.univ.filter fun i' : Fin M ↦ ¬ i'.val < i.val) = A := by
    ext i'
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_iff_val_le_val]
  have hBT : (Finset.univ.filter fun j' : Fin L ↦ ¬ j'.val < j.val + 1) = B := by
    ext j'
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.lt_def]
    omega
  rw [hAS] at hs
  rw [hBT] at ht
  linarith

/-- Explicit measurable fractional Hall construction for ordered clock-bin
graphs. It preserves all actual class masses and uses only legal class edges. -/
theorem orderedClockFlow_of_hall
    {M L : ℕ} (allowed : Fin M → Fin L → Prop)
    (horder : ∀ i i' j j', i ≤ i' → j' ≤ j → allowed i' j' → allowed i j)
    (a : Fin M → ℝ) (b : Fin L → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (htotal : ∑ i, a i = ∑ j, b j)
    (hhall : ∀ A : Finset (Fin M), (∑ i ∈ A, a i) ≤
      ∑ j ∈ orderedClockNeighbors allowed A, b j) :
    (∀ i j, 0 ≤ orderedClockFlow a b i j) ∧
    (∀ i, ∑ j, orderedClockFlow a b i j = a i) ∧
    (∀ j, ∑ i, orderedClockFlow a b i j = b j) ∧
    ∀ i j, ¬ allowed i j → orderedClockFlow a b i j = 0 := by
  refine ⟨orderedClockFlow_nonneg a b ha hb,
    orderedClockFlow_row_sum a b ha hb htotal,
    orderedClockFlow_col_sum a b ha hb htotal, ?_⟩
  intro i j hnot
  exact orderedClockFlow_eq_zero_of_prefix_le a b ha hb i j
    (prefix_le_of_ordered_hall allowed horder a b hb htotal hhall i j hnot)

end OTSelector.Reconstruction
