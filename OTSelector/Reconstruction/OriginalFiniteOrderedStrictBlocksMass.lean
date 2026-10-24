import OTSelector.Reconstruction.OriginalFiniteOrderedStrictBlocksFlow

/-! Exact original masses and crossing zeros on the constructed strict blocks. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 600000

/-- Actual class indices between the two constructed zero cuts. -/
def FiniteSurplusStrictBlock.classes {H : ℕ → ℝ} {N : ℕ}
    (b : FiniteSurplusStrictBlock H N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter b.Contains

/-- Every constructed block contains an original class. -/
theorem FiniteSurplusStrictBlock.classes_nonempty {H : ℕ → ℝ} {N : ℕ}
    (b : FiniteSurplusStrictBlock H N) : b.classes.Nonempty := by
  classical
  have hlr : b.lower.val < b.upper.val := b.consecutive.1
  have hr : b.upper.val ≤ N := Nat.le_of_lt_succ b.upper.isLt
  let i : Fin N := ⟨b.lower.val, by omega⟩
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hlr⟩⟩

/-- Subtracting two actual finite prefixes gives the literal intervening class
mass; no interval-density or connected-support assumption is used. -/
theorem finiteClassPrefix_split
    {N : ℕ} (a : Fin N → ℝ) (l r : ℕ) (hlr : l ≤ r) (hr : r ≤ N) :
    finiteClockPrefix a r = finiteClockPrefix a l +
      ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ l ≤ i.val ∧ i.val < r), a i := by
  classical
  rw [finiteClockPrefix_eq_filter a hr, finiteClockPrefix_eq_filter a (hlr.trans hr)]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hil : i.val < l
  · have hir : i.val < r := hil.trans_le hlr
    simp only [hil, hir, ite_true, not_le.mpr hil, false_and, ite_false, add_zero]
  · by_cases hir : i.val < r
    · simp [hil, hir, Nat.le_of_not_gt hil]
    · simp [hil, hir]

/-- The exact source and target class masses agree on every constructed block. -/
theorem FiniteSurplusStrictBlock.mass_balance
    {N : ℕ} (a c : Fin N → ℝ) (b : FiniteSurplusStrictBlock (finiteClassSurplus a c) N) :
    (∑ i ∈ b.classes, a i) = ∑ i ∈ b.classes, c i := by
  have hs := finiteClassPrefix_split a b.lower.val b.upper.val b.consecutive.1.le
    (Nat.le_of_lt_succ b.upper.isLt)
  have ht := finiteClassPrefix_split c b.lower.val b.upper.val b.consecutive.1.le
    (Nat.le_of_lt_succ b.upper.isLt)
  have hl := b.consecutive.2.1
  have hr := b.consecutive.2.2.1
  dsimp only [finiteClassSurplus] at hl hr
  have hset : b.classes = Finset.univ.filter
      (fun i : Fin N ↦ b.lower.val ≤ i.val ∧ i.val < b.upper.val) := by
    ext i
    simp only [FiniteSurplusStrictBlock.classes, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hset]
  linarith

/-- A balanced block made from actual nonzero classes has positive mass of
each original colour, even though individual classes are monochrome. -/
theorem FiniteSurplusStrictBlock.mass_pos
    {N : ℕ} (a c : Fin N → ℝ) (b : FiniteSurplusStrictBlock (finiteClassSurplus a c) N)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) (hpos : ∀ i, 0 < a i + c i) :
    0 < ∑ i ∈ b.classes, a i := by
  classical
  obtain ⟨i, hi⟩ := b.classes_nonempty
  have hs : a i + c i ≤ ∑ j ∈ b.classes, (a j + c j) :=
    Finset.single_le_sum (fun j _ ↦ add_nonneg (ha j) (hc j)) hi
  have hpositive := (hpos i).trans_le hs
  rw [Finset.sum_add_distrib, ← b.mass_balance a c] at hpositive
  linarith

/-- A block's local prefix surplus is the original global surplus, because
its actual lower prefix cut is tight. -/
theorem FiniteSurplusStrictBlock.local_prefix_surplus
    {N : ℕ} (a c : Fin N → ℝ) (b : FiniteSurplusStrictBlock (finiteClassSurplus a c) N)
    {k : ℕ} (hlk : b.lower.val ≤ k) (hkr : k ≤ b.upper.val) :
    (∑ i ∈ b.classes.filter (fun i ↦ i.val < k), a i) -
        (∑ i ∈ b.classes.filter (fun i ↦ i.val < k), c i) = finiteClassSurplus a c k := by
  classical
  have hset : b.classes.filter (fun i ↦ i.val < k) =
      Finset.univ.filter (fun i : Fin N ↦ b.lower.val ≤ i.val ∧ i.val < k) := by
    ext i
    simp only [FiniteSurplusStrictBlock.classes, FiniteSurplusStrictBlock.Contains, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hset]
  have hs := finiteClassPrefix_split a b.lower.val k hlk
    (hkr.trans (Nat.le_of_lt_succ b.upper.isLt))
  have ht := finiteClassPrefix_split c b.lower.val k hlk
    (hkr.trans (Nat.le_of_lt_succ b.upper.isLt))
  have hl := b.consecutive.2.1
  dsimp only [finiteClassSurplus] at hl ⊢
  linarith

/-- Every actual forward flow entry leaving a constructed block is zero. -/
theorem finiteClassFlow_zero_leaving_block
    {N : ℕ} (P : Fin N → Fin N → ℝ) (a c : Fin N → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = c j)
    (hzero : ∀ i j, ¬ i < j → P i j = 0)
    (b : FiniteSurplusStrictBlock (finiteClassSurplus a c) N)
    (i j : Fin N) (hi : b.Contains i) (hj : ¬ b.Contains j) : P i j = 0 := by
  by_cases hij : i < j
  · have hjr : b.upper.val ≤ j.val := by
      dsimp only [FiniteSurplusStrictBlock.Contains] at hi hj
      have hij' : i.val < j.val := hij
      omega
    exact finiteClassFlow_zero_crossing_of_tight P a c hP hrow hcol hzero b.upper.val
      (Nat.le_of_lt_succ b.upper.isLt) b.consecutive.2.2.1 i j hi.2 hjr
  · exact hzero i j hij

/-- Every actual forward flow entry entering a different constructed block is
zero at the actual lower tight prefix cut. -/
theorem finiteClassFlow_zero_entering_block
    {N : ℕ} (P : Fin N → Fin N → ℝ) (a c : Fin N → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = c j)
    (hzero : ∀ i j, ¬ i < j → P i j = 0)
    (b : FiniteSurplusStrictBlock (finiteClassSurplus a c) N)
    (i j : Fin N) (hi : ¬ b.Contains i) (hj : b.Contains j) : P i j = 0 := by
  by_cases hij : i < j
  · have hil : i.val < b.lower.val := by
      dsimp only [FiniteSurplusStrictBlock.Contains] at hi hj
      have hij' : i.val < j.val := hij
      omega
    exact finiteClassFlow_zero_crossing_of_tight P a c hP hrow hcol hzero b.lower.val
      (Nat.le_of_lt_succ b.lower.isLt) b.consecutive.2.1 i j hil hj.1
  · exact hzero i j hij

end OTSelector.Reconstruction
