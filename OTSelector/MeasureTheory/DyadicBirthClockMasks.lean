import OTSelector.MeasureTheory.DyadicClockBandPartition
import OTSelector.MeasureTheory.DyadicClockCells
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DyadicBirthClockMasks.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DyadicBirthClockMasks`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.DyadicBirthClockMasks

Conditions: Positive outer scale for partition identities; the last index is explicitly bounded by the finite dyadic band count.
Objects: Triple-index birth cells, their measurable ENNReal indicators, and both countable and finite grouped weighted sums.
Proof detail: Use unique cell membership, remove invalid finite-band indices, reindex nonnegative countable sums and factor out the literal outer mask.

## Mathematical sources

- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Subsection subsec:focal-traffic, proof of thm:focal-full-path-traffic; Births comparable to the focal time, between eq:focal-traffic-old-bound and eq:focal-traffic-birth-large. ../main.tex#L9624

Source relation: A precise measurable half-open realization of the manuscript’s birth-shell and elapsed-time partition. All original weights and endpoints are retained; this is a local decomposition proof.
-/

/-! # Borel birth-clock masks with exact pointwise countable and finite grouping -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1000000

/-- The literal birth-region ENNReal indicator. -/
def dyadicBirthClockRegionMask (ε : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  (dyadicBirthClockRegion ε).indicator 1

/-- The literal triple-indexed cell ENNReal indicator. -/
def dyadicBirthClockMask (ε : ℝ) (k : ℕ × ℕ × ℕ) : ℝ × ℝ → ℝ≥0∞ :=
  (dyadicBirthClockCell ε k).indicator 1

theorem measurableSet_dyadicBirthClockRegion (ε : ℝ) :
    MeasurableSet (dyadicBirthClockRegion ε) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)))

theorem measurableSet_dyadicBirthClockCell (ε : ℝ) (k : ℕ × ℕ × ℕ) :
    MeasurableSet (dyadicBirthClockCell ε k) := by
  have hi : MeasurableSet {p : ℝ × ℝ | k.2.2 < dyadicBirthBandCount k.2.1} := by
    by_cases h : k.2.2 < dyadicBirthBandCount k.2.1 <;> simp only [h, ofPred_true, ofPred_false]
    · exact MeasurableSet.univ
    · exact MeasurableSet.empty
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_Ioc.preimage measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter
        (hi.inter (measurableSet_Ioc.preimage measurable_fst))))

theorem measurable_dyadicBirthClockRegionMask (ε : ℝ) :
    Measurable (dyadicBirthClockRegionMask ε) :=
  measurable_const.indicator (measurableSet_dyadicBirthClockRegion ε)

theorem measurable_dyadicBirthClockMask (ε : ℝ) (k : ℕ × ℕ × ℕ) :
    Measurable (dyadicBirthClockMask ε k) :=
  measurable_const.indicator (measurableSet_dyadicBirthClockCell ε k)

theorem pairwise_disjoint_dyadicBirthClockCell {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun k l : ℕ × ℕ × ℕ ↦
      Disjoint (dyadicBirthClockCell ε k) (dyadicBirthClockCell ε l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro p hk hl
  obtain ⟨i, hi, huniq⟩ := existsUnique_dyadicBirthClockCell hε
    (dyadicBirthClockCell_subset_region hε k hk)
  exact hkl ((huniq k hk).trans (huniq l hl).symm)

theorem iUnion_dyadicBirthClockCell {ε : ℝ} (hε : 0 < ε) :
    (⋃ k : ℕ × ℕ × ℕ, dyadicBirthClockCell ε k) = dyadicBirthClockRegion ε := by
  ext p
  constructor
  · intro hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact dyadicBirthClockCell_subset_region hε k hk
  · intro hp
    obtain ⟨k, hk, _⟩ := existsUnique_dyadicBirthClockCell hε hp
    exact mem_iUnion.mpr ⟨k, hk⟩

theorem dyadicBirthClockMask_ne_zero_iff (ε : ℝ) (k : ℕ × ℕ × ℕ) (p : ℝ × ℝ) :
    dyadicBirthClockMask ε k p ≠ 0 ↔ p ∈ dyadicBirthClockCell ε k := by
  classical
  by_cases h : p ∈ dyadicBirthClockCell ε k <;> simp [dyadicBirthClockMask, h]

theorem dyadicBirthClockRegionMask_ne_zero_iff (ε : ℝ) (p : ℝ × ℝ) :
    dyadicBirthClockRegionMask ε p ≠ 0 ↔ p ∈ dyadicBirthClockRegion ε := by
  classical
  by_cases h : p ∈ dyadicBirthClockRegion ε <;> simp [dyadicBirthClockRegionMask, h]

theorem dyadicBirthClockMask_le_one (ε : ℝ) (k : ℕ × ℕ × ℕ) (p : ℝ × ℝ) :
    dyadicBirthClockMask ε k p ≤ 1 := by
  classical
  by_cases h : p ∈ dyadicBirthClockCell ε k <;> simp [dyadicBirthClockMask, h]

/-- Every point has exactly the original birth indicator after summing all cells. -/
theorem tsum_dyadicBirthClockMask {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    (∑' k : ℕ × ℕ × ℕ, dyadicBirthClockMask ε k p) = dyadicBirthClockRegionMask ε p := by
  classical
  by_cases hp : p ∈ dyadicBirthClockRegion ε
  · obtain ⟨k, hk, huniq⟩ := existsUnique_dyadicBirthClockCell hε hp
    have hmem (l : ℕ × ℕ × ℕ) : p ∈ dyadicBirthClockCell ε l ↔ l = k :=
      ⟨huniq l, fun h ↦ h ▸ hk⟩
    simp [dyadicBirthClockMask, indicator_apply, hmem, dyadicBirthClockRegionMask, hp]
  · have hempty (k : ℕ × ℕ × ℕ) : p ∉ dyadicBirthClockCell ε k :=
      fun hk ↦ hp (dyadicBirthClockCell_subset_region hε k hk)
    simp only [dyadicBirthClockMask, indicator_of_notMem (hempty _), tsum_zero,
      dyadicBirthClockRegionMask, indicator_of_notMem hp]

theorem dyadicBirthClockMask_eq_zero_of_invalid (ε : ℝ) (n j i : ℕ)
    (hi : dyadicBirthBandCount j ≤ i) (p : ℝ × ℝ) :
    dyadicBirthClockMask ε (n, j, i) p = 0 := by
  have hn : p ∉ dyadicBirthClockCell ε (n, j, i) := fun h ↦ (not_lt_of_ge hi) h.2.2.2.1
  exact indicator_of_notMem hn _

/-- The last index is genuinely finite, with exactly the prescribed original band count. -/
theorem tsum_dyadicBirthClockMask_eq_finite_sum (ε : ℝ) (n j : ℕ) (p : ℝ × ℝ) :
    (∑' i : ℕ, dyadicBirthClockMask ε (n, j, i) p) =
      ∑ i ∈ Finset.range (dyadicBirthBandCount j), dyadicBirthClockMask ε (n, j, i) p := by
  exact tsum_eq_sum (fun i hi ↦ dyadicBirthClockMask_eq_zero_of_invalid ε n j i
    (Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hi)) p)

theorem tsum_finiteSum_dyadicBirthClockMask {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    (∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      dyadicBirthClockMask ε (n, j, i) p) = dyadicBirthClockRegionMask ε p := by
  have h := tsum_dyadicBirthClockMask hε p
  rw [ENNReal.tsum_prod'] at h
  simp_rw [ENNReal.tsum_prod', tsum_dyadicBirthClockMask_eq_finite_sum] at h
  exact h

/-- Any additional mask can be retained exactly, including arbitrary scene dependence. -/
theorem tsum_weighted_dyadicBirthClockMask {ε : ℝ} (hε : 0 < ε)
    (θ : ℝ × ℝ → ℝ≥0∞) (p : ℝ × ℝ) :
    (∑' k : ℕ × ℕ × ℕ, θ p * dyadicBirthClockMask ε k p) =
      θ p * dyadicBirthClockRegionMask ε p := by
  rw [ENNReal.tsum_mul_left, tsum_dyadicBirthClockMask hε]


/-- Finite narrow-band grouping also retains every additional outer mask exactly. -/
theorem tsum_finiteSum_weighted_dyadicBirthClockMask {ε : ℝ} (hε : 0 < ε)
    (θ : ℝ × ℝ → ℝ≥0∞) (p : ℝ × ℝ) :
    (∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      θ p * dyadicBirthClockMask ε (n, j, i) p) = θ p * dyadicBirthClockRegionMask ε p := by
  simp_rw [← Finset.mul_sum, ENNReal.tsum_mul_left]
  rw [tsum_finiteSum_dyadicBirthClockMask hε]

end OTSelector.Reconstruction

end
end
