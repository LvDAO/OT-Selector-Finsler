import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Interval.Set.Union
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DyadicClockBandPartition.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DyadicClockBandPartition`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.DyadicClockBandPartition

## Lemma skeleton

* **Conditions:** A deterministic nonnegative interval width, natural finite count and positive dyadic birth scale.
* **Objects:** Pairwise disjoint half-open clock bands, exact finite union/width/count identities and one shared nonnegative energy budget.
* **Proof detail:** Check interval endpoint order, telescope the finite half-open partition, compute the dyadic count/width algebra and integrate disjoint pullback bands once.

## Mathematical sources

- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Deterministic interval algebra and finite disjoint integration; no equal-probability clock-mass partition is assumed.
-/

/-! Deterministic half-open clock partitions used for interleaved births. Their
number and width are chosen from dyadic scales, without balancing clock masses. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- The `i`th consecutive physical clock band of width `h` starting at `a`. -/
def clockGridBand (a h : ℝ) (i : ℕ) : Set ℝ := Ioc (a + i * h) (a + (i + 1) * h)

/-- Distinct consecutive clock bands share no endpoint because the left endpoint
is excluded and the right endpoint is included. -/
theorem pairwise_disjoint_clockGridBand (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    Pairwise (fun i j : ℕ ↦ Disjoint (clockGridBand a h i) (clockGridBand a h j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · apply Ioc_disjoint_Ioc_of_le
    have hn : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
    change a + ((i : ℝ) + 1) * h ≤ a + (j : ℝ) * h
    push_cast at hn
    nlinarith [mul_le_mul_of_nonneg_right hn hh]
  · apply Disjoint.symm
    apply Ioc_disjoint_Ioc_of_le
    have hn : ((j + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast Nat.succ_le_of_lt hji
    change a + ((j : ℝ) + 1) * h ≤ a + (i : ℝ) * h
    push_cast at hn
    nlinarith [mul_le_mul_of_nonneg_right hn hh]

/-- Consecutive deterministic bands cover exactly the original half-open shell. -/
theorem biUnion_clockGridBand (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    (⋃ i ∈ Finset.range N, clockGridBand a h i) = Ioc a (a + N * h) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hiN : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hi0 : 0 ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
    change a + (i : ℝ) * h < x ∧ x ≤ a + ((i : ℝ) + 1) * h at hxi
    push_cast at hiN
    exact ⟨by linarith [hxi.1], by nlinarith [hxi.2, mul_le_mul_of_nonneg_right hiN hh]⟩
  · have hc := Ioc_subset_biUnion_Ioc N (fun i : ℕ ↦ a + (i : ℝ) * h)
    simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one, clockGridBand] using hc

/-- A width-`h` band inside the finite shell has precisely its prescribed width
and the endpoints needed by the physical density shell estimate. -/
theorem clockGridBand_endpoints (a : ℝ) {h : ℝ} (hh : 0 ≤ h)
    {i N : ℕ} (hi : i < N) :
    a ≤ a + (i : ℝ) * h ∧ a + ((i : ℝ) + 1) * h ≤ a + N * h ∧
      (a + ((i : ℝ) + 1) * h) - (a + (i : ℝ) * h) = h := by
  have hiN : ((i + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hi
  push_cast at hiN
  exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh),
    by nlinarith [mul_le_mul_of_nonneg_right hiN hh], by ring⟩

/-- The number of narrow bands for the `j`th birth-distance level. -/
def dyadicBirthBandCount (j : ℕ) : ℕ := 8 * 2 ^ j

/-- Every dyadic birth band has width `(t/2^j)/8` and the whole band family
occupies exactly a shell of width `t`. -/
theorem dyadicBirthBand_width_and_total {t : ℝ} (ht : 0 < t) (j : ℕ) :
    0 < t / (dyadicBirthBandCount j : ℝ) ∧
      t / (dyadicBirthBandCount j : ℝ) = (t / (2 : ℝ) ^ j) / 8 ∧
      (dyadicBirthBandCount j : ℝ) * (t / (dyadicBirthBandCount j : ℝ)) = t := by
  have hN : 0 < (dyadicBirthBandCount j : ℝ) := by simp only [dyadicBirthBandCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; positivity
  refine ⟨div_pos ht hN, ?_, mul_div_cancel₀ _ hN.ne'⟩
  simp only [dyadicBirthBandCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- The literal dyadic source shell is partitioned into the stated finite number
of narrow bands; no atom, geometry or mass-equality hypothesis is needed. -/
theorem biUnion_dyadicBirthBands (l : ℝ) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    (⋃ i ∈ Finset.range (dyadicBirthBandCount j),
      clockGridBand (l + t) (t / (dyadicBirthBandCount j : ℝ)) i) = Ioc (l + t) (l + 2 * t) := by
  rw [biUnion_clockGridBand _ (dyadicBirthBand_width_and_total ht j).1.le,
    (dyadicBirthBand_width_and_total ht j).2.2]
  congr 1
  ring

/-- Splitting an actual original mark law into the deterministic disjoint clock
bands spends at most its original energy budget, retaining all clock-energy correlations. -/
theorem sum_clockGridBand_energy_le {Z : Type*} [MeasurableSpace Z]
    (η : Measure Z) {clock : Z → ℝ} (hclock : Measurable clock)
    (energy : Z → ℝ≥0∞) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    (∑ i ∈ Finset.range N, ∫⁻ z in clock ⁻¹' clockGridBand a h i, energy z ∂η) ≤
      ∫⁻ z, energy z ∂η := by
  have hd : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
      (fun i ↦ clock ⁻¹' clockGridBand a h i) := by
    intro i _ j _ hij
    exact ((pairwise_disjoint_clockGridBand a hh) hij).preimage clock
  rw [← lintegral_biUnion_finset hd (fun i _ ↦ measurableSet_Ioc.preimage hclock)]
  exact lintegral_mono' Measure.restrict_le_self (fun _ ↦ le_rfl)

end OTSelector.Reconstruction

end
end
