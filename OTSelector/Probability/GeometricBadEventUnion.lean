import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Geometric Bad Event Union

Conditions: A fixed natural-indexed family of arbitrary events on a finite measure space, real outer-mass bounds exp(−m) for m≥1 and cutoff N≥1; only the measurability helper assumes measurable events.

Objects: Measurable tail union, pointwise exclusion outside it, and geometric probability bound exp(−N)/(1−exp(−1)).

Proof detail: Take the countable tail union, apply subadditivity and explicitly sum its geometric exponential upper bounds.

Relation to primary sources: The union-tail step of first Borel-Cantelli with an explicit geometric series; no independence is required.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 2.3, Theorem 2.3.1 and preceding union-tail estimate, pp. 67–68. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=75
-/
/-! A single data-only union controls every subsequent natural scale.
The geometric estimate uses the existing fixed-scale probabilities. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- A countable tail of the already fixed original-data bad events. -/
def natTailEventUnion {Ω : Type*} (A : ℕ → Set Ω) (N : ℕ) : Set Ω := ⋃ j : ℕ, A (N + j)

theorem measurableSet_natTailEventUnion {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n)) (N : ℕ) :
    MeasurableSet (natTailEventUnion A N) := MeasurableSet.iUnion fun j ↦ hA (N + j)

theorem not_mem_natTailEventUnion {Ω : Type*} {A : ℕ → Set Ω} {N m : ℕ}
    (hNm : N ≤ m) {ω : Ω} (hω : ω ∉ natTailEventUnion A N) : ω ∉ A m := by
  intro hm
  apply hω
  apply Set.mem_iUnion.mpr
  refine ⟨m - N, ?_⟩
  simpa only [Nat.add_sub_of_le hNm] using hm

/-- Fixed-scale exponential bounds give one genuine tail bound for all
scales together; no independence of their events is needed. -/
theorem measure_natTailEventUnion_le_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω)
    (hA : ∀ n : ℕ, 1 ≤ n → μ.real (A n) ≤ Real.exp (-(n : ℝ)))
    {N : ℕ} (hN : 1 ≤ N) :
    μ (natTailEventUnion A N) ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ)) / (1 - Real.exp (-1))) := by
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-(N : ℝ)))
  have heq (j : ℕ) : Real.exp (-((N + j : ℕ) : ℝ)) =
      Real.exp (-(N : ℝ)) * Real.exp (-1) ^ j := by
    rw [Nat.cast_add, neg_add, Real.exp_add,
      show -(j : ℝ) = (j : ℝ) * (-1) by ring, Real.exp_nat_mul]
  calc
    _ ≤ ∑' j : ℕ, μ (A (N + j)) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp (-(N : ℝ)) * Real.exp (-1) ^ j) := by
      apply ENNReal.tsum_le_tsum
      intro j
      have hj := hA (N + j) (hN.trans (Nat.le_add_right _ _))
      rw [heq j] at hj
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ (A (N + j)))]
      exact ENNReal.ofReal_le_ofReal hj
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) hgeo.summable,
        hgeo.tsum_eq, div_eq_mul_inv]

/-- The same all-scale event estimate in the real-valued probability form. -/
theorem measureReal_natTailEventUnion_le_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω)
    (hA : ∀ n : ℕ, 1 ≤ n → μ.real (A n) ≤ Real.exp (-(n : ℝ)))
    {N : ℕ} (hN : 1 ≤ N) :
    μ.real (natTailEventUnion A N) ≤ Real.exp (-(N : ℝ)) / (1 - Real.exp (-1)) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (measure_natTailEventUnion_le_exp μ A hA hN)
  have hpos : 0 ≤ Real.exp (-(N : ℝ)) / (1 - Real.exp (-1)) := by
    exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (by norm_num)))
  simpa only [Measure.real, ENNReal.toReal_ofReal hpos] using h

end OTSelector.Probability
