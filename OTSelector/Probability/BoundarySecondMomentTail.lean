import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Boundary Second Moment Tail

Conditions: A real measurable observable with integrable square and diverging positive cutoffs; each statement retains its displayed scale and nonnegativity hypotheses.

Objects: Vanishing weighted second-moment tails and the sharpened tail conclusion R² P(|f|≥R)→0.

Proof detail: Dominate each truncated/weighted integrand by f² and apply dominated convergence; compare the large-value probability multiplied by R² to its second-moment tail.

Relation to primary sources: A direct dominated-convergence consequence of a finite second moment; the final limit is stronger than the uniform bound supplied by Markov alone.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.2, Theorems 1.6.5–1.6.7, p. 30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
-/
/-! Finite second moment controls weighted grid crossing and large-edge tails. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X]

/-- The shift-averaged weighted crossing loss vanishes using the second
moment alone; no third moment is needed. -/
theorem tendsto_weighted_crossing_second_moment_zero
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f)
    (hi : Integrable (fun x ↦ (f x) ^ 2) μ)
    (C : ℝ) (hC : 0 ≤ C) (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫ x, (f x) ^ 2 * min 1 (C * |f x| / R n) ∂μ)
      atTop (𝓝 0) := by
  have habs : Measurable (fun x ↦ |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hz (n : ℕ) (x : X) : 0 ≤ C * |f x| / R n :=
    div_nonneg (mul_nonneg hC (abs_nonneg _)) (hRpos n).le
  have hlim (x : X) : Tendsto (fun n ↦ (f x) ^ 2 * min 1 (C * |f x| / R n))
      atTop (𝓝 (0 : ℝ)) := by
    have hd : Tendsto (fun n ↦ C * |f x| / R n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
        (tendsto_const_nhds (x := C * |f x|)).mul (tendsto_inv_atTop_zero.comp hR)
    simpa only [min_eq_right zero_le_one, mul_zero] using
      (tendsto_const_nhds (x := (f x) ^ 2)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).min hd)
  have hconv := tendsto_integral_of_dominated_convergence (fun x ↦ (f x) ^ 2)
    (F := fun n x ↦ (f x) ^ 2 * min 1 (C * |f x| / R n))
    (f := fun _ ↦ (0 : ℝ))
    (fun n ↦ ((hf.pow_const 2).mul (measurable_const.min
      ((measurable_const.mul habs).div_const (R n)))).aestronglyMeasurable)
    hi (fun n ↦ ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_min zero_le_one (hz n x)))]
      exact mul_le_of_le_one_right (sq_nonneg _) (min_le_left _ _))
    (ae_of_all _ hlim)
  simpa only [integral_zero] using hconv

/-- The actual large-displacement second-moment tail vanishes. -/
theorem tendsto_second_moment_tail_zero
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f)
    (hi : Integrable (fun x ↦ (f x) ^ 2) μ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫ x, {x | R n ≤ |f x|}.indicator (fun x ↦ (f x) ^ 2) x ∂μ)
      atTop (𝓝 0) := by
  have habs : Measurable (fun x ↦ |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hA (n : ℕ) : MeasurableSet {x | R n ≤ |f x|} :=
    measurableSet_le measurable_const habs
  have hconv := tendsto_integral_of_dominated_convergence (fun x ↦ (f x) ^ 2)
    (F := fun n x ↦ {x | R n ≤ |f x|}.indicator (fun x ↦ (f x) ^ 2) x)
    (f := fun _ ↦ (0 : ℝ))
    (fun n ↦ (hi.indicator (hA n)).aestronglyMeasurable) hi
    (fun n ↦ ae_of_all _ fun x ↦ by
      by_cases hx : R n ≤ |f x|
      · have hx' : x ∈ {y | R n ≤ |f y|} := hx
        simp only [Set.indicator_of_mem hx', Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))]
        exact le_rfl
      · have hx' : x ∉ {y | R n ≤ |f y|} := hx
        simp only [Set.indicator_of_notMem hx', norm_zero]
        exact sq_nonneg _)
    (ae_of_all _ fun x ↦ by
      have he : ∀ᶠ n in atTop,
          {x | R n ≤ |f x|}.indicator (fun x ↦ (f x) ^ 2) x = 0 := by
        filter_upwards [hR.eventually (eventually_gt_atTop |f x|)] with n hn
        exact Set.indicator_of_notMem (show x ∉ {y | R n ≤ |f y|} from not_le.mpr hn) _
      exact tendsto_const_nhds.congr' (he.mono fun _ hn ↦ hn.symm))
  simpa only [integral_zero] using hconv

/-- The squared cutoff scale times the original large-edge probability
vanishes; this is stronger than the bounded second-moment Markov estimate. -/
theorem tendsto_sq_mul_large_edge_probability_zero
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hi : Integrable (fun x ↦ (f x) ^ 2) μ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 ≤ R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ R n ^ 2 * μ.real {x | R n ≤ |f x|}) atTop (𝓝 0) := by
  have habs : Measurable (fun x ↦ |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hbound (n : ℕ) : R n ^ 2 * μ.real {x | R n ≤ |f x|} ≤
      ∫ x, {x | R n ≤ |f x|}.indicator (fun x ↦ (f x) ^ 2) x ∂μ := by
    have hA : MeasurableSet {x | R n ≤ |f x|} := measurableSet_le measurable_const habs
    have hh := integral_mono ((integrable_const (R n ^ 2)).indicator hA) (hi.indicator hA)
      (fun x ↦ by
        by_cases hx : R n ≤ |f x|
        · have hx' : x ∈ {y | R n ≤ |f y|} := hx
          simp only [Set.indicator_of_mem hx']
          nlinarith [sq_abs (f x), abs_nonneg (f x), hRpos n]
        · have hx' : x ∉ {y | R n ≤ |f y|} := hx
          simp only [Set.indicator_of_notMem hx']
          exact le_rfl)
    simpa only [integral_indicator_const _ hA, smul_eq_mul, mul_comm] using hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_second_moment_tail_zero μ f hf hi R hR)
    (fun n ↦ mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg) hbound

end OTSelector.Probability
