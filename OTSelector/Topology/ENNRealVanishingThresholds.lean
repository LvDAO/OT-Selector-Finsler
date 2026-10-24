import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Topology.ENNRealVanishingThresholds

Conditions: A nonnegative extended-real sequence tends to zero.

Objects: Positive finite thresholds tending to zero such that loss divided by threshold also tends to zero.

Proof detail: Take threshold_n = sqrt(toReal(loss_n)) + 1/(n+1), converted to ENNReal. Eventually loss is finite, and loss/threshold ≤ sqrt(loss); squeeze gives the second limit.

## Mathematical sources

- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).
- [Stephen Boyd, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=85): Section 3.1.5, powers and geometric mean examples, pp. 71–73.

Source relation: Explicit locally proved threshold construction; the reference supplies only elementary powers and squeeze.
-/

/-! A vanishing original population loss supplies its own positive finite
discard thresholds. No additional quantitative recovery rate is needed. -/

open Filter
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Probability

/-- Every vanishing loss admits positive finite thresholds for which both the
threshold and the corresponding discard-probability bound vanish. -/
theorem exists_vanishing_discard_thresholds
    (loss : ℕ → ℝ≥0∞) (hloss : Tendsto loss atTop (𝓝 0)) :
    ∃ threshold : ℕ → ℝ≥0∞,
      (∀ n, 0 < threshold n ∧ threshold n ≠ ⊤) ∧
      Tendsto threshold atTop (𝓝 0) ∧
      Tendsto (fun n ↦ loss n / threshold n) atTop (𝓝 0) := by
  let root : ℕ → ℝ := fun n ↦ Real.sqrt (loss n).toReal
  let threshold : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (root n + 1 / ((n : ℝ) + 1))
  have hroot : Tendsto root atTop (𝓝 0) := by
    have hr := Real.continuous_sqrt.tendsto 0
    simpa only [Real.sqrt_zero, ENNReal.toReal_zero, Function.comp_def] using
      hr.comp ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hloss)
  have hpos (n : ℕ) : 0 < threshold n := by
    apply ENNReal.ofReal_pos.mpr
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)
  have htop (n : ℕ) : threshold n ≠ ⊤ := ENNReal.ofReal_ne_top
  have hthreshold : Tendsto threshold atTop (𝓝 0) := by
    simpa only [zero_add, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hroot.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  refine ⟨threshold, fun n ↦ ⟨hpos n, htop n⟩, hthreshold, ?_⟩
  have hupper : ∀ᶠ n in atTop, loss n / threshold n ≤ ENNReal.ofReal (root n) := by
    filter_upwards [hloss.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))] with n hn
    have hnfinite : loss n ≠ ⊤ := ne_top_of_lt hn
    have hsquare : ENNReal.ofReal (root n) * ENNReal.ofReal (root n) = loss n := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hnfinite]
    apply (ENNReal.div_le_iff (ne_of_gt (hpos n)) (htop n)).mpr
    rw [← hsquare]
    have hrootle : ENNReal.ofReal (root n) ≤ threshold n :=
      ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
    exact mul_le_mul' le_rfl hrootle
  have hrootENN : Tendsto (fun n ↦ ENNReal.ofReal (root n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hroot
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hrootENN (Eventually.of_forall (fun _ ↦ bot_le)) hupper

end OTSelector.Probability
