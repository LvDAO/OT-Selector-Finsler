import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointPoisson
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The prescribed input Laplace functional retains its exact first moment

Nonnegative bounded exponential difference quotients recover the unbounded
original input test by Fatou. No uniform integrability or moment hypothesis is
needed to identify even an infinite first moment from its Laplace functional.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private def inputLaplaceSlope (s x : ℝ) := (1 - Real.exp (-s * x)) / s

private theorem inputLaplaceSlope_bounds {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    0 ≤ inputLaplaceSlope s x ∧ inputLaplaceSlope s x ≤ x ∧ inputLaplaceSlope s x ≤ 1 / s := by
  have he : Real.exp (-s * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hlin := Real.add_one_le_exp (-s * x)
  dsimp [inputLaplaceSlope]
  exact ⟨div_nonneg (sub_nonneg.mpr he) hs.le,
    (div_le_iff₀ hs).mpr (by nlinarith),
    div_le_div_of_nonneg_right (by linarith [Real.exp_nonneg (-s * x)]) hs.le⟩

private theorem tendsto_inputLaplaceSlope (x : ℝ) :
    Tendsto (fun n : ℕ ↦ inputLaplaceSlope (1 / ((n : ℝ) + 1)) x) atTop (𝓝 x) := by
  have hd : HasDerivAt (fun s : ℝ ↦ 1 - Real.exp (-s * x)) x 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      (((hasDerivAt_id (0 : ℝ)).neg.mul_const x).exp) using 1; simp
  have hs : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall (fun n ↦ (show 0 < 1 / ((n : ℝ) + 1) by positivity))⟩
  have h := hd.tendsto_slope_zero_right.comp hs
  simpa only [zero_add, neg_zero, zero_mul, Real.exp_zero, sub_self, sub_zero,
    mul_zero, mul_one, one_mul, smul_eq_mul, inputLaplaceSlope, div_eq_mul_inv,
    mul_comm, Function.comp_def] using h

private theorem lintegral_ofReal_le_of_laplace_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ y, 0 ≤ g y)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (-s * f x) ∂P) = ∫ y, Real.exp (-s * g y) ∂Q) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂P) ≤ ∫⁻ y, ENNReal.ofReal (g y) ∂Q := by
  let s (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hfp (n : ℕ) : Integrable (fun x ↦ Real.exp (-s n * f x)) P :=
    Integrable.of_bound (show Measurable (fun x ↦ Real.exp (-s n * f x)) by fun_prop).aestronglyMeasurable
      1 (.of_forall (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith [hs n, hfn x])))
  have hgp (n : ℕ) : Integrable (fun y ↦ Real.exp (-s n * g y)) Q :=
    Integrable.of_bound (show Measurable (fun y ↦ Real.exp (-s n * g y)) by fun_prop).aestronglyMeasurable
      1 (.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith [hs n, hgn y])))
  have hfi (n : ℕ) : Integrable (fun x ↦ inputLaplaceSlope (s n) (f x)) P :=
    ((integrable_const 1).sub (hfp n)).div_const (s n)
  have hgi (n : ℕ) : Integrable (fun y ↦ inputLaplaceSlope (s n) (g y)) Q :=
    ((integrable_const 1).sub (hgp n)).div_const (s n)
  have heq (n : ℕ) : (∫⁻ x, ENNReal.ofReal (inputLaplaceSlope (s n) (f x)) ∂P) =
      ∫⁻ y, ENNReal.ofReal (inputLaplaceSlope (s n) (g y)) ∂Q := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n)
        (.of_forall (fun x ↦ (inputLaplaceSlope_bounds (hs n) (hfn x)).1)),
      ← ofReal_integral_eq_lintegral_ofReal (hgi n)
        (.of_forall (fun y ↦ (inputLaplaceSlope_bounds (hs n) (hgn y)).1))]
    congr 1
    dsimp only [inputLaplaceSlope]
    rw [integral_div, integral_div, integral_sub (integrable_const _) (hfp n),
      integral_sub (integrable_const _) (hgp n), hlap (s n) (hs n)]
    simp
  calc
    _ = ∫⁻ x, atTop.liminf (fun n ↦ ENNReal.ofReal (inputLaplaceSlope (s n) (f x))) ∂P := by
      apply lintegral_congr
      intro x
      exact ((ENNReal.continuous_ofReal.tendsto (f x)).comp (tendsto_inputLaplaceSlope (f x))).liminf_eq.symm
    _ ≤ atTop.liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (inputLaplaceSlope (s n) (f x)) ∂P) := by
      apply lintegral_liminf_le
      intro n
      apply ENNReal.measurable_ofReal.comp
      dsimp [inputLaplaceSlope]
      fun_prop
    _ = atTop.liminf (fun n ↦ ∫⁻ y, ENNReal.ofReal (inputLaplaceSlope (s n) (g y)) ∂Q) := by simp_rw [heq]
    _ ≤ ∫⁻ y, ENNReal.ofReal (g y) ∂Q := by
      apply liminf_le_of_frequently_le'
      exact (Filter.Eventually.of_forall (fun n ↦ lintegral_mono (fun y ↦ ENNReal.ofReal_le_ofReal
        (inputLaplaceSlope_bounds (hs n) (hgn y)).2.1))).frequently

/-- Equal nonnegative Laplace transforms determine the original extended first
moment, with no supplied moment finiteness or uniform-integrability assumption. -/
theorem lintegral_ofReal_eq_of_nonnegative_laplace_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ y, 0 ≤ g y)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (-s * f x) ∂P) = ∫ y, Real.exp (-s * g y) ∂Q) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂P) = ∫⁻ y, ENNReal.ofReal (g y) ∂Q :=
  le_antisymm (lintegral_ofReal_le_of_laplace_eq P Q f g hf hg hfn hgn hlap)
    (lintegral_ofReal_le_of_laplace_eq Q P g f hg hf hgn hfn (fun s hs ↦ (hlap s hs).symm))

end OTSelector.Reconstruction
