import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Zero Cost Weak Limit

Conditions: Continuous nonnegative cost, continuous probability-plan map and weak convergence of outer probability laws; expected cost tends to zero, or each approximant is already supported on cost zero.

Objects: A bounded continuous capped-cost readout and a.e. zero-cost support of the limiting conditional probability plan.

Proof detail: Cap the cost by one, pass its bounded continuous readout through weak convergence, and use nonnegative zero expectation to prove zero cost on almost every limiting plan.

Relation to primary sources: A bounded-test weak-limit argument using a cap, not a uniform-integrability assumption or unbounded continuous-test theorem.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Sections 437J(d),(f),(g), 437K–437L, PDF p. 61 onward. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.4, Exercise 1.4.1, p. 24. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=32
-/
/-!
# Vanishing original nonnegative cost survives weak plan laws

A bounded continuous test detects the zero set of the unchanged nonnegative
cost. The original expected cost bound suffices without uniform integrability.
-/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A bounded continuous test with exactly the original cost's zero set. -/
def nonnegativeCostCap (e : C(X, ℝ)) (he : ∀ x, 0 ≤ e x) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x ↦ min 1 (e x), continuous_const.min e.continuous⟩
    2 (fun x y ↦ by
      change dist (min 1 (e x)) (min 1 (e y)) ≤ 2
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> linarith [le_min zero_le_one (he x), le_min zero_le_one (he y),
        min_le_left (1 : ℝ) (e x), min_le_left (1 : ℝ) (e y)])

/-- The capped original cost gives a bounded continuous full-plan readout. -/
def probabilityNonnegativeCostCapReadout (e : C(X, ℝ)) (he : ∀ x, 0 ≤ e x) :
    ProbabilityMeasure X →ᵇ ℝ := by
  let k := nonnegativeCostCap e he
  have hb (π : ProbabilityMeasure X) : |∫ x, k x ∂(π : Measure X)| ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := (π : Measure X)) (f := k)
      (ae_of_all _ fun x ↦ by
        change |min 1 (e x)| ≤ 1
        rw [abs_of_nonneg (le_min zero_le_one (he x))]
        exact min_le_left _ _)
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h
  exact BoundedContinuousFunction.mkOfBound
    ⟨fun π ↦ ∫ x, k x ∂(π : Measure X), ProbabilityMeasure.continuous_integral_boundedContinuousFunction k⟩
    2 (fun π τ ↦ by
      change dist (∫ x, k x ∂(π : Measure X)) (∫ x, k x ∂(τ : Measure X)) ≤ 2
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hb π, hb τ]))

/-- A weak law of original probability plans is carried by the zero-cost
face whenever the original expected nonnegative cost vanishes. -/
theorem ae_cost_zero_of_probabilityPlanLaw_weak_of_expected_cost_zero
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] [HasOuterApproxClosed S]
    (P : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (π : S → ProbabilityMeasure X) (hπ : Continuous π)
    (e : C(X, ℝ)) (he : ∀ x, 0 ≤ e x)
    (hcost : Tendsto (fun n ↦ ∫⁻ s, ∫⁻ x, ENNReal.ofReal (e x)
      ∂(π s : Measure X) ∂(P n : Measure S)) atTop (𝓝 0)) :
    ∀ᵐ s ∂(Q : Measure S), ∀ᵐ x ∂(π s : Measure X), e x = 0 := by
  let k := nonnegativeCostCap e he
  let L := probabilityNonnegativeCostCapReadout e he
  let H : S →ᵇ ℝ := L.compContinuous ⟨π, hπ⟩
  have hH (s : S) : H s = ∫ x, k x ∂(π s : Measure X) := rfl
  have hk0 (x : X) : 0 ≤ k x := le_min zero_le_one (he x)
  have hH0 (s : S) : 0 ≤ H s := by rw [hH]; exact integral_nonneg hk0
  have hik (s : S) : Integrable k (π s : Measure X) :=
    Integrable.of_bound k.continuous.aestronglyMeasurable ‖k‖
      (ae_of_all _ fun x ↦ k.norm_coe_le_norm x)
  have hiH (R : ProbabilityMeasure S) : Integrable H (R : Measure S) :=
    Integrable.of_bound H.continuous.aestronglyMeasurable ‖H‖
      (ae_of_all _ fun s ↦ H.norm_coe_le_norm s)
  have hb (n : ℕ) : (∫⁻ s, ENNReal.ofReal (H s) ∂(P n : Measure S)) ≤
      ∫⁻ s, ∫⁻ x, ENNReal.ofReal (e x) ∂(π s : Measure X) ∂(P n : Measure S) := by
    apply lintegral_mono
    intro s
    change ENNReal.ofReal (H s) ≤ ∫⁻ x, ENNReal.ofReal (e x) ∂(π s : Measure X)
    rw [hH, ofReal_integral_eq_lintegral_ofReal (hik s) (ae_of_all _ hk0)]
    exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hzero : Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (H s) ∂(P n : Measure S))
      atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hcost ε hε] with n hn
    exact (hb n).trans hn
  have hreal := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) H
  have hlimit : Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (H s) ∂(P n : Measure S)) atTop
      (𝓝 (ENNReal.ofReal (∫ s, H s ∂(Q : Measure S)))) := by
    have hc := (ENNReal.continuous_ofReal.tendsto _).comp hreal
    exact hc.congr' (Eventually.of_forall fun n ↦
      ofReal_integral_eq_lintegral_ofReal (hiH (P n)) (ae_of_all _ hH0))
  have hE : ∫ s, H s ∂(Q : Measure S) = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp (tendsto_nhds_unique hlimit hzero))
      (integral_nonneg hH0)
  have hHzero := (integral_eq_zero_iff_of_nonneg hH0 (hiH Q)).mp hE
  filter_upwards [hHzero] with s hs
  have hkzero := (integral_eq_zero_iff_of_nonneg hk0 (hik s)).mp
    (by simpa only [hH, Pi.zero_apply] using hs)
  filter_upwards [hkzero] with x hx
  change min 1 (e x) = 0 at hx
  by_cases h : e x ≤ 1
  · simpa only [min_eq_right h] using hx
  · rw [min_eq_left (le_of_not_ge h)] at hx
    norm_num at hx

/-- Once every inner law is carried by the original zero-cost face, a
further weak limit retains that same face. -/
theorem ae_cost_zero_of_probabilityPlanLaw_weak_of_ae_cost_zero
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] [HasOuterApproxClosed S]
    (P : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (π : S → ProbabilityMeasure X) (hπ : Continuous π)
    (e : C(X, ℝ)) (he : ∀ x, 0 ≤ e x)
    (hzero : ∀ n, ∀ᵐ s ∂(P n : Measure S), ∀ᵐ x ∂(π s : Measure X), e x = 0) :
    ∀ᵐ s ∂(Q : Measure S), ∀ᵐ x ∂(π s : Measure X), e x = 0 := by
  apply ae_cost_zero_of_probabilityPlanLaw_weak_of_expected_cost_zero P Q hweak π hπ e he
  have hz (n : ℕ) : (∫⁻ s, ∫⁻ x, ENNReal.ofReal (e x)
      ∂(π s : Measure X) ∂(P n : Measure S)) = 0 := by
    calc
      _ = ∫⁻ _s, (0 : ℝ≥0∞) ∂(P n : Measure S) := by
        apply lintegral_congr_ae
        filter_upwards [hzero n] with s hs
        calc
          _ = ∫⁻ _x, (0 : ℝ≥0∞) ∂(π s : Measure X) :=
            lintegral_congr_ae (hs.mono fun _ hx ↦ by rw [hx, ENNReal.ofReal_zero])
          _ = 0 := lintegral_zero
      _ = 0 := lintegral_zero
  simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0))

end OTSelector.Probability
