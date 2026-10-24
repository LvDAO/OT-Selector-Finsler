import OTSelector.Reconstruction.FinslerOriginalFrozenCoreLLN

/-!
# Random-kernel pair law (U-statistic form)

The plan-free tile mean is an expectation of a *pair sum* whose kernel depends on
the outcome not only through the iid pairs but also through a random probe /
random matrix kernel.  The repo iid pair law
`OTSelector.Probability.integral_pairTest_eq` handles a fixed kernel.  This module
proves the clean structural extension needed by the plan-free lane: when the random
kernel factors as (*outcome-dependent scalar/amplitude*) × (*fixed pair kernel*) and
the amplitude is independent of the pair configuration (product space), the pair
sum law survives with the amplitude's expectation factored out:

  `∫ (ω₀, s), f ω₀ * ∑ i ∑ j, Φ (X i s, Y j s) ∂(μ₀.prod P)
      = (∫ f) * (n * m * ∫ Φ).`

The proof is Fubini for the product of two bounded measurable factors
(`MeasureTheory.integral_prod_mul`, unconditional) composed with the fixed-kernel iid
pair law.

Two consequences, both proved here:

* `integral_randomKernel_pairSum_centered`: a *centered* random amplitude
  (`∫ f = 0`) kills the random-kernel pair sum exactly: the probe bias cancels;
* `integral_randomKernel_pairSum_normalized`: the normalized pair mean is
  `(∫ f) * ∫ Φ`, i.e. the population readout times the mean amplitude — the form
  needed to identify the normalized plan-free tile average with the population tile
  value.

This is the exact U-statistic law for *independent* random kernels.  The remaining
gap for the frozen tile matrix is that its kernel also depends on the outcome
through the *mask* `edgeEvent`, which couples the amplitude to the pairs; that
coupling is not covered here.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
  {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Random-kernel pair law (factorizable kernel).**  For a bounded measurable
amplitude `f` on an independent probability space `(Ω₀, μ₀)` and a fixed bounded
measurable pair kernel `Φ`, the expectation of the amplitude-weighted pair sum is
the amplitude mean times the pair count times the population integral. -/
theorem integral_randomKernel_pairSum
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {n m : ℕ} (X : Fin n → Ω → M) (Y : Fin m → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (Φ : M × M' → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hΦb : ∀ p, |Φ p| ≤ B)
    (f : Ω₀ → ℝ) :
    ∫ z : Ω₀ × Ω,
        f z.1 * (∑ i, ∑ j, Φ (X i z.2, Y j z.2)) ∂(μ₀.prod P) =
      (∫ x, f x ∂μ₀) * ((n : ℝ) * (m : ℝ) * ∫ p, Φ p ∂(μ.prod ν)) := by
  rw [integral_prod_mul f (fun s ↦ ∑ i, ∑ j, Φ (X i s, Y j s))]
  rw [integral_pairTest_eq X Y hX hY hXlaw hYlaw hpair Φ hΦ hΦb]

/-- **Centered random amplitudes kill the random-kernel pair sum exactly.**  If the
amplitude has zero mean, the expectation of the random-kernel pair sum vanishes:
the probe bias cancels against the population pair law. -/
theorem integral_randomKernel_pairSum_centered
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {n m : ℕ} (X : Fin n → Ω → M) (Y : Fin m → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (Φ : M × M' → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hΦb : ∀ p, |Φ p| ≤ B)
    (f : Ω₀ → ℝ) (hf : ∫ x, f x ∂μ₀ = 0) :
    ∫ z : Ω₀ × Ω,
        f z.1 * (∑ i, ∑ j, Φ (X i z.2, Y j z.2)) ∂(μ₀.prod P) = 0 := by
  rw [integral_randomKernel_pairSum X Y hX hY hXlaw hYlaw hpair Φ hΦ hΦb f, hf,
    zero_mul]

/-- **Normalized random-kernel pair mean.**  Dividing the pair sum by the number of
pairs gives the amplitude mean times the population pair integral: the exact
U-statistic normalization used to identify the plan-free tile average with the
population tile value. -/
theorem integral_randomKernel_pairSum_normalized
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (X : Fin n → Ω → M) (Y : Fin m → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (Φ : M × M' → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hΦb : ∀ p, |Φ p| ≤ B)
    (f : Ω₀ → ℝ) :
    ∫ z : Ω₀ × Ω,
        f z.1 * ((∑ i, ∑ j, Φ (X i z.2, Y j z.2)) / ((n : ℝ) * (m : ℝ))) ∂(μ₀.prod P) =
      (∫ x, f x ∂μ₀) * (∫ p, Φ p ∂(μ.prod ν)) := by
  have hnm : (n : ℝ) * (m : ℝ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn) (by exact_mod_cast hm)
  have hpoint : ∀ z : Ω₀ × Ω,
      f z.1 * ((∑ i, ∑ j, Φ (X i z.2, Y j z.2)) / ((n : ℝ) * (m : ℝ))) =
        (f z.1 * (∑ i, ∑ j, Φ (X i z.2, Y j z.2))) / ((n : ℝ) * (m : ℝ)) := by
    intro z
    ring
  simp only [hpoint]
  rw [integral_div, integral_randomKernel_pairSum X Y hX hY hXlaw hYlaw hpair Φ hΦ hΦb f]
  field_simp

end OTSelector.Probability
