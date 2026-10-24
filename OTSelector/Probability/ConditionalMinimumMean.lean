import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Linarith

/-!
# Conditional Minimum Mean

Conditions: Finite-measure conditional integral identities or probability conditional means bounded below by p, with global mean p; the zero theorem permits a complete normed-vector target.

Objects: All conditioning-event integrals at the minimum, conditional mean/expectation equal p, and conditional expectation zero from all test integrals zero.

Proof detail: Compare each conditioning event with its complement to force equality of its integral. Use the defining conditional integral identities and uniqueness; the vector zero case uses the same test-integral criterion.

Relation to primary sources: Locally derived minimum/uniqueness consequences of conditional expectation, not an ergodic decomposition theorem.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 4.1, definition and uniqueness, pp. 205–207; Example 4.1.5, p. 208; Theorem 4.1.9, pp. 210–211. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213
-/
/-! A global minimum remains minimal under feasible event conditioning. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace OTSelector.Probability

/-- The unnormalized cost of a positive-probability event is its probability
multiplied by the cost under its conditional law. -/
theorem measureReal_mul_integral_cond
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → ℝ) (A : Set Ω) (hA : P A ≠ 0) :
    P.real A * (∫ x, f x ∂P[|A]) = ∫ x in A, f x ∂P := by
  have hreal : P.real A ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hA, measure_ne_top P A⟩
  change (P A).toReal ≠ 0 at hreal
  simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← mul_assoc, Measure.real_def, mul_inv_cancel₀ hreal, one_mul]

/-- A conditional lower bound on every event in a sub-sigma algebra, together
with equality of the total mean, fixes the mean on every such event. -/
theorem setIntegral_eq_minimum_mul_measureReal
    {Ω : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω]
    (P : @Measure Ω m₀) [IsProbabilityMeasure P] (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : Integrable f P) {p : ℝ} (hmean : ∫ x, f x ∂P = p)
    (hmin : ∀ A, MeasurableSet[m] A → P A ≠ 0 → p ≤ ∫ x, f x ∂P[|A])
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    (∫ x in A, f x ∂P) = p * P.real A := by
  have lower (B : Set Ω) (hB : MeasurableSet[m] B) :
      p * P.real B ≤ ∫ x in B, f x ∂P := by
    by_cases hz : P B = 0
    · simp [Measure.real_def, hz, setIntegral_measure_zero (f := f) hz]
    · have h := mul_le_mul_of_nonneg_left (hmin B hB hz) (measureReal_nonneg (μ := P) (s := B))
      rw [measureReal_mul_integral_cond P f B hz] at h
      simpa only [mul_comm p] using h
  have hsum := integral_add_compl (hm A hA) hf
  have hmass := measureReal_add_measureReal_compl (μ := P) (hm A hA)
  rw [hmean] at hsum
  rw [probReal_univ] at hmass
  have hleft := lower A hA
  have hright := lower Aᶜ hA.compl
  have hweighted := congrArg (fun z : ℝ ↦ p * z) hmass
  simp only [mul_add, mul_one] at hweighted
  linarith

/-- Every positive-probability event retaining the global lower bound
actually retains equality with the global minimum. -/
theorem integral_cond_eq_minimum_of_conditional_lower_bound
    {Ω : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω]
    (P : @Measure Ω m₀) [IsProbabilityMeasure P] (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : Integrable f P) {p : ℝ} (hmean : ∫ x, f x ∂P = p)
    (hmin : ∀ A, MeasurableSet[m] A → P A ≠ 0 → p ≤ ∫ x, f x ∂P[|A])
    {A : Set Ω} (hA : MeasurableSet[m] A) (hpos : P A ≠ 0) :
    (∫ x, f x ∂P[|A]) = p := by
  apply mul_left_cancel₀ (show P.real A ≠ 0 from
    ENNReal.toReal_ne_zero.mpr ⟨hpos, measure_ne_top P A⟩)
  rw [measureReal_mul_integral_cond P f A hpos,
    setIntegral_eq_minimum_mul_measureReal P hm hf hmean hmin hA, mul_comm]

/-- The conditional expectation of a globally minimizing integrable cost is
its minimum whenever conditioning on each event retains the same lower bound. -/
theorem condExp_eq_minimum_of_conditional_lower_bound
    {Ω : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω]
    (P : @Measure Ω m₀) [IsProbabilityMeasure P] (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : Integrable f P) {p : ℝ} (hmean : ∫ x, f x ∂P = p)
    (hmin : ∀ A, MeasurableSet[m] A → P A ≠ 0 → p ≤ ∫ x, f x ∂P[|A]) :
    P[f | m] =ᵐ[P] fun _ ↦ p := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := P) hm hf
  · intro A _ _
    exact integrable_const p
  · intro A hA _
    rw [setIntegral_eq_minimum_mul_measureReal P hm hf hmean hmin hA]
    simp only [setIntegral_const, smul_eq_mul, mul_comm]
  · exact stronglyMeasurable_const.aestronglyMeasurable

/-- Vanishing integrals on every event of a sub-sigma algebra give actual
conditional centering, without an ergodic decomposition. -/
theorem condExp_eq_zero_of_all_setIntegral_eq_zero
    {Ω V : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : @Measure Ω m₀) [IsFiniteMeasure P] (hm : m ≤ m₀)
    {f : Ω → V} (hf : Integrable f P)
    (hzero : ∀ A, MeasurableSet[m] A → ∫ x in A, f x ∂P = 0) :
    P[f | m] =ᵐ[P] fun _ ↦ 0 := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := P) hm hf
  · intro A _ _
    exact integrable_zero _ _ _
  · intro A hA _
    simp only [hzero A hA, integral_zero]
  · exact stronglyMeasurable_zero.aestronglyMeasurable

end OTSelector.Probability
