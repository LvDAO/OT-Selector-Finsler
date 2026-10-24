import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.Field

/-!
# Expectation Convergence From Bounds

Conditions: Integrable V_n on possibly changing probability spaces, a common a.e. lower bound L−M, vanishing lower-deviation probabilities and eventual upper bounds on E V_n.

Objects: Convergence E V_n→L together with elementary positive/negative-part identities.

Proof detail: Bound the negative part of V_n−L by a small tolerance plus a constant times its lower-deviation indicator. Then use positive/negative-part algebra and the upper expectation premise to squeeze the mean.

Relation to primary sources: A local one-sided expectation convergence theorem. It assumes no almost-sure convergence and does not silently invoke Fatou or uniform integrability on changing sample spaces.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.4, Theorem 1.4.7, p. 23; Section 1.6, positive/negative parts p. 28 and Theorem 1.6.1, p. 29. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=31
-/
/-!
# Mean convergence from a probability lower bound and an expectation upper bound

This is the abstract form of the pressure-convergence step in the paper.  If the
random variables `V n` are uniformly bounded below, their probability of falling
below `L - ε` tends to zero, and their expectations are eventually at most
`L + ε`, then their expectations converge to `L`.  In the application `V n` is the
original normalized empirical transport value and `L` is the common pressure.

No compactness or measurability of optimizers enters: the two asymptotic bounds
are the only inputs.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Probability

/-- `max x 0 = x + max (-x) 0`. -/
private lemma max_eq_add_max_neg (x : ℝ) : max x 0 = x + max (-x) 0 := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left hx, max_eq_right (by linarith)]
    ring

/-- `|x| = max x 0 + max (-x) 0`. -/
private lemma abs_eq_max_add_max_neg (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx, max_eq_right hx, max_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (by linarith)]
    ring

/-- Pointwise comparison of the negative part with a deficit event. -/
private lemma negPart_le_deficit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {V : Ω → ℝ} (hmV : Measurable V) (hV : Integrable V P) {L M δ : ℝ}
    (_hM : 0 ≤ M) (hδ : 0 < δ)
    (hbound : ∀ᵐ ω ∂P, L - M ≤ V ω) :
    (∫ ω, max (-(V ω - L)) 0 ∂P) ≤
      (M + 1) * P.real {ω | V ω < L - δ} + δ := by
  have hE : MeasurableSet {ω | V ω < L - δ} :=
    measurableSet_lt hmV measurable_const
  have hI1 : Integrable (fun ω ↦ max (-(V ω - L)) 0) P :=
    (hV.sub (integrable_const L)).neg.pos_part
  have hpoint : ∀ᵐ ω ∂P, max (-(V ω - L)) 0 ≤
      (M + 1) * (Set.indicator {ω | V ω < L - δ} (fun _ ↦ (1 : ℝ)) ω) + δ := by
    filter_upwards [hbound] with ω hω
    by_cases hlt : V ω < L - δ
    · have hmem : ω ∈ {ω | V ω < L - δ} := hlt
      simp only [Set.indicator_of_mem hmem]
      exact max_le (by linarith) (by linarith)
    · have hmem : ω ∉ {ω | V ω < L - δ} := hlt
      rw [Set.indicator_of_notMem hmem, mul_zero, zero_add]
      exact max_le (by linarith [not_lt.mp hlt]) hδ.le
  have hI2 : Integrable (fun ω ↦ (M + 1) *
      (Set.indicator {ω | V ω < L - δ} (fun _ ↦ (1 : ℝ)) ω) + δ) P := by
    exact (((integrable_const (1 : ℝ)).indicator hE).const_mul (M + 1)).add
      (integrable_const δ)
  have hmono := integral_mono_ae hI1 hI2 hpoint
  have hright : (∫ ω, (M + 1) *
      (Set.indicator {ω | V ω < L - δ} (fun _ ↦ (1 : ℝ)) ω) + δ ∂P) =
      (M + 1) * P.real {ω | V ω < L - δ} + δ := by
    rw [integral_add (((integrable_const (1 : ℝ)).indicator hE).const_mul (M + 1))
      (integrable_const δ), integral_const_mul, integral_indicator hE,
      integral_const]
    simp [measureReal_def]
  rwa [hright] at hmono

/-- Bounded-below random variables whose probability of a deficit vanishes and whose
expectations have upper limit at most `L` have expectations converging to `L`. -/
theorem tendsto_integral_of_probability_lower_and_integral_upper
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (V : ∀ n, Ω n → ℝ) (hV : ∀ n, Measurable (V n))
    (hint : ∀ n, Integrable (V n) (P n))
    (L M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ n, ∀ᵐ ω ∂P n, L - M ≤ V n ω)
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (P n).real {ω | V n ω < L - ε}) atTop (𝓝 0))
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ ω, V n ω ∂P n ≤ L + ε) :
    Tendsto (fun n ↦ ∫ ω, V n ω ∂P n) atTop (𝓝 L) := by
  -- The negative parts relative to the limit vanish in mean.
  have hneg : Tendsto (fun n ↦ ∫ ω, max (-(V n ω - L)) 0 ∂P n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / 2 := half_pos hε
    have hlim : Tendsto (fun n ↦ (M + 1) * (P n).real {ω | V n ω < L - ε / 2})
        atTop (𝓝 0) := by
      simpa using (hprob (ε / 2) hδ).const_mul (M + 1)
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hlim.eventually (Iio_mem_nhds (half_pos hε)))
    refine ⟨N, fun n hn ↦ ?_⟩
    have hb := negPart_le_deficit (P n) (hV n) (hint n) hM hδ (hbound n)
    have hnn : 0 ≤ ∫ ω, max (-(V n ω - L)) 0 ∂P n :=
      integral_nonneg fun _ ↦ le_max_right _ _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith [hN n hn]
  -- The positive parts are controlled by the expectation upper bound.
  have hpos : Tendsto (fun n ↦ ∫ ω, max (V n ω - L) 0 ∂P n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hup := hupper (ε / 2) (half_pos hε)
    have hneg' : ∀ᶠ n in atTop, ∫ ω, max (-(V n ω - L)) 0 ∂P n < ε / 2 :=
      hneg.eventually (Iio_mem_nhds (half_pos hε))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hup.and hneg')
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨hupn, hnegn⟩ := hN n hn
    have hid : (∫ ω, max (V n ω - L) 0 ∂P n) =
        (∫ ω, V n ω ∂P n) - L + ∫ ω, max (-(V n ω - L)) 0 ∂P n := by
      have hsplit : (fun ω ↦ max (V n ω - L) 0) =
          fun ω ↦ (V n ω - L) + max (-(V n ω - L)) 0 := by
        funext ω
        exact max_eq_add_max_neg (V n ω - L)
      rw [hsplit]
      have hi1 : Integrable (fun ω ↦ V n ω - L) (P n) :=
        (hint n).sub (integrable_const L)
      have hi2 : Integrable (fun ω ↦ max (-(V n ω - L)) 0) (P n) :=
        ((hint n).sub (integrable_const L)).neg.pos_part
      rw [integral_add hi1 hi2, integral_sub (hint n) (integrable_const L),
        integral_const]
      simp
    have hnn : 0 ≤ ∫ ω, max (V n ω - L) 0 ∂P n :=
      integral_nonneg fun _ ↦ le_max_right _ _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, hid]
    linarith
  -- Combine: `|V - L| = (V - L)^+ + (L - V)^+`.
  have habs : Tendsto (fun n ↦ ∫ ω, |V n ω - L| ∂P n) atTop (𝓝 0) := by
    have heq : (fun n ↦ ∫ ω, |V n ω - L| ∂P n) =
        fun n ↦ (∫ ω, max (V n ω - L) 0 ∂P n) +
          (∫ ω, max (-(V n ω - L)) 0 ∂P n) := by
      funext n
      rw [← integral_add]
      · congr 1
        funext ω
        exact abs_eq_max_add_max_neg (V n ω - L)
      · exact ((hint n).sub (integrable_const L)).pos_part
      · exact ((hint n).sub (integrable_const L)).neg.pos_part
    rw [heq]
    simpa only [zero_add] using hpos.add hneg
  have hconv : Tendsto (fun n ↦ ∫ ω, V n ω ∂P n - L) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ habs
    filter_upwards [] with n
    have h := abs_integral_le_integral_abs (μ := P n) (f := fun ω ↦ V n ω - L)
    simpa only [Real.norm_eq_abs, integral_sub (hint n) (integrable_const L),
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
      sub_zero] using h
  simpa only [sub_add_cancel, zero_add] using hconv.add_const L

end OTSelector.Probability
