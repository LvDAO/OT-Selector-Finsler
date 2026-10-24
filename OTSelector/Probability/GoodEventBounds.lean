import Mathlib.MeasureTheory.Integral.Bochner.Set
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.GoodEventBounds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.GoodEventBounds`; the selected original proof blocks follow. -/
section

/-!
# Probability.GoodEventBounds

## Lemma skeleton

* **Conditions:** A sequence of probability laws, good-event lower or integrable upper bounds and bad-event masses tending to zero.
* **Objects:** Probability lower transfers and eventual expectation upper bounds.
* **Proof detail:** Contain the bad-value event in the good-event complement; for expectations split into the good/bad restrictions and pay the global bound times bad mass.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=59): Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).

Source relation (composition): Elementary good-event indicator/integral comparison; no convergence of the random variables is inferred.
-/

/-!
# From good-event pathwise bounds to probability and expectation bounds

The paper's lower and upper pressure estimates are proved on a sequence of good
sample events whose probabilities tend to one.  These two elementary transfers
turn such pathwise bounds into the probability lower bound and the expectation
upper bound consumed by the pressure squeeze.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]

/-- **Good-event probability lower bound.**  If on the good events the values
are at least `L - eps`, and the probability of the bad events tends to zero,
then the probability that a value drops below `L - eps` tends to zero. -/
theorem tendsto_measureReal_lt_sub_of_good_event
    (V : ∀ n, Ω n → ℝ) (G : ∀ n, Set (Ω n)) {L eps : ℝ}
    (hgood : ∀ n, ∀ ω ∈ G n, L - eps ≤ V n ω)
    (hbad : Tendsto (fun n => (P n).real ((G n)ᶜ)) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).real {ω | V n ω < L - eps}) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => measureReal_nonneg)
    (fun n => measureReal_mono ?_) hbad
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [Set.mem_compl_iff]
  intro hGω
  exact absurd hω (not_lt.mpr (hgood n ω hGω))

/-- **Good-event expectation upper bound.**  If the values are globally bounded
above by `M` and are at most `L + eps` on good events whose complement has
vanishing measure, then the expectations are eventually at most `L + eps + eps'`. -/
theorem integral_le_of_good_event
    (V : ∀ n, Ω n → ℝ) (G : ∀ n, Set (Ω n))
    (hGmeas : ∀ n, MeasurableSet (G n))
    (hVint : ∀ n, Integrable (V n) (P n))
    {M L eps : ℝ}
    (hglobal : ∀ n ω, V n ω ≤ M)
    (hgood : ∀ n, ∀ ω ∈ G n, V n ω ≤ L + eps)
    (hbad : Tendsto (fun n => (P n).real ((G n)ᶜ)) atTop (𝓝 0))
    {eps' : ℝ} (heps' : 0 < eps') :
    ∀ᶠ n in atTop, ∫ ω, V n ω ∂P n ≤ L + eps + eps' := by
  set c : ℝ := M - (L + eps) with hc
  have hbadzero : Tendsto (fun n => c * (P n).real ((G n)ᶜ)) atTop (𝓝 0) := by
    simpa using hbad.const_mul c
  have hev : ∀ᶠ n in atTop, c * (P n).real ((G n)ᶜ) ≤ eps' := by
    exact (hbadzero.eventually (Iio_mem_nhds heps')).mono fun n h => le_of_lt h
  filter_upwards [hev] with n hn
  -- Pointwise bound by a constant plus an indicator of the bad event.
  have hpt : ∀ᵐ ω ∂P n, V n ω ≤ (L + eps) +
      c * (Set.indicator ((G n)ᶜ) (fun _ => (1 : ℝ)) ω) := by
    filter_upwards with ω
    by_cases hω : ω ∈ G n
    · rw [Set.indicator_of_notMem (by simpa using hω), mul_zero, add_zero]
      exact hgood n ω hω
    · rw [Set.indicator_of_mem (by simpa using hω)]
      have : L + eps + c * 1 = M := by rw [hc]; ring
      rw [this]
      exact hglobal n ω
  have hRhsInt : Integrable (fun ω => (L + eps) +
      c * (Set.indicator ((G n)ᶜ) (fun _ => (1 : ℝ)) ω)) (P n) :=
    (integrable_const (L + eps)).add
      ((((integrable_const (1 : ℝ)).indicator ((hGmeas n).compl))).const_mul c)
  have hmono := integral_mono_ae (hVint n) hRhsInt hpt
  have hval : (∫ ω, (L + eps) +
        c * (Set.indicator ((G n)ᶜ) (fun _ => (1 : ℝ)) ω) ∂P n) =
      (L + eps) + c * (P n).real ((G n)ᶜ) := by
    rw [integral_add (integrable_const _)
      ((((integrable_const (1 : ℝ)).indicator ((hGmeas n).compl))).const_mul c),
      integral_const, integral_const_mul, integral_indicator ((hGmeas n).compl)]
    simp [measureReal_def]
  rw [hval] at hmono
  linarith

end OTSelector.Probability

end
end
