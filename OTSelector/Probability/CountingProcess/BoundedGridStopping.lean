import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Martingale.OptionalSampling
import OTSelector.Probability.CountingProcess.Closure
import OTSelector.Probability.CountingProcess.Core

/-!
# Probability.CountingProcess.BoundedGridStopping

**Conditions:** The bounded-predictable compensated transform has integrable accumulated intensity; stopping times are bounded by a deterministic endpoint and have finite range.

**Objects:** Optional sampling at one stopping time or between two ordered stopping times.

**Proof detail:** Apply bounded-predictable martingale closure, convert finite stopping ranges to countable ranges and specialize the existing optional-sampling conditional-expectation theorem.

**Sources:** [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=243), Section 4.4, Theorem 4.4.1, p. 235, and Exercise 4.4.4, p. 239; [Richard D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124 (1980)](https://ir.cwi.nl/pub/11499/11499D.pdf#page=16), Section 2.2, pp. 10–11, especially equation (2.2.1), p. 11 (PDF page 16); Section 2.3, equation (2.3.1), p. 12.

Source relation (adapter): Durrett gives the bounded finite-grid sampling principle; the exact sigma-finite-filtration version is the Mathlib theorem used here. The local wrappers retain the extra integrable-intensity assumption required by bounded-predictable closure.
-/


/-!
# Optional sampling for bounded predictable transforms on finite stopping grids

This file extends the finite-grid optional-sampling wrappers of `GridStopping` from bounded
finite-range predictable transforms to bounded predictable transforms.  The closure theorem needs
the accumulated intensity to be integrable at every deterministic endpoint, so that hypothesis is
kept explicit in both wrappers below.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Optional sampling of a compensated bounded-predictable transform at one finite-valued
stopping time. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_boundedPredictable_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedPredictable ℱ H)
    (hAint : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) τ =ᵐ[μ]
      μ[compensatedIntegral N Λ H T | hτ.measurableSpace] :=
  (hΛ.martingale_of_boundedPredictable hH hAint)
    |>.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      hτ hτ_le hτ_range.countable

/-- Optional sampling between two finite-valued stopping times for a compensated
bounded-predictable transform. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_boundedPredictable_finiteRange_pair
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedPredictable ℱ H)
    (hAint : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) σ =ᵐ[μ]
      μ[stoppedValue (compensatedIntegral N Λ H) τ | hσ.measurableSpace] :=
  (hΛ.martingale_of_boundedPredictable hH hAint)
    |>.stoppedValue_ae_eq_condExp_of_le_of_countable_range
      hτ hσ hστ hτ_le hτ_range.countable hσ_range.countable

end OTSelector.CountingProcess
