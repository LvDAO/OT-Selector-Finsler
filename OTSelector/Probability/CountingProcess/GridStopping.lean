import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Martingale.OptionalSampling
import OTSelector.Probability.CountingProcess.Core
import OTSelector.Probability.CountingProcess.Exponential

/-!
# Probability.CountingProcess.GridStopping

**Conditions:** Bounded-simple predictable transforms satisfy the intensity martingale contract; stopping times have finite range and a deterministic upper endpoint, with explicit ordering for the pair version.

**Objects:** Stopped compensated/exponential-driver values equal to terminal conditional expectations.

**Proof detail:** Construct the actual driver martingale from the given intensity contract and invoke bounded countable-range optional sampling, using finite range to discharge countability.

**Sources:** [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=243), Section 4.4, Theorem 4.4.1, p. 235, and Exercise 4.4.4, p. 239; [Richard D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124 (1980)](https://ir.cwi.nl/pub/11499/11499D.pdf#page=16), Section 2.2, pp. 10–11, especially equation (2.2.1), p. 11 (PDF page 16); Section 2.3, equation (2.3.1), p. 12.

Source relation (adapter): The finite-grid conditional identities are direct specializations of Mathlib’s optional-sampling theorem. They concern compensated exponential drivers and do not assert that the full counting exponential is a martingale.
-/


/-!
# Optional sampling on finite stopping grids

Mathlib's continuous-time optional-sampling theorem applies to bounded stopping times whose
ranges are countable.  This file specializes that theorem to the actual martingales supplied by
`HasPredictableIntensity`.  Finite stopping grids are sufficient here and make the countability
premise explicit.

These results do not assert that `countingExponential` is a martingale.  Applying them to a
product-weighted exponential driver still requires a separately proved bounded-simple
predictable left weight.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Optional sampling of a compensated bounded-simple transform at one finite-valued stopping
time. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) τ =ᵐ[μ]
      μ[compensatedIntegral N Λ H T | hτ.measurableSpace] :=
  (hΛ.martingale hH).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτ_le hτ_range.countable

/-- Optional sampling between two finite-valued stopping times for a compensated bounded-simple
transform. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_finiteRange_pair
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) σ =ᵐ[μ]
      μ[stoppedValue (compensatedIntegral N Λ H) τ | hσ.measurableSpace] :=
  (hΛ.martingale hH).stoppedValue_ae_eq_condExp_of_le_of_countable_range
    hτ hσ hστ hτ_le hτ_range.countable hσ_range.countable

/-- Finite-grid optional sampling for the unweighted exponential driver. -/
theorem HasPredictableIntensity.stoppedValue_exponentialDriver_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ θ : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hθ : IsBoundedSimplePredictable ℱ θ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (exponentialDriver N Λ θ) τ =ᵐ[μ]
      μ[exponentialDriver N Λ θ T | hτ.measurableSpace] :=
  (hΛ.exponentialDriver_martingale hθ).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτ_le hτ_range.countable

/-- Finite-grid optional sampling for a product-weighted exponential driver.  The left weight is
required to be genuinely bounded, finite-valued, and predictable. -/
theorem HasPredictableIntensity.stoppedValue_weightedExponentialDriver_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ L θ : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hL : IsBoundedSimplePredictable ℱ L)
    (hθ : IsBoundedSimplePredictable ℱ θ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (weightedExponentialDriver N Λ L θ) τ =ᵐ[μ]
      μ[weightedExponentialDriver N Λ L θ T | hτ.measurableSpace] :=
  (hΛ.weightedExponentialDriver_martingale hL hθ)
    |>.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      hτ hτ_le hτ_range.countable

end OTSelector.CountingProcess
