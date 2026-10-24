import OTSelector.Reconstruction.FinslerOriginalReserveCostComparison
import OTSelector.Probability.MarkedDePoissonization
import OTSelector.Probability.MarkedPressureKernelStability

/-!
# Count concentration and box normalization for the reserve cost comparison

This module closes the count-concentration and normalization half of gap (i) of
FinslerOriginalReserveCostComparison.lean.

1. **Definitional count identification.**  The actual variable-count legal
   pressure integrand is the fixed-count legal value at the realized colored
   counts (legalMarkedTilted_eq_fixedValue).  Hence the legal pressure is the
   expectation of the fixed-count legal value at the realized Poisson counts.

2. **Count concentration.**  The expected absolute deviation of either Poisson
   count from the intensity r is at most sqrt r
   (integral_abs_sourceCount_deviation_le,
   integral_abs_targetCount_deviation_le), and the expected source count is
   exactly r (integral_sourceCount_eq).  Both are unchanged original Poisson
   facts; no selected matching law is involved.

3. **Box normalization of the reserve cost comparison.**  If the variable-count
   pointwise reserve comparison
   legalMarkedTilted <= core cost + (source count) * Bedge
   holds almost surely, then integrating over the marked-cloud law and using the
   exact count mean gives
   legalMarkedPressure <= E[core tilted cost] + r * Bedge.
   This is the normalized (per volume r = L^q) form needed for the box limit; the
   count factor is exactly the intensity, not a count tail.

## Remaining gap

The sharp reserve cost: the count-majorant bound above produces the budget
r * Bedge = r^(1+2/q)(C q) + r |t| G, whereas the paper's reserve construction
produces the much smaller C rho^(1-2/q) L^q from the averaged transport of the
residual ports (not from the number of added edges times the maximum edge cost).
Obtaining the sharp budget requires the Neumann/transport estimate in place of
the crude per-edge majorant; with it, the box limit and
FiniteValueComparisonWithReserveCost follow as in
FinslerOriginalReserveLiftingMeasurable.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {α : Measure A} [IsProbabilityMeasure α] {β : Measure B} [IsProbabilityMeasure β]
  {r : ℝ≥0} {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t : ℝ}

/-- **Definitional count identification.**  The actual variable-count legal
tilted value is the fixed-count legal value computed at the realized Poisson
counts. -/
theorem legalMarkedTilted_eq_fixedValue
    (sourceClock : A → ℝ) (targetClock : B → ℝ) (omega : TwoMarkedCloudSpace q A B) :
    legalMarkedTilted q sourceClock targetClock r kin g t omega =
      legalMarkedFixedValue q (mSourceCount omega) (mTargetCount omega)
        sourceClock targetClock (r : ℝ) kin g t omega := rfl

/-- The expected absolute deviation of the source Poisson count from the
intensity is at most the square root of the intensity. -/
theorem integral_abs_sourceCount_deviation_le :
    (∫ omega : TwoMarkedCloudSpace q A B,
        |((mSourceCount omega : ℕ) : ℝ) - (r : ℝ)|
        ∂(twoMarkedCloudLaw (q := q) A B α β r)) ≤ Real.sqrt (r : ℝ) :=
  integral_abs_mSourceCount_sub_le (q := q) α β r

/-- The expected absolute deviation of the target Poisson count from the
intensity is at most the square root of the intensity. -/
theorem integral_abs_targetCount_deviation_le :
    (∫ omega : TwoMarkedCloudSpace q A B,
        |((mTargetCount omega : ℕ) : ℝ) - (r : ℝ)|
        ∂(twoMarkedCloudLaw (q := q) A B α β r)) ≤ Real.sqrt (r : ℝ) :=
  integral_abs_mTargetCount_sub_le (q := q) α β r

/-- The expected source count is exactly the intensity r: the count factor in
the reserve comparison normalizes exactly by the volume. -/
theorem integral_sourceCount_eq :
    (∫ omega : TwoMarkedCloudSpace q A B, ((mSourceCount omega : ℕ) : ℝ)
      ∂(twoMarkedCloudLaw (q := q) A B α β r)) = (r : ℝ) :=
  integral_mSourceCount (q := q) α β r

/-- **Box normalization of the reserve cost comparison.**  If the variable-count
pointwise reserve comparison holds almost surely with the count factor, then the
legal pressure is at most the expected retained core tilted cost plus the exact
volume r times the edge bound. -/
theorem legalMarkedPressure_le_integral_core_add_reserve
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (coreCost : TwoMarkedCloudSpace q A B → ℝ)
    {Bedge : ℝ}
    (hcore : Integrable coreCost (twoMarkedCloudLaw (q := q) A B α β r))
    (hpressure : Integrable (fun omega =>
      legalMarkedTilted q sourceClock targetClock r kin g t omega)
      (twoMarkedCloudLaw (q := q) A B α β r))
    (hpointwise : ∀ᵐ omega ∂(twoMarkedCloudLaw (q := q) A B α β r),
      legalMarkedTilted q sourceClock targetClock r kin g t omega ≤
        coreCost omega + ((mSourceCount omega : ℕ) : ℝ) * Bedge) :
    legalMarkedPressure q sourceClock targetClock α β r kin g t ≤
      (∫ omega, coreCost omega ∂(twoMarkedCloudLaw (q := q) A B α β r)) +
        (r : ℝ) * Bedge := by
  have hcount_int : Integrable (fun omega : TwoMarkedCloudSpace q A B =>
      ((mSourceCount omega : ℕ) : ℝ) * Bedge)
      (twoMarkedCloudLaw (q := q) A B α β r) :=
    (integrable_mSourceCount (q := q) α β r).mul_const Bedge
  have hmono : legalMarkedPressure q sourceClock targetClock α β r kin g t ≤
      ∫ omega, coreCost omega + ((mSourceCount omega : ℕ) : ℝ) * Bedge
        ∂(twoMarkedCloudLaw (q := q) A B α β r) :=
    integral_mono_ae hpressure (hcore.add hcount_int) hpointwise
  rw [integral_add hcore hcount_int, integral_mul_const,
    integral_mSourceCount] at hmono
  exact hmono

end OTSelector.Reconstruction
