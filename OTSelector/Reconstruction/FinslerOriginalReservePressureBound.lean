import OTSelector.Reconstruction.FinslerOriginalMinimizerPalm
import OTSelector.Reconstruction.FinslerOriginalReserveLiftingMeasurable

/-!
# Pressure reserve at the dilated tilt

This module closes the remaining input of FinslerOriginalMinimizerPalm: the
pressure reserve bound

  p (t lam^(2/q)) - I_w (t lam^(2/q)) <= C' * rho^(1 - 2/q),

uniformly in rho, where lam = 1 - rho.

The key observation is that the reserve comparison of
FinslerOriginalReserveLiftingMeasurable gives a STRONGER statement than the
required one: from the finite-value comparison with explicit reserve cost the
normalized limit gives

  p s <= I_w s   for every tilt s
  (legalPressureLimit_le_weightedInf_of_reserveComparison),

i.e. the pressure reserve is ZERO, not merely C' * rho^(1 - 2/q).  Applied at
the dilated tilt s = t lam^(2/q) this gives the required bound with C' = 0 and
in particular the C' * rho^(1 - 2/q) form for every C' >= 0.

Two consequences are proved:

1. **Exact minimizer identification** (canonicalCandidate_minimizerGap_eq_zero):
   the canonical candidate's energy bound M.value s <= p s and the infimum
   bound I_w s <= M.value s sandwich the value, so M.value s = I_w s for every
   tilt s.  The canonical candidate is an EXACT minimizer of the weighted
   stationary value, with no compactness or minimizer-existence theorem needed.

2. **Stationarity from the finite-value comparison**
   (stationarity_of_finiteValueComparison): the population pressure integrated
   against the candidate's Palm law is at most I_w at every tilt.  Together
   with the Palm lane (stationarity implies the finite-value comparison) this
   shows that, conditional on the Palm identification and the boundary data,
   (Stationarity) is EQUIVALENT to the finite-value comparison.  Hence the
   palm lane needs no separate stationarity input beyond the finite-value
   comparison itself, and the minimizer gap is zero rather than absorbable.

## Remaining sub-gap

Only the finite-value comparison FiniteValueComparisonWithReserveCost itself
remains, exactly as before; the stationarity hypothesis, the pressure reserve
and the minimizer gap are all equivalent to it and introduce no further
analytic content.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X]

/-- **The pressure reserve is zero under the finite-value comparison.**  The
normalized reserve comparison gives p <= I_w at every tilt. -/
theorem pressureReserve_zero_of_finiteValueComparison
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {p : ℝ → ℝ} {C G : ℝ} (hq : 4 < q)
    (hcont : ∀ t : ℝ, ContinuousAt (fun s : ℝ => legalWeightedInf q α β kin g s) t)
    (hcompare : FiniteValueComparisonWithReserveCost q α β kin g p C G) (t : ℝ) :
    p t ≤ legalWeightedInf q α β kin g t :=
  legalPressureLimit_le_weightedInf_of_reserveComparison hq hcont hcompare t

/-- **Pressure reserve at the dilated tilt.**  For retained density lam = 1 - rho
the pressure reserve at the tilt t lam^(2/q) is at most C' rho^(1 - 2/q) for
every C' >= 0; in fact it is at most zero. -/
theorem pressureReserve_at_dilatedTilt_le
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {p : ℝ → ℝ} {C G : ℝ} (hq : 4 < q)
    (hcont : ∀ t : ℝ, ContinuousAt (fun s : ℝ => legalWeightedInf q α β kin g s) t)
    (hcompare : FiniteValueComparisonWithReserveCost q α β kin g p C G)
    {C' : ℝ} (hC'0 : 0 ≤ C') {t rho : ℝ} (hrho0 : 0 < rho) :
    p (t * (1 - rho) ^ (2 / (q : ℝ))) -
        legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) ≤
      C' * rho ^ (1 - 2 / (q : ℝ)) := by
  have hzero := pressureReserve_zero_of_finiteValueComparison hq hcont hcompare
    (t * (1 - rho) ^ (2 / (q : ℝ)))
  have hres : 0 ≤ C' * rho ^ (1 - 2 / (q : ℝ)) :=
    mul_nonneg hC'0 (Real.rpow_nonneg hrho0.le _)
  linarith

/-- **Exact minimizer identification.**  Under the finite-value comparison the
canonical candidate's value equals the weighted stationary value at every tilt:
the energy bound and the infimum bound sandwich it.  No minimizer-existence
theorem is needed. -/
theorem canonicalCandidate_minimizerGap_eq_zero
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {p : ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hbdd : ∀ u : ℝ, BddBelow (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value u)))
    (henergy : ∀ u : ℝ, M.value u ≤ p u)
    (hres : ∀ u : ℝ, p u ≤ legalWeightedInf q α β kin g u) (u : ℝ) :
    M.value u = legalWeightedInf q α β kin g u := by
  have h1 := henergy u
  have h2 := hres u
  have h3 := legalWeightedInf_le_value u (hbdd u) M
  linarith

/-- **Stationarity from the finite-value comparison.**  The population pressure
integrated against the canonical candidate's Palm law is at most the weighted
stationary value at every tilt. -/
theorem stationarity_of_finiteValueComparison
    {q : ℕ} (hq : 4 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {p : ℝ → ℝ} {C G : ℝ}
    (hcont : ∀ t : ℝ, ContinuousAt (fun s : ℝ => legalWeightedInf q α β kin g s) t)
    (hcompare : FiniteValueComparisonWithReserveCost q α β kin g p C G)
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (u : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (hIint : Integrable (fun m => I m u) (legalMarkedJointPalm q M.law))
    (hpt : ∀ᵐ m ∂(legalMarkedJointPalm q M.law),
      I m u ≤ kin m.1.1 m.1.2 m.2 + u * g m.1.1 m.1.2)
    (henergy : M.value u ≤ p u) :
    (∫ m, I m u ∂legalMarkedJointPalm q M.law) ≤
      legalWeightedInf q α β kin g u := by
  have hdom := domination_of_pointwise M u I hIint hpt
  have hres := pressureReserve_zero_of_finiteValueComparison hq hcont hcompare u
  linarith

end OTSelector.Reconstruction
