import OTSelector.Reconstruction.FinslerOriginalReserveCompletionStationary

/-!
# Stationarity: the dilated retained core as a near-minimizer

This module isolates the (Stationarity) hypothesis of
FinslerOriginalReservePalmIdentification in its exact form and proves it from
the universal domination of the population pressure.

The weighted stationary value

  I_w(t) = sInf (range (fun Q : LegalWeightedStationaryPoissonMatching q alpha beta kin g => Q.value t))

is the greatest lower bound of the values of all legal weighted stationary
matchings.  Hence a population pressure B(t) = int I(x,t) dmu is at most I_w(t)
if and only if it is at most the value of EVERY legal weighted stationary
matching: the dilated retained core is a near-minimizer precisely when its
pressure is a universal lower bound for the stationary value functional.  This
is the stationarity statement; it reduces the analytic input to the pointwise
domination of the value functional.

1. **The infimum is below every value** (legalWeightedInf_le_value).

2. **Stationarity iff universal domination** (stationarity_iff_forall_le_values):
   the exact reformulation of (Stationarity).

3. **Stationarity from universal domination** (stationarity_of_all_values).

4. **Stationarity from a minimizer identity** (stationarity_of_minimizer): if the
   dilated retained-core pressure is the value of a legal weighted stationary
   matching which nearly realizes the infimum, then (Stationarity) holds.

5. **The dilated-tilt form** (stationarity_at_dilatedTilt): the exact statement
   used by FinslerOriginalReservePalmIdentification, at tilt t (1-rho)^(2/q)
   with retained density lam = 1-rho.

## Remaining sub-gap

The only remaining input is the universal domination
forall Q, int I(x, t lam^(2/q)) dmu <= Q.value(t lam^(2/q)), i.e. that the local
legal pressure function of the retained core is dominated, after Palm
integration, by the value of every legal weighted stationary matching at the
dilated tilt.  This is the stationarity of the retained core: no statement about
the infimum/order algebra is missing here.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X]

/-- **The weighted stationary infimum is below every value.** -/
theorem legalWeightedInf_le_value
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} (t : ℝ)
    (hbdd : BddBelow (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)))
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    legalWeightedInf q α β kin g t ≤ Q.value t := by
  unfold legalWeightedInf
  exact csInf_le hbdd ⟨Q, rfl⟩

/-- **Stationarity iff universal domination.**  The dilated retained-core
pressure is at most the weighted stationary value exactly when it is at most the
value of every legal weighted stationary matching. -/
theorem stationarity_iff_forall_le_values
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (μ : Measure X) (I : X → ℝ → ℝ) (t : ℝ)
    (hne : (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)).Nonempty)
    (hbdd : BddBelow (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t))) :
    ((∫ x, I x t ∂μ) ≤ legalWeightedInf q α β kin g t) ↔
      (∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
        (∫ x, I x t ∂μ) ≤ Q.value t) := by
  constructor
  · intro h Q
    exact le_trans h (legalWeightedInf_le_value t hbdd Q)
  · intro h
    unfold legalWeightedInf
    exact le_csInf hne (fun y hy => by
      obtain ⟨Q, rfl⟩ := hy
      exact h Q)

/-- **Stationarity from universal domination.** -/
theorem stationarity_of_all_values
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (μ : Measure X) (I : X → ℝ → ℝ) (t : ℝ)
    (hne : (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)).Nonempty)
    (hle : ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      (∫ x, I x t ∂μ) ≤ Q.value t) :
    (∫ x, I x t ∂μ) ≤ legalWeightedInf q α β kin g t := by
  unfold legalWeightedInf
  exact le_csInf hne (fun y hy => by
    obtain ⟨Q, rfl⟩ := hy
    exact hle Q)

/-- **Stationarity from a minimizer identity.**  If the dilated retained-core
pressure is the value of a legal weighted stationary matching which nearly
realizes the infimum, then the stationarity inequality holds. -/
theorem stationarity_of_minimizer
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (μ : Measure X) (I : X → ℝ → ℝ) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hval : (∫ x, I x t ∂μ) = Q.value t)
    (hmin : Q.value t ≤ legalWeightedInf q α β kin g t) :
    (∫ x, I x t ∂μ) ≤ legalWeightedInf q α β kin g t := by
  rw [hval]
  exact hmin

/-- **Stationarity at the dilated tilt.**  The exact form used by the Palm
identification: for retained density lam = 1 - rho, the dilated population
pressure at tilt t (1-rho)^(2/q) is at most the weighted stationary value at
that tilt, provided it is dominated by the value of every legal weighted
stationary matching. -/
theorem stationarity_at_dilatedTilt
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (μ : Measure X) (I : X → ℝ → ℝ) (t rho : ℝ)
    (hne : (Set.range (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g =>
      Q.value (t * (1 - rho) ^ (2 / (q : ℝ))))).Nonempty)
    (hle : ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      (∫ x, I x (t * (1 - rho) ^ (2 / (q : ℝ))) ∂μ) ≤
        Q.value (t * (1 - rho) ^ (2 / (q : ℝ)))) :
    (∫ x, I x (t * (1 - rho) ^ (2 / (q : ℝ))) ∂μ) ≤
      legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) :=
  stationarity_of_all_values μ I (t * (1 - rho) ^ (2 / (q : ℝ))) hne hle

end OTSelector.Reconstruction
