import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.FinslerOriginalReserveStationarity

/-!
# Universal domination of the stationary value functional

This module attempts the last analytic statement of
FinslerOriginalReserveStationarity: for every legal weighted stationary Poisson
matching Q, the dilated population pressure is at most Q.value(t lam^(2/q)),
together with nonemptiness and bounded-below-ness of the value range.

The investigation:

* Q.value is NOT an infimum over plans.  It is the Palm integral of the
  kinetic-plus-probe cost: Q.value t = int (kin m.1.1 m.1.2 m.2 + t * g m.1.1
  m.1.2) d(legalMarkedJointPalm q Q.law) (value_eq_integral_markedCost).
* Therefore the pointwise route is available PER CANDIDATE: if the local
  pressure function I is a pointwise lower bound of the cost integrand
  kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 almost everywhere for the Palm law of
  Q, then monotonicity of the integral gives
  int I d(Palm Q) <= Q.value t (domination_of_pointwise), and universally over
  candidates (universal_domination_of_pointwise).
* The order algebra then converts any FIXED-measure universal domination into
  the stationarity inequality (stationarity_of_universal_domination, composing
  FinslerOriginalReserveStationarity).

1. **Value as a Palm cost integral** (value_eq_integral_markedCost).

2. **Per-candidate domination from the pointwise comparison**
   (domination_of_pointwise).

3. **Universal domination over candidates** (universal_domination_of_pointwise).

4. **Stationarity from fixed-measure universal domination**
   (stationarity_of_universal_domination).

5. **Stationarity from the pointwise comparison plus a common Palm**
   (stationarity_of_pointwise_commonPalm): if every candidate has the same Palm
   law mu as the population measure, the pointwise comparison gives
   (Stationarity) outright.

## Remaining sub-gap

The pointwise comparison is per candidate Palm.  The stationarity inequality
needs a FIXED population measure mu with int I dmu <= Q.value t for EVERY
candidate Q, so the two routes differ exactly in the Palm law: what is still
missing is either
  (i) the identification mu = legalMarkedJointPalm q Q.law for all competitor
      candidates (all candidates share the population Palm law), or
  (ii) a domination theorem int I dmu <= int c d(Palm Q) comparing the fixed
      population integral with each candidate's Palm cost integral.
Everything else - the value rewriting, the pointwise-to-integral monotonicity,
the universal quantifier over candidates and the order algebra with I_w - is
proved here.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X]

/-- **The signed value is the Palm integral of the marked cost.**  This is the
definitional identity showing that Q.value is not an infimum over plans but the
Palm expectation of the kinetic-plus-probe cost. -/
theorem value_eq_integral_markedCost
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) :
    M.value t =
      ∫ m, (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
        ∂legalMarkedJointPalm q M.law := by
  unfold LegalWeightedStationaryPoissonMatching.value
  rw [integral_add M.kinetic_integrable (M.probe_integrable.const_mul t),
    integral_const_mul]

/-- **Per-candidate domination from the pointwise comparison.**  If the local
pressure function I is a pointwise lower bound of the marked cost almost
everywhere for the Palm law of Q, then its Palm integral is at most Q.value t. -/
theorem domination_of_pointwise
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (hIint : Integrable (fun m => I m t) (legalMarkedJointPalm q M.law))
    (hpt : ∀ᵐ m ∂(legalMarkedJointPalm q M.law),
      I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) :
    (∫ m, I m t ∂legalMarkedJointPalm q M.law) ≤ M.value t := by
  rw [value_eq_integral_markedCost]
  exact integral_mono_ae hIint
    (M.kinetic_integrable.add (M.probe_integrable.const_mul t)) hpt

/-- **Universal domination over candidates.**  The pointwise comparison for every
candidate's own Palm law gives the domination of the Palm-integrated pressure by
every candidate value. -/
theorem universal_domination_of_pointwise
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (hIint : ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      Integrable (fun m => I m t) (legalMarkedJointPalm q Q.law))
    (hpt : ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      ∀ᵐ m ∂(legalMarkedJointPalm q Q.law),
        I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) :
    ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      (∫ m, I m t ∂legalMarkedJointPalm q Q.law) ≤ Q.value t :=
  fun Q => domination_of_pointwise Q t I (hIint Q) (hpt Q)

/-- **Stationarity from fixed-measure universal domination.**  The order algebra
of FinslerOriginalReserveStationarity converts the domination of the fixed
population pressure by every candidate value into the stationarity inequality. -/
theorem stationarity_of_universal_domination
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (μ : Measure X) (I : X → ℝ → ℝ) (t : ℝ)
    (hne : (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)).Nonempty)
    (hdom : ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      (∫ x, I x t ∂μ) ≤ Q.value t) :
    (∫ x, I x t ∂μ) ≤ legalWeightedInf q α β kin g t :=
  stationarity_of_all_values μ I t hne hdom

/-- **Stationarity from the pointwise comparison plus a common Palm.**  If every
candidate shares the population Palm law mu, then the pointwise comparison gives
(Stationarity) by monotonicity of the integral against the single measure mu. -/
theorem stationarity_of_pointwise_commonPalm
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (hne : (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)).Nonempty)
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hpalm : ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      legalMarkedJointPalm q Q.law = μ)
    (hIint : Integrable (fun m => I m t) μ)
    (hpt : ∀ᵐ m ∂μ, I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) :
    (∫ m, I m t ∂μ) ≤ legalWeightedInf q α β kin g t := by
  refine stationarity_of_universal_domination μ I t hne (fun Q => ?_)
  rw [value_eq_integral_markedCost, hpalm Q]
  have hcost : Integrable
      (fun m => kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) μ := by
    rw [← hpalm Q]
    exact Q.kinetic_integrable.add (Q.probe_integrable.const_mul t)
  exact integral_mono_ae hIint hcost hpt

end OTSelector.Reconstruction
