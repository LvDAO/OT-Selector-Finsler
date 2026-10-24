import OTSelector.Reconstruction.FinslerOriginalCommonPalm
import OTSelector.Reconstruction.FinslerOriginalReservePalmIdentification

/-!
# Minimizer gap identification and its absorption

This module closes the residual of FinslerOriginalCommonPalm: the minimizer gap
Q0.value t - I_w t of the candidate whose Palm law is the population measure.

## Minimizer existence

A minimizer of the weighted stationary value would be a candidate Q with
Q.value t = I_w t.  The repository has no compactness/existence theorem for the
weighted stationary lane (search: IsMinimizer, csInf_mem, exists_minimizer; the
only minimizer results are finite-dimensional isMinOn on compact sets), so exact
minimizer existence is NOT available.  What IS available from the definition of
the infimum is the existence of approximate minimizers: for every eps > 0 some
candidate has value below I_w t + eps (exists_value_lt_legalWeightedInf_add).
The gap of any candidate is nonnegative (minimizerGap_nonneg).

## Absorption into the reserve

The canonical finite-optimum candidate M of
FinslerOriginalReserveCompletionStationary satisfies the energy bound
M.value t <= p t (where p is the actual legal pressure limit).  Therefore its
minimizer gap is at most p t - I_w t, the pressure reserve.  We prove:

1. **Approximate minimizers exist** (exists_value_lt_legalWeightedInf_add).

2. **The minimizer gap is nonnegative** (minimizerGap_nonneg).

3. **Near-minimizer Palm route** (stationarity_add_minimizerGap_of_palm): if the
   population measure is a candidate's Palm and the candidate is within eps of
   the infimum, the population pressure is at most I_w + eps.

4. **Canonical-candidate absorption** (stationarity_of_canonicalCandidate): if
   the population measure is the canonical candidate's Palm and its energy bound
   M.value t <= p t holds together with a pressure reserve p t <= I_w t + R,
   then the population pressure is at most I_w t + R.  The minimizer gap is thus
   bounded by the pressure reserve, with no minimizer existence needed.

5. **Reserve absorption of the gap** (finiteValueComparisonWithReserveCost_of_
   palmIdentificationGap): if the stationarity comparison holds only up to a gap
   C' * rho^(1 - 2/q), the finite-value comparison still holds with the reserve
   constant increased from C to C + C'.  The gap is absorbed into the reserve.

## Remaining sub-gap

Only the explicit gap bound is missing: the canonical candidate's minimizer gap
must be bounded by C' * rho^(1 - 2/q) (or by the pressure reserve R at the
dilated tilt), uniformly in rho.  Theorem 4 reduces that bound to the pressure
reserve comparison p t <= I_w t + R; theorem 5 shows any such bound is
absorbable.  No further order-algebra step is missing.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X]

/-- **Approximate minimizers exist.**  For every eps > 0 some legal weighted
stationary matching has value below I_w t + eps.  This replaces exact minimizer
existence, which is not available in the weighted stationary lane. -/
theorem exists_value_lt_legalWeightedInf_add
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} (t : ℝ)
    (hne : (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)).Nonempty)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      Q.value t < legalWeightedInf q α β kin g t + eps := by
  unfold legalWeightedInf
  have hlt : sInf (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)) <
      sInf (Set.range
        (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)) + eps := by
    linarith
  obtain ⟨b, hb, hblt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨Q, rfl⟩ := hb
  exact ⟨Q, hblt⟩

/-- **The minimizer gap is nonnegative.** -/
theorem minimizerGap_nonneg
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} (t : ℝ)
    (hbdd : BddBelow (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)))
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    0 ≤ Q.value t - legalWeightedInf q α β kin g t := by
  have h := legalWeightedInf_le_value t hbdd Q
  linarith

/-- **Near-minimizer Palm route.**  If the population measure is the Palm law of
a candidate whose value is within eps of the weighted stationary value, the
population pressure is at most I_w t + eps. -/
theorem stationarity_add_minimizerGap_of_palm
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q₀ : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hmu : μ = legalMarkedJointPalm q Q₀.law)
    (hIint : Integrable (fun m => I m t) μ)
    (hpt : ∀ᵐ m ∂μ, I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    {eps : ℝ} (hQ : Q₀.value t ≤ legalWeightedInf q α β kin g t + eps) :
    (∫ m, I m t ∂μ) ≤ legalWeightedInf q α β kin g t + eps := by
  have hdom := domination_of_population_eq_palm Q₀ t I μ hmu hIint hpt
  linarith

/-- **Canonical-candidate absorption.**  The canonical finite-optimum candidate
satisfies M.value t <= p t (energy bound, FinslerOriginalReserveCompletion
Stationary), so its minimizer gap is at most the pressure reserve p t - I_w t.
If a pressure reserve p t <= I_w t + R is available, the population pressure,
integrated against the candidate's Palm law, is at most I_w t + R. -/
theorem stationarity_of_canonicalCandidate
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (hIint : Integrable (fun m => I m t) (legalMarkedJointPalm q M.law))
    (hpt : ∀ᵐ m ∂(legalMarkedJointPalm q M.law),
      I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    {p R : ℝ} (henergy : M.value t ≤ p)
    (hpress : p ≤ legalWeightedInf q α β kin g t + R) :
    (∫ m, I m t ∂legalMarkedJointPalm q M.law) ≤
      legalWeightedInf q α β kin g t + R := by
  have hdom := domination_of_pointwise M t I hIint hpt
  linarith

/-- **Reserve absorption of the gap.**  If the stationarity comparison holds up
to the minimizer gap C' * rho^(1 - 2/q), the finite-value comparison holds with
the reserve constant increased from C to C + C': the gap is absorbed into the
reserve. -/
theorem finiteValueComparisonWithReserveCost_of_palmIdentificationGap
    {q : ℕ} (hq : 2 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {p : ℝ → ℝ} {C G C' : ℝ}
    (hC0 : 0 ≤ C) (hC1 : 1 ≤ C) (hG0 : 0 ≤ G) (hC'0 : 0 ≤ C')
    (μ : Measure X) [IsFiniteMeasure μ]
    (S : ℝ → Set X) (hS : ∀ rho, MeasurableSet (S rho))
    (I : X → ℝ → ℝ)
    (hIm : ∀ x u, |I x u| ≤ C + |u| * G)
    (hdelta : ∀ rho, 0 < rho → rho < 1 → μ.real ((S rho)ᶜ) ≤ rho)
    (hint : ∀ t rho, 0 < rho → rho < 1 →
      Integrable (fun x => I x (t * (1 - rho) ^ (2 / (q : ℝ)))) μ)
    (hpalm : ∀ t rho, 0 < rho → rho < 1 →
      p t ≤ ∫ x, (1 - rho) ^ (-(2 / (q : ℝ))) *
          I x (t * (1 - rho) ^ (2 / (q : ℝ)))
        ∂(μ.withDensity ((S rho).indicator (fun _ => ENNReal.ofReal (1 - rho)))))
    (hstat : ∀ t rho, 0 < rho → rho < 1 →
      (∫ x, I x (t * (1 - rho) ^ (2 / (q : ℝ))) ∂μ) ≤
        legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) +
          C' * rho ^ (1 - 2 / (q : ℝ))) :
    FiniteValueComparisonWithReserveCost q α β kin g p (C + C') G := by
  intro t rho hrho0 hrho1
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hexp : 0 ≤ 2 / (q : ℝ) := by positivity
  have hlam0 : 0 < 1 - rho := by linarith
  have hlam1 : 1 - rho ≤ 1 := by linarith
  have hpow_le : (1 - rho) ^ (2 / (q : ℝ)) ≤ 1 :=
    Real.rpow_le_one hlam0.le hlam1 hexp
  have hs0 : 0 ≤ 1 - 2 / (q : ℝ) := by
    have h : 2 / (q : ℝ) ≤ 1 := (div_le_one hq0).mpr (by exact_mod_cast hq.le)
    linarith
  have hBbound : ∀ x, |I x (t * (1 - rho) ^ (2 / (q : ℝ)))| ≤ C + |t| * G := by
    intro x
    have h1 := hIm x (t * (1 - rho) ^ (2 / (q : ℝ)))
    have h2 : |t * (1 - rho) ^ (2 / (q : ℝ))| ≤ |t| := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hlam0.le _)]
      nlinarith [abs_nonneg t]
    have h3 : |t * (1 - rho) ^ (2 / (q : ℝ))| * G ≤ |t| * G :=
      mul_le_mul_of_nonneg_right h2 hG0
    linarith
  have hBnn0 : 0 ≤ C + |t| * G := by
    have h1 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
    linarith
  have hmain := retainedPressure_le_dilated_add_boundary (μ := μ) (S := S rho)
    (hS := hS rho) I t hlam0 hBnn0 hBbound (hint t rho hrho0 hrho1)
    (hpalm t rho hrho0 hrho1) (hdelta rho hrho0 hrho1)
  have hstat' := hstat t rho hrho0 hrho1
  have habs := boundaryLoss_le_reserveCost hq t rho C G (C + |t| * G) rho
    hrho0 hrho1 hC0 hC1 hG0 (le_refl _) hBnn0 (le_of_lt hrho0) (le_refl rho)
  have hfac : 0 ≤ (1 - rho) ^ (1 - 2 / (q : ℝ)) := Real.rpow_nonneg hlam0.le _
  have hfac1 : (1 - rho) ^ (1 - 2 / (q : ℝ)) ≤ 1 :=
    Real.rpow_le_one hlam0.le hlam1 hs0
  have hstatmul := mul_le_mul_of_nonneg_left hstat' hfac
  have hexpand : (1 - rho) ^ (1 - 2 / (q : ℝ)) *
      (legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) +
        C' * rho ^ (1 - 2 / (q : ℝ))) =
      (1 - rho) ^ (1 - 2 / (q : ℝ)) *
        legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) +
      (1 - rho) ^ (1 - 2 / (q : ℝ)) * (C' * rho ^ (1 - 2 / (q : ℝ))) := by
    ring
  have hgap0 : 0 ≤ C' * rho ^ (1 - 2 / (q : ℝ)) :=
    mul_nonneg hC'0 (Real.rpow_nonneg hrho0.le _)
  have hgaple : (1 - rho) ^ (1 - 2 / (q : ℝ)) * (C' * rho ^ (1 - 2 / (q : ℝ))) ≤
      C' * rho ^ (1 - 2 / (q : ℝ)) :=
    mul_le_of_le_one_left hgap0 hfac1
  have hCC : C * rho ^ (1 - 2 / (q : ℝ)) ≤
      (C + C') * rho ^ (1 - 2 / (q : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hrho0.le _)
  have htG : C * |t| * G * rho ≤ (C + C') * |t| * G * rho := by
    have h0 : 0 ≤ |t| * G * rho := by
      have h1 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
      exact mul_nonneg h1 hrho0.le
    have h1 := mul_le_mul_of_nonneg_right (show C ≤ C + C' by linarith) h0
    calc C * |t| * G * rho = C * (|t| * G * rho) := by ring
      _ ≤ (C + C') * (|t| * G * rho) := h1
      _ = (C + C') * |t| * G * rho := by ring
  linarith [hmain, habs, hstatmul, hexpand, hgaple, hCC, htG]

end OTSelector.Reconstruction
