import OTSelector.Reconstruction.FinslerOriginalStationaryDomination
import OTSelector.Reconstruction.MarkedStationaryValueLegalScenePalmReadout

/-!
# Common Palm and the fixed-measure comparison for stationarity

This module investigates the remaining sub-gap of
FinslerOriginalStationaryDomination: the pointwise comparison gives the
domination of the population pressure by every candidate value only for the
candidate's OWN Palm law, while the stationarity inequality needs a FIXED
population measure.

Findings:

* The Palm law is the mean of a scene kernel over the scene law:
  legalMarkedJointPalm q Q = legalMarkedSceneUnitPalmKernel q o_m Q
  (legalMarkedJointPalm_eq_unitPalmKernel_comp).  It therefore depends on the
  whole scene law and NOT only on the input law: two candidates with the same
  prescribed input Poisson law can have different Palm laws.  Hence the common
  Palm hypothesis (i) is not derivable from the structure fields.

* What IS common to all candidates is the pair of clock marginals: every
  candidate Palm has source clock alpha and target clock beta
  (candidatePalm_marginals).  So the candidate Palms form a family of
  probability measures with common scalar marginals.

* Consequently the strongest true form of the fixed-measure comparison is the
  Palm identification for ONE candidate, with an explicit minimizer-gap
  residual:
    int I dmu <= Q0.value t = I_w(t) + (Q0.value t - I_w t)
  whenever mu is Q0's Palm and I is pointwise dominated by the marked cost
  (stationarity_add_minimizerGap), and if the candidate is a minimizer
  (Q0.value t <= I_w t) the stationarity inequality holds outright
  (stationarity_of_population_minimizerPalm).

## Remaining sub-gap

The residual (Q0.value t - I_w t) >= 0 is the minimizer gap of the candidate
whose Palm is the population measure.  Closing it requires either the Palm
identification with an actual minimizer, or a comparison of the fixed population
integral with every candidate's Palm cost integral.  The kernel-composition
identity shows that the Palm does depend on the full scene law, so common-Palm
cannot be obtained from the structure fields alone.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-- **Every candidate Palm has the prescribed clock marginals.**  This is the
common data of all legal weighted stationary candidates. -/
theorem candidatePalm_marginals
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    (legalMarkedJointPalm q Q.law).map (fun m => m.1.1) = α ∧
      (legalMarkedJointPalm q Q.law).map (fun m => m.1.2) = β :=
  ⟨Q.source_clock, Q.target_clock⟩

/-- **Domination when the population measure is a candidate's Palm.**  If the
fixed population measure is the Palm law of the candidate Q0, the pointwise
comparison gives the domination of the population pressure by Q0's value. -/
theorem domination_of_population_eq_palm
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q₀ : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hmu : μ = legalMarkedJointPalm q Q₀.law)
    (hIint : Integrable (fun m => I m t) μ)
    (hpt : ∀ᵐ m ∂μ, I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) :
    (∫ m, I m t ∂μ) ≤ Q₀.value t := by
  have hIint' : Integrable (fun m => I m t) (legalMarkedJointPalm q Q₀.law) := by
    rwa [hmu] at hIint
  have hpt' : ∀ᵐ m ∂(legalMarkedJointPalm q Q₀.law),
      I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 := by
    rwa [hmu] at hpt
  rw [hmu]
  exact domination_of_pointwise Q₀ t I hIint' hpt'

/-- **Fixed-measure comparison with explicit minimizer-gap residual.**  If the
population measure is a candidate's Palm and the local pressure is pointwise
dominated by the marked cost, then the population pressure is at most the
weighted stationary value PLUS the candidate's minimizer gap. -/
theorem stationarity_add_minimizerGap
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q₀ : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hmu : μ = legalMarkedJointPalm q Q₀.law)
    (hIint : Integrable (fun m => I m t) μ)
    (hpt : ∀ᵐ m ∂μ, I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    (hbdd : BddBelow (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t))) :
    (∫ m, I m t ∂μ) ≤
      legalWeightedInf q α β kin g t +
        (Q₀.value t - legalWeightedInf q α β kin g t) := by
  have hdom := domination_of_population_eq_palm Q₀ t I μ hmu hIint hpt
  have hinf : legalWeightedInf q α β kin g t ≤ Q₀.value t :=
    legalWeightedInf_le_value t hbdd Q₀
  linarith

/-- **Stationarity when the population measure is a minimizer's Palm.**  If the
fixed population measure is the Palm law of a candidate which realizes the
infimum, the pointwise comparison gives the stationarity inequality
int I dmu <= I_w(t) outright. -/
theorem stationarity_of_population_minimizerPalm
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q₀ : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (I : PhysicalPairPalmMark (Fin q) → ℝ → ℝ)
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hmu : μ = legalMarkedJointPalm q Q₀.law)
    (hIint : Integrable (fun m => I m t) μ)
    (hpt : ∀ᵐ m ∂μ, I m t ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    (hmin : Q₀.value t ≤ legalWeightedInf q α β kin g t) :
    (∫ m, I m t ∂μ) ≤ legalWeightedInf q α β kin g t := by
  have hdom := domination_of_population_eq_palm Q₀ t I μ hmu hIint hpt
  linarith

end OTSelector.Reconstruction
