import OTSelector.Reconstruction.FinslerOriginalCommonScaleTwoBranch
import OTSelector.Reconstruction.FinslerOriginalCommonScaleCountingTransfer
import OTSelector.Reconstruction.FinslerNormalizedAdaptivePhaseCurveCounts

/-!
# Branch certificates and probability tail for the two-branch whole-path L2

This file assembles the final certificates of the two-branch splice:

* the small/truncation branch certificate is the counting good-event L2 theorem
  transferred through the wall-to-truncation containment (the counting bad event
  lies inside the phase bad event union the truncation complement);
* the large-amplitude branch certificate is the large-amplitude module output;
* the phase-curve bad event carries its exact exponential phase-walk tail.

The final theorem states the whole-path L2/Palm-square bound off the phase bad
event with the explicit probability tail, the squared integral paying twice the
small-branch coefficient plus twice the large-branch coefficient.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Small-branch certificate: a counting good-event L2 bound transfers to the
truncation branch off the phase bad event, provided the counting bad event lies
inside the larger truncation bad event. -/
theorem smallBranch_of_counting
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {BadCount Bad : Set Ω} (hsub : BadCount ⊆ Bad) (hBad : MeasurableSet Bad) {C : ℝ}
    (hLp : MemLp (BadCountᶜ.indicator f) 2 P)
    (hInt : (∫ x, (BadCountᶜ.indicator f x) ^ 2 ∂P) ≤ C) :
    MemLp (Badᶜ.indicator f) 2 P ∧
      (∫ x, (Badᶜ.indicator f x) ^ 2 ∂P) ≤ C :=
  memLp_two_indicator_of_bad_subset hsub hBad hLp hInt

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Phase-curve bad event is Borel at the counting radius. -/
theorem measurableSet_phaseBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (radius K : ℝ) :
    MeasurableSet (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) :=
  D.measurableSet_normalizedSourcePhaseCurveBadEvent hF hw T hcut 1 radius K

/-- Final two-branch whole-path L2 bound off the phase bad event, with explicit
branch coefficients and the exact exponential phase-walk probability tail. -/
theorem ae_original_minimizer_commonScale_twoBranch_probability
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (ρ A a b : ℝ) (radius K : ℝ) {H Hc : ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {traffic : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ}
    {CA CL : ℝ}
    (hHc : Hc = max H (2 * ((L : ℝ) * a + b)))
    (hSmallLp : MemLp (Set.indicator (({t | Hc <
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖} ∪
        D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ) traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (hSmallInt : (∫ x, (Set.indicator (({t | Hc <
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖} ∪
        D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ) traffic x) ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ CA)
    (hLargeLp : MemLp (Set.indicator {t | 2 * ((L : ℝ) * a + b) ≤
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖ ∧
          H < ‖D.normalizedMomentumPhaseField T cut h L t 0‖} traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (hLargeInt : (∫ x, (Set.indicator {t | 2 * ((L : ℝ) * a + b) ≤
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖ ∧
          H < ‖D.normalizedMomentumPhaseField T cut h L t 0‖} traffic x) ^ 2
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ CL) :
    MemLp ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ.indicator traffic) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ x, ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ.indicator
          traffic x) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        2 * CA + 2 * CL ∧
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) ≤
        Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
            (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
            2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
              (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
              (Real.exp 1 - 1))) := by
  have hSmallLp' : MemLp (Set.indicator (({t | max H (2 * ((L : ℝ) * a + b)) <
      ‖D.normalizedMomentumPhaseField T cut h L t 0‖} ∪
      D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ) traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) := by
    rw [← hHc]
    exact hSmallLp
  have hSmallInt' : (∫ x, (Set.indicator (({t | max H (2 * ((L : ℝ) * a + b)) <
      ‖D.normalizedMomentumPhaseField T cut h L t 0‖} ∪
      D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ) traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ CA := by
    rw [← hHc]
    exact hSmallInt
  have hsmall := D.ae_twoBranch_memLp_two hF hw T hcut h L radius K a b H
    hSmallLp' hSmallInt' hLargeLp hLargeInt
  refine ⟨hsmall.1, hsmall.2, ?_⟩
  exact D.normalizedSourcePhaseCurveBadEvent_one_measure_real_le hF hw T hcut Q radius K

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
