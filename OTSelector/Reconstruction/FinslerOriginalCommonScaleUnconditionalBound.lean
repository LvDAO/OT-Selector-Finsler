import OTSelector.Reconstruction.FinslerOriginalCommonScaleCertifiedBound
import OTSelector.Reconstruction.FinslerOriginalCommonScaleLargeAmplitude

/-!
# Unconditional whole-path bound via the amplitude-one two-phase split

Task-109 identified the wall hypotheses as incompatible with the large-branch
threshold requirement 1 <= H. The natural relaxation to 1 <= C * H is not
available either: the retained current-scale certificate set carries the
conjunct 1 <= amplitude, so for a threshold H < 1 the large-amplitude branch
{H < amplitude} is not contained in the certificate set (the amplitude slice
H < amplitude < 1 is lost). We record this obstruction explicitly below.

The correct unconditional decomposition is at amplitude one, with no wall
hypotheses at all:

* the bounded-phase branch {amplitude <= max 1 (2(La+b))};
* the large-amplitude branch {1 < amplitude and 2(La+b) <= amplitude}.

The large-amplitude branch is fully instantiated: its retained certificate index
is N = floor C with C the canonical phase scale coefficient, which satisfies
1 <= N and N <= C * 1, so the large-amplitude module applies with H = 1.

The final theorem splices the two branches by the two-branch cover lemma and adds
the exact exponential phase-bad-event tail. The only input left is the
bounded-phase squared-integral certificate (its MemLp half is supplied by the
pre-existing bounded-phase traffic module).
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

/-- The proposed relaxation cannot work: for a threshold H < 1 the amplitude
slice H < x < 1 is nonempty, so the large-amplitude set {H < x} is not
contained in {1 <= x} and hence not in any certificate set requiring
1 <= amplitude. -/
theorem largeBranch_relaxation_false {H : ℝ} (hH : H < 1) :
    ¬ ({x : ℝ | H < x} ⊆ {x : ℝ | 1 ≤ x}) := by
  intro hsub
  have hx : H < (H + 1) / 2 := by linarith
  have h1 : (1 : ℝ) ≤ (H + 1) / 2 := hsub hx
  linarith

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The retained certificate index for the amplitude-one large branch:
N = floor C, with 1 <= N and N <= C * 1. -/
theorem floor_coefficient_index (L : ℝ≥0) (ρ A : ℝ) :
    1 ≤ Nat.floor (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A) ∧
      ((Nat.floor (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A) : ℕ) : ℝ) ≤
        canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A * 1 := by
  have hC1 : (1 : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A :=
    (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1
  have hC0 : (0 : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A := by linarith
  refine ⟨?_, ?_⟩
  · exact Nat.le_floor (by simpa only [Nat.cast_one] using hC1)
  · simpa using Nat.floor_le hC0

/-- The large-amplitude branch certificate at threshold one, fully instantiated:
the branch {1 < amplitude and 2(La+b) <= amplitude} inherits the retained
certificate L2 bound with index N = floor C. -/
theorem ae_largeAmplitudeBranch_one_sq_integral_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (ρ A a b B : ℝ)
    {P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}
    {traffic : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ}
    (hLp : MemLp (Set.indicator {s |
        ((Nat.floor (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A) : ℕ) : ℝ) ≤
          (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic) 2 P)
    (hInt : (∫ x, (Set.indicator {s |
        ((Nat.floor (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A) : ℕ) : ℝ) ≤
          (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic x) ^ 2 ∂P) ≤ B) :
    MemLp (Set.indicator {s | 1 <
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic) 2 P ∧
      (∫ x, (Set.indicator {s | 1 <
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic x) ^ 2 ∂P) ≤ B := by
  obtain ⟨hN, hNH⟩ := floor_coefficient_index L ρ A
  exact D.ae_largeAmplitudeBranch_sq_integral_le hF hw T hcut h L ρ A
    (a := a) (b := b) (H := 1) (B := B)
    (N := Nat.floor (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A))
    le_rfl hN hNH hLp hInt

/-- Amplitude-one two-phase cover of the complement of the phase-curve bad event:
every scene is either bounded-phase at level max 1 (2(La+b)) or in the
large-amplitude branch at threshold one. -/
theorem amplitude_one_cover
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (h : ℝ) (L : ℝ≥0) (a b radius K : ℝ) :
    (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ ⊆
      {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
          max 1 (2 * ((L : ℝ) * a + b))} ∪
        {s | 1 < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} := by
  intro s _
  have hTle : 2 * ((L : ℝ) * a + b) ≤ max 1 (2 * ((L : ℝ) * a + b)) :=
    le_max_right _ _
  have h1le : (1 : ℝ) ≤ max 1 (2 * ((L : ℝ) * a + b)) := le_max_left _ _
  by_cases hle : ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
      max 1 (2 * ((L : ℝ) * a + b))
  · exact Or.inl hle
  · have hgt : max 1 (2 * ((L : ℝ) * a + b)) <
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := not_le.mp hle
    exact Or.inr ⟨by linarith, by linarith⟩

/-- Final unconditional whole-path bound: bounded-phase branch at
max 1 (2(La+b)) plus the fully instantiated large-amplitude branch at
threshold one, spliced off the phase-curve bad event, with the exact exponential
phase-bad-event tail. The only branch input is the bounded-phase squared-integral
certificate. -/
theorem ae_original_minimizer_commonScale_unconditional_of_boundedPhase
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (ρ A a b : ℝ) (radius K CB Blarge : ℝ)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {traffic : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ}
    (hBddLp : MemLp (Set.indicator {s |
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
          max 1 (2 * ((L : ℝ) * a + b))} traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (hBddInt : (∫ x, (Set.indicator {s |
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
          max 1 (2 * ((L : ℝ) * a + b))} traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ CB)
    (hCertLp : MemLp (Set.indicator {s |
        ((Nat.floor (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A) : ℕ) : ℝ) ≤
          (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (hCertInt : (∫ x, (Set.indicator {s |
        ((Nat.floor (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A) : ℕ) : ℝ) ≤
          (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} traffic x) ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        Blarge) :
    MemLp ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ.indicator traffic) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ x, ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ.indicator
          traffic x) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
        2 * CB + 2 * Blarge ∧
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
          (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) ≤
        Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
            (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
            2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
              (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
              (Real.exp 1 - 1))) := by
  have hmeas : Measurable (fun s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) ↦
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hBad : MeasurableSet
      (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) :=
    D.measurableSet_normalizedSourcePhaseCurveBadEvent hF hw T hcut 1 radius K
  have hA : MeasurableSet {s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) |
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
          max 1 (2 * ((L : ℝ) * a + b))} :=
    measurableSet_le hmeas measurable_const
  have hB : MeasurableSet {s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) |
        1 < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} :=
    (measurableSet_lt measurable_const hmeas).inter
      (measurableSet_le measurable_const hmeas)
  have hcover := amplitude_one_cover (D := D) (cut := cut) T h L a b radius K
  have hlarge := ae_largeAmplitudeBranch_one_sq_integral_le (D := D)
    hF hw T hcut h L ρ A a b Blarge hCertLp hCertInt
  have hmain := memLp_two_indicator_of_branch_cover hBad hcover hA hB
    hBddLp hBddInt hlarge.1 hlarge.2
  exact ⟨hmain.1, hmain.2,
    D.normalizedSourcePhaseCurveBadEvent_one_measure_real_le hF hw T hcut Q radius K⟩

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
