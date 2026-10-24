import OTSelector.Reconstruction.FinslerOriginalCommonScaleCertifiedBound

/-!
# Geometric parameters and wall hypotheses for the certified two-branch bound

The certified whole-path bound of FinslerOriginalCommonScaleCertifiedBound
carries three geometric parameter hypotheses: the wall bounds on the truncation
level Hs = max H (2(La+b)), positivity of the two wall constants, and the
counting-threshold bound. This file analyses these parameters.

The main finding is a genuine incompatibility: the truncation wall bounds are
strictly smaller than 1, while the large-amplitude branch requires the branch
threshold H to satisfy 1 <= H, and Hs >= H. Hence for 0 <= rho the wall
hypotheses can never be discharged with 1 <= H.

The remaining lemmas therefore record the strongest available statements:

* the truncation level is always at least 1 when 1 <= H;
* the wall hypotheses are incompatible with 0 <= rho and 1 <= H;
* replacing the large-branch threshold condition 1 <= H by its actual
  operative consequence 1 <= C * H (with C the canonical scale coefficient)
  makes all wall hypotheses simultaneously satisfiable with the explicit choice
  H = 1 / C, Hs = max H T, N = 1, provided the amplitude threshold T is
  small enough and K is the counting threshold itself.

Thus the exact residual compatibility constraint is the large-amplitude module's
1 <= H hypothesis: it must be weakened to 1 <= C * H.
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

/-- The truncation level max H (2(La+b)) is at least 1 as soon as H >= 1. -/
theorem one_le_wallLevel (H L a b : ℝ) (hH : 1 ≤ H) :
    1 ≤ max H (2 * (L * a + b)) :=
  le_max_of_le_left hH

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The certified bound's wall hypotheses are incompatible with the large-branch
threshold requirement 1 <= H whenever 0 <= rho. Indeed the truncation level
dominates H >= 1 while the first wall is at most 1 / 2. -/
theorem wall_hypotheses_incompatible
    (Hc H L a b ρ : ℝ) (hH : 1 ≤ H) (hρ : 0 ≤ ρ)
    (hHc : Hc = max H (2 * (L * a + b)))
    (hwall1 : Hc ≤ 1 / (2 * (ρ + 1))) : False := by
  have hlevel : 1 ≤ Hc := by
    rw [hHc]
    exact le_max_of_le_left hH
  have hle : 1 / (2 * (ρ + 1)) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ 2 * (ρ + 1) := by linarith
    exact one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- With the wall constant positivity, the explicit truncation level
max (1 / C) T stays inside both wall bounds as soon as the amplitude threshold
T does, where C is the canonical phase scale coefficient. -/
theorem wallLevel_le_walls_of_small_amplitude
    (L ρ A T : ℝ) (hc1 : 0 < 2 * (ρ + 1)) (hc2 : 0 < 4 * (1 + L) * A)
    (hT1 : T ≤ 1 / (2 * (ρ + 1))) (hT2 : T ≤ 1 / (4 * (1 + L) * A)) :
    max (1 / canonicalPhaseCurveScaleCoefficient L ρ A) T ≤ 1 / (2 * (ρ + 1)) ∧
      max (1 / canonicalPhaseCurveScaleCoefficient L ρ A) T ≤
        1 / (4 * (1 + L) * A) := by
  have hC2 : 2 * (ρ + 1) ≤ canonicalPhaseCurveScaleCoefficient L ρ A :=
    (canonicalPhaseCurveScaleCoefficient_bounds L ρ A).2.1
  have hC3 : 4 * (1 + L) * A ≤ canonicalPhaseCurveScaleCoefficient L ρ A :=
    (canonicalPhaseCurveScaleCoefficient_bounds L ρ A).2.2
  refine ⟨max_le ?_ hT1, max_le ?_ hT2⟩
  · exact one_div_le_one_div_of_le hc1 hC2
  · exact one_div_le_one_div_of_le hc2 hC3

/-- Explicit relaxed parameter choice: H = 1 / C, Hs = max H T, N = 1. All wall
bounds and the scale relation N <= C * H hold, and 1 <= C * H holds; only the
large-branch module's 1 <= H itself fails. -/
theorem exists_relaxed_parameters
    (L ρ A T : ℝ) (hc1 : 0 < 2 * (ρ + 1)) (hc2 : 0 < 4 * (1 + L) * A)
    (hT1 : T ≤ 1 / (2 * (ρ + 1))) (hT2 : T ≤ 1 / (4 * (1 + L) * A)) :
    let C := canonicalPhaseCurveScaleCoefficient L ρ A
    let H := 1 / C
    let Hc := max H T
    let N : ℕ := 1
    Hc ≤ 1 / (2 * (ρ + 1)) ∧ Hc ≤ 1 / (4 * (1 + L) * A) ∧
      1 ≤ C * H ∧ 1 ≤ N ∧ (N : ℝ) ≤ C * H ∧
        (Hc = max H T) := by
  dsimp only
  have hCpos : 0 < canonicalPhaseCurveScaleCoefficient L ρ A := by
    have hC1 : 1 ≤ canonicalPhaseCurveScaleCoefficient L ρ A :=
      (canonicalPhaseCurveScaleCoefficient_bounds L ρ A).1
    linarith
  have hCH : canonicalPhaseCurveScaleCoefficient L ρ A *
      (1 / canonicalPhaseCurveScaleCoefficient L ρ A) = 1 := by
    field_simp
  have hwalls := wallLevel_le_walls_of_small_amplitude L ρ A T hc1 hc2 hT1 hT2
  refine ⟨hwalls.1, hwalls.2, ?_, ?_, ?_, rfl⟩
  · rw [hCH]
  · exact le_rfl
  · rw [hCH]
    norm_num

/-- The counting threshold hypothesis is discharged by taking K to be the
threshold itself. -/
theorem counting_threshold_choice
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut r : ℝ) :
    let K := D.normalizedSourcePhaseCurveCountThreshold T cut r
    0 ≤ K ∧ D.normalizedSourcePhaseCurveCountThreshold T cut r ≤ K := by
  dsimp only
  exact ⟨le_of_lt (D.normalizedSourcePhaseCurveCountThreshold_pos T cut r), le_rfl⟩

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
