import OTSelector.Reconstruction.FinslerOriginalLargeWindowTrafficExpectation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Common-scale large-amplitude branch

The large-amplitude branch of the two-branch whole-path L2 estimate is the event
where the literal normalized momentum field amplitude exceeds a truncation level
H and the canonical node comparison holds. For the scene-selected canonical
integer scale, exceeding H implies the retained integer threshold, so the branch
is contained in the existing large-amplitude certificate set. Therefore the
existing large-amplitude square bound transfers to the amplitude-defined branch,
and the index error of the certificate vanishes along the truncation index.
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

/-- A squared-indicator L2 bound transfers from a larger measurable set to a
smaller subset of it. -/
theorem memLp_two_indicator_sq_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {A B : Set Ω} (hAB : A ⊆ B) (hA : MeasurableSet A) {C : ℝ}
    (hLp : MemLp (B.indicator f) 2 P)
    (hInt : (∫ x, (B.indicator f x) ^ 2 ∂P) ≤ C) :
    MemLp (A.indicator f) 2 P ∧ (∫ x, (A.indicator f x) ^ 2 ∂P) ≤ C := by
  have hEq : A.indicator f = A.indicator (B.indicator f) := by
    funext x
    by_cases hx : x ∈ A
    · have hx' : x ∈ B := hAB hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · simp only [Set.indicator_of_notMem hx]
  have hLpA : MemLp (A.indicator (B.indicator f)) 2 P := by
    refine MemLp.of_le_mul (g := B.indicator f) (c := 1) hLp
      (hLp.aestronglyMeasurable.indicator hA) ?_
    filter_upwards with x
    by_cases hx : x ∈ A
    · have hx' : x ∈ B := hAB hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
      simp
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      positivity
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact hLpA
  · have hpt : ∀ x, (A.indicator (B.indicator f) x) ^ 2 ≤ (B.indicator f x) ^ 2 := by
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        nlinarith [sq_nonneg (B.indicator f x)]
    have hIntB : Integrable (fun x ↦ (B.indicator f x) ^ 2) P := hLp.integrable_sq
    have hIntA : Integrable (fun x ↦ (A.indicator (B.indicator f) x) ^ 2) P :=
      hLpA.integrable_sq
    calc (∫ x, (A.indicator f x) ^ 2 ∂P)
        = ∫ x, (A.indicator (B.indicator f) x) ^ 2 ∂P := by rw [hEq]
      _ ≤ ∫ x, (B.indicator f x) ^ 2 ∂P :=
          integral_mono_ae hIntA hIntB (ae_of_all _ hpt)
      _ ≤ C := hInt

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The amplitude-defined large-amplitude branch is contained in the retained
canonical integer certificate set: for H at least one and integer threshold N of
size at most the coefficient times H, exceeding H puts the scene's selected
canonical integer scale above N. -/
theorem largeCanonicalAmplitudeBranch_subset
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (ρ A : ℝ)
    {a b H : ℝ} {N : ℕ} (hH : 1 ≤ H) (hN : 1 ≤ N)
    (hNH : (N : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A * H) :
    {s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) |
        H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖} ⊆
      {s | (N : ℝ) ≤ (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖} := by
  intro s hs
  obtain ⟨hamp, hcomp⟩ := hs
  have hC1 : (1 : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A :=
    (canonicalPhaseCurveScaleCoefficient_bounds (L : ℝ) ρ A).1
  have hCpos : (0 : ℝ) < canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A :=
    lt_of_lt_of_le zero_lt_one hC1
  have hk1 : (1 : ℝ) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := by
    linarith
  have hCH : canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A * H <
      canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A *
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ :=
    mul_lt_mul_of_pos_left hamp hCpos
  have hNamp : (N : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A *
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := le_trans hNH hCH.le
  have hceil : canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A *
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
      (Nat.ceil (canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A *
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖) : ℝ) := Nat.le_ceil _
  have hk : (N : ℝ) ≤ (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) := by
    unfold normalizedCanonicalCurveIntegerScale canonicalPhaseIntegerScale
    exact hNamp.trans hceil
  exact ⟨hk, hk1, hcomp⟩

/-- The large-amplitude branch square bound follows from the retained canonical
integer certificate: on the amplitude branch exceeding H the literal traffic
square is L2 with the same bound as the certificate set. -/
theorem ae_largeAmplitudeBranch_sq_integral_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (ρ A : ℝ)
    {a b H B : ℝ} {N : ℕ} (hH : 1 ≤ H) (hN : 1 ≤ N)
    (hNH : (N : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A * H)
    {P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}
    {traffic : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ}
    (hLp : MemLp ({s | (N : ℝ) ≤
        (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖}.indicator traffic) 2 P)
    (hInt : (∫ x, ((({s | (N : ℝ) ≤
        (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖}).indicator traffic) x) ^ 2 ∂P) ≤ B) :
    MemLp ({s | H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
        2 * ((L : ℝ) * a + b) ≤
          ‖D.normalizedMomentumPhaseField T cut h L s 0‖}.indicator traffic) 2 P ∧
      (∫ x, ((({s | H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
        2 * ((L : ℝ) * a + b) ≤
          ‖D.normalizedMomentumPhaseField T cut h L s 0‖}).indicator traffic) x) ^ 2 ∂P) ≤ B := by
  have hmeas : Measurable (fun s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) ↦
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hA : MeasurableSet {s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) |
        H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖} :=
    (measurableSet_lt measurable_const hmeas).inter
      (measurableSet_le measurable_const hmeas)
  exact memLp_two_indicator_sq_of_subset
    (largeCanonicalAmplitudeBranch_subset D hF hw T hcut h L ρ A hH hN hNH)
    hA hLp hInt

end OriginalSeedConditionalMoments

/-- Along the truncation index, the retained certificate index error vanishes:
the integer index is the floor of the coefficient times the truncation level. -/
theorem tendsto_floorIndex_error {err : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (herr : Tendsto err atTop (𝓝 0)) :
    Tendsto (fun H : ℝ ↦ err ⌊C * H⌋₊) atTop (𝓝 0) :=
  herr.comp ((tendsto_nat_floor_atTop (α := ℝ)).comp
    ((tendsto_const_mul_atTop_of_pos (f := fun x : ℝ => x) hC).mpr tendsto_id))

end OTSelector.Reconstruction
