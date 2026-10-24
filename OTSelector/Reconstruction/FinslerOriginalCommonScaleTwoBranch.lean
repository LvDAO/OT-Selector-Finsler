import OTSelector.Reconstruction.FinslerOriginalCommonScaleLargeAmplitude
import OTSelector.Reconstruction.FinslerOriginalCommonScaleTruncation

/-!
# Final two-branch splice for the common-scale whole-path L2

The amplitude axis is split at the scene level Hs := max H (2*(L*a+b)):
the small/truncation branch is {amp <= Hs} (where the truncation certificate
applies off the phase bad event), and the large-amplitude branch is
{2*(L*a+b) <= amp and H < amp} (where the scene-selected canonical integer
certificate applies). Their union covers the complement of the phase-curve bad
event, so the two branch L2 bounds splice into a whole-path L2 bound off the
phase bad event, with the squared integral paying only the factor two.
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

/-- Branch splice: if two measurable sets cover the complement of a measurable bad
event, the squared-indicator L2 bounds of the two branches splice into the
whole-path bound off the bad event, with the squared integral at most twice the
sum of the branch bounds. -/
theorem memLp_two_indicator_of_branch_cover {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ} {Bad A B : Set Ω} (hBad : MeasurableSet Bad)
    (hcover : Badᶜ ⊆ A ∪ B) (hA : MeasurableSet A) (hB : MeasurableSet B)
    {CA CB : ℝ}
    (hLpA : MemLp (A.indicator f) 2 P)
    (hIntA : (∫ x, (A.indicator f x) ^ 2 ∂P) ≤ CA)
    (hLpB : MemLp (B.indicator f) 2 P)
    (hIntB : (∫ x, (B.indicator f x) ^ 2 ∂P) ≤ CB) :
    MemLp (Badᶜ.indicator f) 2 P ∧
      (∫ x, (Badᶜ.indicator f x) ^ 2 ∂P) ≤ 2 * CA + 2 * CB := by
  have hB'sub : B \ A ⊆ B := Set.sdiff_subset
  have hB'meas : MeasurableSet (B \ A) := hB.diff hA
  obtain ⟨hLpB', hIntB'⟩ := memLp_two_indicator_sq_of_subset hB'sub hB'meas hLpB hIntB
  have hLpsum : MemLp (A.indicator f + (B \ A).indicator f) 2 P := hLpA.add hLpB'
  have heq : Badᶜ.indicator f = Badᶜ.indicator (A.indicator f + (B \ A).indicator f) := by
    funext x
    by_cases hx : x ∈ Badᶜ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.add_apply]
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA, Set.indicator_of_notMem (fun h => h.2 hxA)]
        ring
      · rcases hcover hx with hxA' | hxB
        · exact absurd hxA' hxA
        · rw [Set.indicator_of_notMem hxA,
            Set.indicator_of_mem ((Set.mem_sdiff x).mpr ⟨hxB, hxA⟩)]
          ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hLpBad : MemLp (Badᶜ.indicator f) 2 P := by
    rw [heq]
    refine MemLp.of_le_mul (g := A.indicator f + (B \ A).indicator f) (c := 1) hLpsum
      (hLpsum.aestronglyMeasurable.indicator hBad.compl) ?_
    filter_upwards with x
    by_cases hx : x ∈ Badᶜ
    · rw [Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      simp
  refine ⟨hLpBad, ?_⟩
  have hsq : ∀ x, (Badᶜ.indicator f x) ^ 2 ≤
      2 * (A.indicator f x) ^ 2 + 2 * ((B \ A).indicator f x) ^ 2 := by
    intro x
    by_cases hx : x ∈ Badᶜ
    · rw [Set.indicator_of_mem hx]
      by_cases hxA : x ∈ A
      · rw [Set.indicator_of_mem hxA, Set.indicator_of_notMem (fun h => h.2 hxA)]
        nlinarith [sq_nonneg (f x)]
      · rcases hcover hx with hxA' | hxB
        · exact absurd hxA' hxA
        · rw [Set.indicator_of_notMem hxA,
            Set.indicator_of_mem ((Set.mem_sdiff x).mpr ⟨hxB, hxA⟩)]
          nlinarith [sq_nonneg (f x)]
    · rw [Set.indicator_of_notMem hx]
      nlinarith [sq_nonneg (A.indicator f x), sq_nonneg ((B \ A).indicator f x)]
  have hIntA' : Integrable (fun x => (A.indicator f x) ^ 2) P := hLpA.integrable_sq
  have hIntB'' : Integrable (fun x => ((B \ A).indicator f x) ^ 2) P := hLpB'.integrable_sq
  have hmaj : Integrable (fun x => 2 * (A.indicator f x) ^ 2 +
      2 * ((B \ A).indicator f x) ^ 2) P :=
    (hIntA'.const_mul 2).add (hIntB''.const_mul 2)
  calc (∫ x, (Badᶜ.indicator f x) ^ 2 ∂P)
      ≤ ∫ x, 2 * (A.indicator f x) ^ 2 + 2 * ((B \ A).indicator f x) ^ 2 ∂P :=
        integral_mono_ae hLpBad.integrable_sq hmaj (ae_of_all _ hsq)
    _ = 2 * (∫ x, (A.indicator f x) ^ 2 ∂P) + 2 * (∫ x, ((B \ A).indicator f x) ^ 2 ∂P) := by
        rw [integral_add (hIntA'.const_mul 2) (hIntB''.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * CA + 2 * CB := by
        nlinarith [hIntA, hIntB']

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The amplitude axis is covered off the phase-curve bad event by the small
branch at the scene level Hs = max H (2*(L*a+b)) and the large-amplitude branch
{2*(L*a+b) <= amp, H < amp}; the residual region {H < amp, 2*(L*a+b) > amp} is
absorbed by the small branch. -/
theorem twoBranch_cover
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ)
    (L : ℝ≥0) (radius K a b H : ℝ)
    {s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)}
    (hs : s ∉ D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) :
    s ∈ (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
        {t | max H (2 * ((L : ℝ) * a + b)) <
          ‖D.normalizedMomentumPhaseField T cut h L t 0‖})ᶜ ∪
      {t | 2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L t 0‖ ∧
        H < ‖D.normalizedMomentumPhaseField T cut h L t 0‖} := by
  by_cases hle : ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
      max H (2 * ((L : ℝ) * a + b))
  · refine Or.inl ?_
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨hs, not_lt.mpr hle⟩
  · have hlt : max H (2 * ((L : ℝ) * a + b)) <
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ := not_le.mp hle
    have hH : H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ :=
      lt_of_le_of_lt (le_max_left _ _) hlt
    have hT : 2 * ((L : ℝ) * a + b) <
        ‖D.normalizedMomentumPhaseField T cut h L s 0‖ :=
      lt_of_le_of_lt (le_max_right _ _) hlt
    exact Or.inr ⟨hT.le, hH⟩

/-- Final two-branch splice: off the phase-curve bad event, the literal
whole-path traffic is L2 with the squared integral bounded by twice the sum of
the small/truncation branch bound and the large-amplitude branch bound at the
scene level Hs = max H (2*(L*a+b)). -/
theorem ae_twoBranch_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ)
    (L : ℝ≥0) (radius K a b H : ℝ)
    {P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))}
    {traffic : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ}
    {CA CB : ℝ}
    (hLpA : MemLp ((({t | max H (2 * ((L : ℝ) * a + b)) <
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖} ∪
        D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ).indicator traffic) 2 P)
    (hIntA : (∫ x, ((({t | max H (2 * ((L : ℝ) * a + b)) <
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖} ∪
        D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ).indicator traffic x) ^ 2 ∂P)
        ≤ CA)
    (hLpB : MemLp ({t | 2 * ((L : ℝ) * a + b) ≤
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖ ∧
          H < ‖D.normalizedMomentumPhaseField T cut h L t 0‖}.indicator traffic) 2 P)
    (hIntB : (∫ x, (({t | 2 * ((L : ℝ) * a + b) ≤
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖ ∧
          H < ‖D.normalizedMomentumPhaseField T cut h L t 0‖}.indicator traffic) x) ^ 2 ∂P)
        ≤ CB) :
    MemLp ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ.indicator traffic) 2 P ∧
      (∫ x, ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ.indicator
        traffic x) ^ 2 ∂P) ≤ 2 * CA + 2 * CB := by
  have hmeas : Measurable (fun s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) ↦
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖) :=
    ((D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
      (measurable_id.prodMk measurable_const)).norm
  have hBad : MeasurableSet
      (D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K) :=
    D.measurableSet_normalizedSourcePhaseCurveBadEvent hF hw T hcut 1 radius K
  have hA : MeasurableSet (({t | max H (2 * ((L : ℝ) * a + b)) <
      ‖D.normalizedMomentumPhaseField T cut h L t 0‖} ∪
      D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K)ᶜ) :=
    (measurableSet_lt measurable_const hmeas |>.union hBad).compl
  have hB : MeasurableSet {t | 2 * ((L : ℝ) * a + b) ≤
      ‖D.normalizedMomentumPhaseField T cut h L t 0‖ ∧
        H < ‖D.normalizedMomentumPhaseField T cut h L t 0‖} :=
    (measurableSet_le measurable_const hmeas).inter
      (measurableSet_lt measurable_const hmeas)
  have hA' : MeasurableSet ((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
      {t | max H (2 * ((L : ℝ) * a + b)) <
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖})ᶜ) := by
    simpa only [Set.union_comm] using hA
  have hLpA' : MemLp (((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
      {t | max H (2 * ((L : ℝ) * a + b)) <
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖})ᶜ).indicator traffic) 2 P := by
    simpa only [Set.union_comm] using hLpA
  have hIntA' : (∫ x, (((D.normalizedSourcePhaseCurveBadEvent T cut 1 radius K ∪
      {t | max H (2 * ((L : ℝ) * a + b)) <
        ‖D.normalizedMomentumPhaseField T cut h L t 0‖})ᶜ).indicator traffic) x ^ 2 ∂P)
      ≤ CA := by
    simpa only [Set.union_comm] using hIntA
  exact memLp_two_indicator_of_branch_cover hBad
    (fun s hs ↦ twoBranch_cover D hF hw T hcut h L radius K a b H hs) hA' hB
    hLpA' hIntA' hLpB hIntB

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
