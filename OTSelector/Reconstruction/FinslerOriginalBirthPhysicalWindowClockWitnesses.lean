import OTSelector.Reconstruction.FinslerOriginalSupportedBirthWindowWeights

/-! Nonzero literal occupied birth-window weights internally produce their
actual unit-clock parameter in the unchanged physical affine window. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- Positive left occupied weight gives its genuine affine physical-clock witness. -/
theorem originalSupportedLeftBirthPhysicalClockWeight_clock_witness
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell z ≠ 0) :
    ∃ r ∈ Icc (0 : ℝ) 1,
      z.2 = D.originalLeftBirthPhysicalClockReference ε cap n j i ell +
        birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j) * r := by
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
  have hs : 0 < birthDyadicElapsedScale ε n j :=
    div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hwidth : 0 < width := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hf := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp
      (D.originalSupportedLeftBirthPhysicalClockWeight_mask_ne_zero ε cap n j i ell z hz)
  have hc := D.originalLeftBirthPhysicalClockMask_clock_mem ε cap n j i ell z hf.2.2
  change ref < z.2 ∧ z.2 ≤ ref + width at hc
  refine ⟨(z.2 - ref) / width, ⟨div_nonneg (by linarith [hc.1]) hwidth.le,
    (div_le_iff₀ hwidth).mpr (by linarith [hc.2])⟩, ?_⟩
  change z.2 = ref + width * ((z.2 - ref) / width)
  field_simp
  ring

/-- The reflected right weight gives its actual negatively oriented window clock. -/
theorem originalSupportedRightBirthPhysicalClockWeight_clock_witness
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell z ≠ 0) :
    ∃ r ∈ Icc (0 : ℝ) 1,
      z.2 = D.originalRightBirthPhysicalClockReference ε cap n j i ell +
        (-birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)) * r := by
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
  have hs : 0 < birthDyadicElapsedScale ε n j :=
    div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hwidth : 0 < width := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hf := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp
      (D.originalSupportedRightBirthPhysicalClockWeight_mask_ne_zero ε cap n j i ell z hz)
  have hc := D.originalRightBirthPhysicalClockMask_clock_mem ε cap n j i ell z hf.2.2
  change ref - width ≤ z.2 ∧ z.2 < ref at hc
  refine ⟨(ref - z.2) / width, ⟨div_nonneg (by linarith [hc.2]) hwidth.le,
    (div_le_iff₀ hwidth).mpr (by linarith [hc.1])⟩, ?_⟩
  change z.2 = ref + (-width) * ((ref - z.2) / width)
  field_simp
  ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
