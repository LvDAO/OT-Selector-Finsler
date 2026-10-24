import OTSelector.Reconstruction.FinslerOriginalOldWindowTraffic

/-! Nonzero literal occupied old-focal-window weights internally produce their
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
theorem originalSupportedLeftOldPhysicalClockWeight_clock_witness
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockWeight ε cap 0 n ell z ≠ 0) :
    ∃ r ∈ Icc (0 : ℝ) 1,
      z.2 = D.originalOldPhysicalClockReference ε cap 0 n ell +
        oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n) * r := by
  let ref := D.originalOldPhysicalClockReference ε cap 0 n ell
  let width := oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)
  have ht : 0 < birthDyadicShellScale ε n := birthDyadicShellScale_pos hε n
  have hwidth : 0 < width := (oldPhysicalClockWindow_spec hcap ht).2.1
  have hm : D.originalSupportedOldPhysicalClockMask ε cap 0 n ell z ≠ 0 :=
    (mul_ne_zero_iff.mp hz).2
  have hc := D.originalSupportedOldPhysicalClockMask_left_clock_mem ε cap n ell z hm
  change ref < z.2 ∧ z.2 ≤ ref + width at hc
  refine ⟨(z.2 - ref) / width, ⟨div_nonneg (by linarith [hc.1]) hwidth.le,
    (div_le_iff₀ hwidth).mpr (by linarith [hc.2])⟩, ?_⟩
  change z.2 = ref + width * ((z.2 - ref) / width)
  field_simp
  ring

/-- The reflected right weight gives its actual negatively oriented window clock. -/
theorem originalSupportedRightOldPhysicalClockWeight_clock_witness
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell z ≠ 0) :
    ∃ r ∈ Icc (0 : ℝ) 1,
      z.2 = D.originalOldPhysicalClockReference ε cap 1 n ell +
        (-oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)) * r := by
  let ref := D.originalOldPhysicalClockReference ε cap 1 n ell
  let width := oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)
  have ht : 0 < birthDyadicShellScale ε n := birthDyadicShellScale_pos hε n
  have hwidth : 0 < width := (oldPhysicalClockWindow_spec hcap ht).2.1
  have hm : D.originalSupportedOldPhysicalClockMask ε cap 1 n ell z ≠ 0 :=
    (mul_ne_zero_iff.mp hz).2
  have hc := D.originalSupportedOldPhysicalClockMask_right_clock_mem ε cap n ell z hm
  change ref - width ≤ z.2 ∧ z.2 < ref at hc
  refine ⟨(ref - z.2) / width, ⟨div_nonneg (by linarith [hc.2]) hwidth.le,
    (div_le_iff₀ hwidth).mpr (by linarith [hc.1])⟩, ?_⟩
  change z.2 = ref + (-width) * ((ref - z.2) / width)
  field_simp
  ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
