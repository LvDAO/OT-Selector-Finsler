import OTSelector.Reconstruction.FinslerOriginalBirthPhysicalClockMasks
import OTSelector.Reconstruction.OriginalClockTrafficRegions
import OTSelector.Reconstruction.OriginalPairClockSupportMask

/-! Actual birth-window masks retain the original two clock supports, the
nearer-endpoint classification, and the unchanged finite physical window. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
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

/-- The supported closer-source focal birth window, on the literal original pair. -/
def originalSupportedLeftBirthPhysicalClockMask (ε cap : ℝ) (n j i ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  originalPairClockSupportMask _ μ ν z *
    originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε 0 z *
      D.originalLeftBirthPhysicalClockMask ε cap n j i ell z

/-- The supported closer-target focal birth window, with its reflected endpoints. -/
def originalSupportedRightBirthPhysicalClockMask (ε cap : ℝ) (n j i ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  originalPairClockSupportMask _ μ ν z *
    originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε 4 z *
      D.originalRightBirthPhysicalClockMask ε cap n j i ell z

theorem measurable_originalSupportedLeftBirthPhysicalClockMask
    (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell) :=
  ((measurable_originalPairClockSupportMask _ μ ν).mul
    (measurable_originalClockTrafficRegionMask _ _ ε 0)).mul
      (D.measurable_originalLeftBirthPhysicalClockMask ε cap n j i ell)

theorem measurable_originalSupportedRightBirthPhysicalClockMask
    (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell) :=
  ((measurable_originalPairClockSupportMask _ μ ν).mul
    (measurable_originalClockTrafficRegionMask _ _ ε 4)).mul
      (D.measurable_originalRightBirthPhysicalClockMask ε cap n j i ell)

theorem originalSupportedLeftBirthPhysicalClockMask_le_one
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) :
    D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≤ 1 := by
  exact (mul_le_mul' (mul_le_mul' (originalPairClockSupportMask_le_one _ μ ν z)
    (originalClockTrafficRegionMask_le_one _ _ ε 0 z))
      (D.originalLeftBirthPhysicalClockMask_le_one ε cap n j i ell z)).trans_eq (by simp)

theorem originalSupportedRightBirthPhysicalClockMask_le_one
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) :
    D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≤ 1 := by
  exact (mul_le_mul' (mul_le_mul' (originalPairClockSupportMask_le_one _ μ ν z)
    (originalClockTrafficRegionMask_le_one _ _ ε 4 z))
      (D.originalRightBirthPhysicalClockMask_le_one ε cap n j i ell z)).trans_eq (by simp)

/-- Nonzero actual masks expose their original three factors, without an oracle. -/
theorem originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) :
    D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0 ↔
      originalPairClockSupportMask _ μ ν z ≠ 0 ∧
        originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε 0 z ≠ 0 ∧
          D.originalLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0 := by
  simp only [originalSupportedLeftBirthPhysicalClockMask, mul_ne_zero_iff, and_assoc]

theorem originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) :
    D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0 ↔
      originalPairClockSupportMask _ μ ν z ≠ 0 ∧
        originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε 4 z ≠ 0 ∧
          D.originalRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0 := by
  simp only [originalSupportedRightBirthPhysicalClockMask, mul_ne_zero_iff, and_assoc]

/-- The two original support memberships and all strict active-clock bounds. -/
theorem originalSupportedLeftBirthPhysicalClockMask_support
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    z.1.1.1 ∈ μ.support ∧ z.1.1.2 ∈ ν.support ∧
      D.lo + S.level < z.1.1.1 ∧ z.1.1.1 < z.2 ∧
        z.2 < z.1.1.2 ∧ z.1.1.2 < D.hi + S.level := by
  have hf := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  have hs := (originalPairClockSupportMask_ne_zero_iff _ μ ν z).mp hf.1
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 0 z).mp hf.2.1
  exact ⟨hs.1, hs.2, hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.1⟩

theorem originalSupportedRightBirthPhysicalClockMask_support
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    z.1.1.1 ∈ μ.support ∧ z.1.1.2 ∈ ν.support ∧
      D.lo + S.level < z.1.1.1 ∧ z.1.1.1 < z.2 ∧
        z.2 < z.1.1.2 ∧ z.1.1.2 < D.hi + S.level := by
  have hf := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  have hs := (originalPairClockSupportMask_ne_zero_iff _ μ ν z).mp hf.1
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 4 z).mp hf.2.1
  exact ⟨hs.1, hs.2, hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.1⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
