import OTSelector.Reconstruction.OldFocalPhysicalClockWindows
import OTSelector.Reconstruction.FinslerOriginalClockPieceMasks
import OTSelector.Reconstruction.OriginalPairClockSupportMask

/-! The actual supported old-source and old-target masks have an exact finite
physical-clock cover; no original time endpoints or contributors are discarded. -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- A literal old-region piece retains the two original clock supports and
one finite physical-clock subwindow. Side zero is source, side one is target. -/
def originalSupportedOldPhysicalClockMask (ε cap : ℝ) (side : Fin 2) (n ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  (originalPairClockSupportMask _ μ ν z * D.originalFocalOldPieceMask ε side n z) *
    oldPhysicalClockWindowMask cap (birthDyadicShellScale ε n) ell
      (D.originalPhysicalClockInward side z)

/-- Actual physical reference: the left endpoint on the source side and
right endpoint on the target side. -/
def originalOldPhysicalClockReference (ε cap : ℝ) (side : Fin 2) (n ell : ℕ) : ℝ :=
  if side = 0 then (S.level : ℝ) + D.lo +
    oldPhysicalClockWindowReference cap (birthDyadicShellScale ε n) ell
  else (S.level : ℝ) + D.hi -
    oldPhysicalClockWindowReference cap (birthDyadicShellScale ε n) ell

theorem measurable_originalSupportedOldPhysicalClockMask
    (ε cap : ℝ) (side : Fin 2) (n ell : ℕ) :
    Measurable (D.originalSupportedOldPhysicalClockMask ε cap side n ell) :=
  ((measurable_originalPairClockSupportMask _ μ ν).mul
    (D.measurable_originalFocalOldPieceMask ε side n)).mul
      ((measurable_oldPhysicalClockWindowMask cap _ ell).comp
        (D.measurable_originalPhysicalClockInward side))

theorem originalSupportedOldPhysicalClockMask_le_one {ε : ℝ} (hε : 0 < ε)
    (cap : ℝ) (side : Fin 2) (n ell : ℕ) (z : MarkClock) :
    D.originalSupportedOldPhysicalClockMask ε cap side n ell z ≤ 1 := by
  apply (mul_le_mul' (mul_le_mul' (originalPairClockSupportMask_le_one _ μ ν z)
    (D.originalClockTrafficPieceMask_le_one hε (.inl (.inr (side, n))) z))
    (oldPhysicalClockWindowMask_le_one cap _ ell _)).trans
  simp

/-- A nonzero old window internally supplies actual original supports,
its unchanged old-region classification and its true finite clock window. -/
theorem originalSupportedOldPhysicalClockMask_support
    (ε cap : ℝ) (side : Fin 2) (n ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap side n ell z ≠ 0) :
    z.1.1.1 ∈ μ.support ∧ z.1.1.2 ∈ ν.support ∧
      originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
        (originalFocalOldRegionIndex side) z ≠ 0 ∧
      D.originalPhysicalClockInward side z ∈
        Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) ∧
      D.originalPhysicalClockInward side z ∈
        Ioc (oldPhysicalClockWindowReference cap (birthDyadicShellScale ε n) ell)
          (oldPhysicalClockWindowReference cap (birthDyadicShellScale ε n) ell +
            oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)) := by
  have hf := mul_ne_zero_iff.mp hz
  have hs := mul_ne_zero_iff.mp hf.1
  have hp := mul_ne_zero_iff.mp hs.2
  have hsup := (originalPairClockSupportMask_ne_zero_iff _ μ ν z).mp hs.1
  have hshell : D.originalPhysicalClockInward side z ∈
      Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) := by
    by_contra hn
    exact hp.2 (indicator_of_notMem hn _)
  exact ⟨hsup.1, hsup.2, hp.1, hshell,
    (oldPhysicalClockWindowMask_ne_zero_iff cap _ ell _).mp hf.2⟩

/-- The finite old subwindows sum to the same supported original old piece. -/
theorem sum_originalSupportedOldPhysicalClockMask {ε cap : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap) (side : Fin 2) (n : ℕ) (z : MarkClock) :
    (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      D.originalSupportedOldPhysicalClockMask ε cap side n ell z) =
        originalPairClockSupportMask _ μ ν z * D.originalFocalOldPieceMask ε side n z := by
  let A := originalPairClockSupportMask (finrank ℝ S.covector.ker) μ ν z *
    D.originalFocalOldPieceMask ε side n z
  change (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
    A * oldPhysicalClockWindowMask cap (birthDyadicShellScale ε n) ell
      (D.originalPhysicalClockInward side z)) = A
  rw [← Finset.mul_sum]
  by_cases hA : A = 0
  · simp [hA]
  · have hpiece := (mul_ne_zero_iff.mp hA).2
    have hsh := (mul_ne_zero_iff.mp hpiece).2
    have hx : D.originalPhysicalClockInward side z ∈
        Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) := by
      by_contra hn
      exact hsh (indicator_of_notMem hn _)
    rw [sum_oldPhysicalClockWindowMask hcap (birthDyadicShellScale_pos hε n) hx, mul_one]

/-- The actual left clock lies in its original Ioc physical subwindow. -/
theorem originalSupportedOldPhysicalClockMask_left_clock_mem
    (ε cap : ℝ) (n ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 0 n ell z ≠ 0) :
    z.2 ∈ Ioc (D.originalOldPhysicalClockReference ε cap 0 n ell)
      (D.originalOldPhysicalClockReference ε cap 0 n ell +
        oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)) := by
  have h := (D.originalSupportedOldPhysicalClockMask_support ε cap 0 n ell z hz).2.2.2.2
  simp only [originalPhysicalClockInward, originalOldPhysicalClockReference, ↓reduceIte] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The reflected right window retains its exact Ico orientation. -/
theorem originalSupportedOldPhysicalClockMask_right_clock_mem
    (ε cap : ℝ) (n ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 1 n ell z ≠ 0) :
    z.2 ∈ Ico (D.originalOldPhysicalClockReference ε cap 1 n ell -
      oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n))
      (D.originalOldPhysicalClockReference ε cap 1 n ell) := by
  have h := (D.originalSupportedOldPhysicalClockMask_support ε cap 1 n ell z hz).2.2.2.2
  simp only [originalPhysicalClockInward, originalOldPhysicalClockReference,
    one_ne_zero, ↓reduceIte] at h ⊢
  constructor <;> linarith [h.1, h.2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
