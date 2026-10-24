import OTSelector.Reconstruction.OriginalClockTrafficPieceIndex
import OTSelector.Reconstruction.OriginalClockTrafficRegions
import OTSelector.Reconstruction.FinslerOriginalBirthClockMaskSupport
import OTSelector.MeasureTheory.DyadicClockShellMasks

/-! # The actual deterministic birth, old and regular original-clock masks -/
open Set Function MeasureTheory Module Manifold
open scoped ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option maxHeartbeats 1000000

/-- A fixed inward/elapsed birth group retains only its actual finite narrow bands. -/
theorem finite_sum_dyadicBirthClockMask_le_one {ε : ℝ} (hε : 0 < ε)
    (n j : ℕ) (p : ℝ × ℝ) :
    (∑ i ∈ Finset.range (dyadicBirthBandCount j), dyadicBirthClockMask ε (n, j, i) p) ≤ 1 := by
  have h : (∑ i ∈ Finset.range (dyadicBirthBandCount j),
      dyadicBirthClockMask ε (n, j, i) p) ≤ dyadicBirthClockRegionMask ε p := by
    calc
      _ ≤ ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
          dyadicBirthClockMask ε (n, j, i) p := ENNReal.le_tsum j
      _ ≤ ∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
          dyadicBirthClockMask ε (n, j, i) p := ENNReal.le_tsum n
      _ = _ := tsum_finiteSum_dyadicBirthClockMask hε p
  apply h.trans
  classical
  by_cases hp : p ∈ dyadicBirthClockRegion ε <;> simp [dyadicBirthClockRegionMask, hp]

set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- Side zero uses the unchanged original source clock; side one uses the target. -/
def originalSidedBirthClockMask (ε : ℝ) (side : Fin 2) (n j i : ℕ) (z : MarkClock) : ℝ≥0∞ :=
  if side = 0 then D.originalLeftBirthClockMask ε n j i z
  else D.originalRightBirthClockMask ε n j i z

/-- Actual physical time measured inward from the selected original endpoint collar. -/
def originalPhysicalClockInward (side : Fin 2) (z : MarkClock) : ℝ :=
  if side = 0 then z.2 - S.level - D.lo else D.hi - (z.2 - S.level)

/-- A focal birth piece keeps its literal finite narrow-clock-band sum. -/
def originalFocalBirthPieceMask (ε : ℝ) (side : Fin 2) (n j : ℕ) (z : MarkClock) : ℝ≥0∞ :=
  originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
    (originalFocalBirthRegionIndex side) z *
      ∑ i ∈ Finset.range (dyadicBirthBandCount j), D.originalSidedBirthClockMask ε side n j i z

/-- A focal old piece uses the actual physical inward clock, rather than a birth clock. -/
def originalFocalOldPieceMask (ε : ℝ) (side : Fin 2) (n : ℕ) (z : MarkClock) : ℝ≥0∞ :=
  originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
    (originalFocalOldRegionIndex side) z *
      dyadicClockShellMask ε n (D.originalPhysicalClockInward side z)

/-- The actual countable family consists of birth groups, old shells and four regular regions. -/
def originalClockTrafficPieceMask (ε : ℝ) : OriginalClockTrafficPieceIndex → MarkClock → ℝ≥0∞
  | .inl (.inl (side, n, j)) => D.originalFocalBirthPieceMask ε side n j
  | .inl (.inr (side, n)) => D.originalFocalOldPieceMask ε side n
  | .inr i => originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalRegularRegionIndex i)

theorem measurable_originalSidedBirthClockMask (ε : ℝ) (side : Fin 2) (n j i : ℕ) :
    Measurable (D.originalSidedBirthClockMask ε side n j i) := by
  unfold originalSidedBirthClockMask
  split_ifs
  · exact D.measurable_originalLeftBirthClockMask ε n j i
  · exact D.measurable_originalRightBirthClockMask ε n j i

theorem measurable_originalPhysicalClockInward (side : Fin 2) :
    Measurable (D.originalPhysicalClockInward side) := by
  unfold originalPhysicalClockInward
  split_ifs
  · exact (measurable_snd.sub_const (S.level : ℝ)).sub_const D.lo
  · exact measurable_const.sub (measurable_snd.sub_const (S.level : ℝ))

theorem measurable_originalFocalBirthPieceMask (ε : ℝ) (side : Fin 2) (n j : ℕ) :
    Measurable (D.originalFocalBirthPieceMask ε side n j) :=
  (measurable_originalClockTrafficRegionMask _ _ ε _).mul
    (Finset.measurable_sum _ (fun i _ ↦ D.measurable_originalSidedBirthClockMask ε side n j i))

theorem measurable_originalFocalOldPieceMask (ε : ℝ) (side : Fin 2) (n : ℕ) :
    Measurable (D.originalFocalOldPieceMask ε side n) :=
  (measurable_originalClockTrafficRegionMask _ _ ε _).mul
    ((measurable_dyadicClockShellMask ε n).comp (D.measurable_originalPhysicalClockInward side))

theorem measurable_originalClockTrafficPieceMask (ε : ℝ) (piece : OriginalClockTrafficPieceIndex) :
    Measurable (D.originalClockTrafficPieceMask ε piece) := by
  rcases piece with (bo | i)
  · rcases bo with (⟨side, n, j⟩ | ⟨side, n⟩)
    · exact D.measurable_originalFocalBirthPieceMask ε side n j
    · exact D.measurable_originalFocalOldPieceMask ε side n
  · exact measurable_originalClockTrafficRegionMask _ _ ε _

theorem finite_sum_originalSidedBirthClockMask_le_one {ε : ℝ} (hε : 0 < ε)
    (side : Fin 2) (n j : ℕ) (z : MarkClock) :
    (∑ i ∈ Finset.range (dyadicBirthBandCount j), D.originalSidedBirthClockMask ε side n j i z) ≤
      1 := by
  by_cases hs : side = 0
  · simpa only [originalSidedBirthClockMask, hs, ↓reduceIte, originalLeftBirthClockMask] using
      finite_sum_dyadicBirthClockMask_le_one hε n j (D.originalLeftBirthClockCoordinates z)
  · simpa only [originalSidedBirthClockMask, hs, ↓reduceIte, originalRightBirthClockMask] using
      finite_sum_dyadicBirthClockMask_le_one hε n j (D.originalRightBirthClockCoordinates z)

/-- Every piece is pointwise bounded by its same unchanged original-region mask. -/
theorem originalClockTrafficPieceMask_le_regionMask {ε : ℝ} (hε : 0 < ε)
    (piece : OriginalClockTrafficPieceIndex) (z : MarkClock) :
    D.originalClockTrafficPieceMask ε piece z ≤
      originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
        (originalClockTrafficPieceRegionIndex piece) z := by
  rcases piece with (bo | i)
  · rcases bo with (⟨side, n, j⟩ | ⟨side, n⟩)
    · exact mul_le_of_le_one_right bot_le
        (D.finite_sum_originalSidedBirthClockMask_le_one hε side n j z)
    · exact mul_le_of_le_one_right bot_le
        (dyadicClockShellMask_le_one ε n (D.originalPhysicalClockInward side z))
  · exact le_rfl

theorem originalClockTrafficPieceMask_le_one {ε : ℝ} (hε : 0 < ε)
    (piece : OriginalClockTrafficPieceIndex) (z : MarkClock) :
    D.originalClockTrafficPieceMask ε piece z ≤ 1 :=
  (D.originalClockTrafficPieceMask_le_regionMask hε piece z).trans
    (originalClockTrafficRegionMask_le_one _ _ ε _ z)

theorem originalClockTrafficPieceMask_ne_zero_region {ε : ℝ} (hε : 0 < ε)
    (piece : OriginalClockTrafficPieceIndex) (z : MarkClock)
    (hz : D.originalClockTrafficPieceMask ε piece z ≠ 0) :
    originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalClockTrafficPieceRegionIndex piece) z ≠ 0 := by
  intro h
  exact hz (le_zero_iff.mp (by simpa only [h] using
    D.originalClockTrafficPieceMask_le_regionMask hε piece z))

/-- A positive birth group internally supplies a genuine original narrow-band contributor. -/
theorem originalFocalBirthPieceMask_ne_zero_support (ε : ℝ) (side : Fin 2) (n j : ℕ)
    (z : MarkClock) (hz : D.originalFocalBirthPieceMask ε side n j z ≠ 0) :
    originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalFocalBirthRegionIndex side) z ≠ 0 ∧
      ∃ i < dyadicBirthBandCount j, D.originalSidedBirthClockMask ε side n j i z ≠ 0 := by
  have hr : originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalFocalBirthRegionIndex side) z ≠ 0 := by
    intro hr
    apply hz
    simp only [originalFocalBirthPieceMask, hr, zero_mul]
  refine ⟨hr, ?_⟩
  by_contra hn
  push Not at hn
  apply hz
  have hs : (∑ i ∈ Finset.range (dyadicBirthBandCount j),
      D.originalSidedBirthClockMask ε side n j i z) = 0 :=
    Finset.sum_eq_zero (fun i hi ↦ hn i (Finset.mem_range.mp hi))
  simp only [originalFocalBirthPieceMask, hs, mul_zero]

/-- A positive old piece remains in its same focal region and actual physical-clock shell. -/
theorem originalFocalOldPieceMask_ne_zero_support (ε : ℝ) (side : Fin 2) (n : ℕ)
    (z : MarkClock) (hz : D.originalFocalOldPieceMask ε side n z ≠ 0) :
    originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalFocalOldRegionIndex side) z ≠ 0 ∧
      D.originalPhysicalClockInward side z ∈
        Ioc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) := by
  constructor
  · intro hr
    apply hz
    simp only [originalFocalOldPieceMask, hr, zero_mul]
  · by_contra hs
    apply hz
    simp only [originalFocalOldPieceMask, dyadicClockShellMask, indicator_of_notMem hs, mul_zero]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
