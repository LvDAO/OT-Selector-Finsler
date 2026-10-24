import OTSelector.Reconstruction.FinslerOriginalClockPieceMasks

/-! # The actual countable clock pieces sum to the unchanged eight regions -/
open Set Function MeasureTheory Module Manifold
open scoped ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- The literal focal birth region lies wholly in the corresponding actual birth collar. -/
theorem originalFocalBirthRegionMask_birthRegion_eq_one (ε : ℝ) (side : Fin 2) (z : MarkClock)
    (hz : originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalFocalBirthRegionIndex side) z ≠ 0) :
    (if side = 0 then D.originalLeftBirthClockRegionMask ε z
      else D.originalRightBirthClockRegionMask ε z) = 1 := by
  fin_cases side
  · have ha := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 0 z).mp hz
    have hb := (originalClockTrafficRegionIndex_eq_zero_iff _ _ ε z).mp ha.2.2.2.2
    have hm : D.originalLeftBirthClockCoordinates z ∈ dyadicBirthClockRegion ε := by
      change 0 < z.1.1.1 - S.level - D.lo ∧ z.1.1.1 - S.level - D.lo ≤ ε ∧
        0 < z.2 - z.1.1.1 ∧ z.2 - z.1.1.1 ≤ z.1.1.1 - S.level - D.lo
      exact ⟨by linarith [ha.1], by linarith [hb.2.2],
        by linarith [ha.2.2.1], by linarith [hb.2.1]⟩
    exact indicator_of_mem hm _
  · have ha := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 4 z).mp hz
    have hb := (originalClockTrafficRegionIndex_eq_four_iff _ _ ε z).mp ha.2.2.2.2
    have hm : D.originalRightBirthClockCoordinates z ∈ dyadicBirthClockRegion ε := by
      change 0 < D.hi - (z.1.1.2 - S.level) ∧ D.hi - (z.1.1.2 - S.level) ≤ ε ∧
        0 < z.1.1.2 - z.2 ∧ z.1.1.2 - z.2 ≤ D.hi - (z.1.1.2 - S.level)
      exact ⟨by linarith [ha.2.1], by linarith [hb.2.2],
        by linarith [ha.2.2.2.1], by linarith [hb.2.1]⟩
    exact indicator_of_mem hm _

/-- The old focal region uses the physical inward clock in the original collar. -/
theorem originalFocalOldRegionMask_physicalInward_mem (ε : ℝ) (side : Fin 2) (z : MarkClock)
    (hz : originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalFocalOldRegionIndex side) z ≠ 0) :
    D.originalPhysicalClockInward side z ∈ Ioc 0 ε := by
  fin_cases side
  · have ha := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 2 z).mp hz
    have hb := (originalClockTrafficRegionIndex_eq_two_iff _ _ ε z).mp ha.2.2.2.2
    change 0 < z.2 - S.level - D.lo ∧ z.2 - S.level - D.lo ≤ ε
    exact ⟨by linarith [ha.1, ha.2.2.1], by linarith [hb.2.2]⟩
  · have ha := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 6 z).mp hz
    have hb := (originalClockTrafficRegionIndex_eq_six_iff _ _ ε z).mp ha.2.2.2.2
    change 0 < D.hi - (z.2 - S.level) ∧ D.hi - (z.2 - S.level) ≤ ε
    exact ⟨by linarith [ha.2.1, ha.2.2.2.1], by linarith [hb.2.2]⟩

/-- The birth shell family reconstructs precisely its same original focal-birth region. -/
theorem tsum_originalFocalBirthPieceMask {ε : ℝ} (hε : 0 < ε) (side : Fin 2) (z : MarkClock) :
    (∑' n : ℕ, ∑' j : ℕ, D.originalFocalBirthPieceMask ε side n j z) =
      originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
        (originalFocalBirthRegionIndex side) z := by
  have hsum : (∑' n : ℕ, ∑' j : ℕ, ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      D.originalSidedBirthClockMask ε side n j i z) =
      if side = 0 then D.originalLeftBirthClockRegionMask ε z
        else D.originalRightBirthClockRegionMask ε z := by
    by_cases hs : side = 0
    · simpa only [originalSidedBirthClockMask, hs, ↓reduceIte] using
        D.tsum_finiteSum_originalLeftBirthClockMask hε z
    · simpa only [originalSidedBirthClockMask, hs, ↓reduceIte] using
        D.tsum_finiteSum_originalRightBirthClockMask hε z
  unfold originalFocalBirthPieceMask
  simp_rw [ENNReal.tsum_mul_left]
  rw [hsum]
  by_cases hz : originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalFocalBirthRegionIndex side) z = 0
  · simp only [hz, zero_mul]
  · rw [D.originalFocalBirthRegionMask_birthRegion_eq_one ε side z hz, mul_one]

/-- The physical old-shell family reconstructs precisely its same original focal-old region. -/
theorem tsum_originalFocalOldPieceMask {ε : ℝ} (hε : 0 < ε) (side : Fin 2) (z : MarkClock) :
    (∑' n : ℕ, D.originalFocalOldPieceMask ε side n z) =
      originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
        (originalFocalOldRegionIndex side) z := by
  unfold originalFocalOldPieceMask
  rw [ENNReal.tsum_mul_left, tsum_dyadicClockShellMask hε]
  by_cases hz : originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
      (originalFocalOldRegionIndex side) z = 0
  · simp only [hz, zero_mul]
  · rw [indicator_of_mem (D.originalFocalOldRegionMask_physicalInward_mem ε side z hz),
      Pi.one_apply, mul_one]

/-- The actual countable family is exactly the original eight-region partition at every point. -/
theorem tsum_originalClockTrafficPieceMask {ε : ℝ} (hε : 0 < ε) (z : MarkClock) :
    (∑' piece : OriginalClockTrafficPieceIndex, D.originalClockTrafficPieceMask ε piece z) =
      ∑ i : Fin 8, originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε i z := by
  have hsplit : (∑' piece : OriginalClockTrafficPieceIndex,
      D.originalClockTrafficPieceMask ε piece z) =
      (∑ side : Fin 2, ∑' n : ℕ, ∑' j : ℕ, D.originalFocalBirthPieceMask ε side n j z) +
      (∑ side : Fin 2, ∑' n : ℕ, D.originalFocalOldPieceMask ε side n z) +
      (∑ i : Fin 4, originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε
        (originalRegularRegionIndex i) z) := by
    rw [ENNReal.summable.tsum_sum ENNReal.summable,
      ENNReal.summable.tsum_sum ENNReal.summable]
    simp only [originalClockTrafficPieceMask, ENNReal.tsum_prod', tsum_fintype]
  rw [hsplit]
  simp_rw [D.tsum_originalFocalBirthPieceMask hε, D.tsum_originalFocalOldPieceMask hε]
  exact sum_originalClockRegionIndex_partition (fun i : Fin 8 ↦
    originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε i z)

/-- The actual unchanged half-open occupation speed multiplied by one literal clock piece. -/
def originalClockTrafficPieceWeight (ε : ℝ) (piece : OriginalClockTrafficPieceIndex)
    (z : MarkClock) : ℝ≥0∞ :=
  ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
    D.originalClockTrafficPieceMask ε piece z

theorem measurable_originalClockTrafficPieceWeight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (ε : ℝ) (piece : OriginalClockTrafficPieceIndex) :
    Measurable (D.originalClockTrafficPieceWeight ε piece) :=
  (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
    (D.measurable_originalClockTrafficPieceMask ε piece)

theorem originalClockTrafficPieceWeight_le_occupation {ε : ℝ} (hε : 0 < ε)
    (piece : OriginalClockTrafficPieceIndex) (z : MarkClock) :
    D.originalClockTrafficPieceWeight ε piece z ≤
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ :=
  mul_le_of_le_one_right bot_le (D.originalClockTrafficPieceMask_le_one hε piece z)

/-- The actual occupation-weight family has the same exact pointwise sum as the original regions. -/
theorem tsum_originalClockTrafficPieceWeight {ε : ℝ} (hε : 0 < ε) (z : MarkClock) :
    (∑' piece : OriginalClockTrafficPieceIndex, D.originalClockTrafficPieceWeight ε piece z) =
      ∑ i : Fin 8, ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
        originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε i z := by
  unfold originalClockTrafficPieceWeight
  rw [ENNReal.tsum_mul_left, D.tsum_originalClockTrafficPieceMask hε, Finset.mul_sum]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
