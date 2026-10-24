import OTSelector.Reconstruction.OriginalOldRegularClockLegs
import OTSelector.Reconstruction.OriginalClockTrafficRegions

/-! The actual original clock masks themselves imply compact regular strips
and fixed old-leg gaps. These are consequences of the original paired clocks,
not extra eligibility or geometric hypotheses on a chosen contributor. -/
open Set
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 900000

/-- Exact literal source birth/regular classification. -/
theorem originalClockTrafficRegionIndex_eq_one_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 1 ↔
      z.2 - z.1.1.1 ≤ z.1.1.2 - z.2 ∧
      z.2 - z.1.1.1 ≤ z.1.1.1 - l ∧ ε < z.1.1.1 - l := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all
  linarith

/-- Exact literal source old/regular classification. -/
theorem originalClockTrafficRegionIndex_eq_three_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 3 ↔
      z.2 - z.1.1.1 ≤ z.1.1.2 - z.2 ∧
      z.1.1.1 - l < z.2 - z.1.1.1 ∧ ε < z.2 - l := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all
  constructor <;> linarith

/-- Exact literal target birth/regular classification. -/
theorem originalClockTrafficRegionIndex_eq_five_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 5 ↔
      z.1.1.2 - z.2 < z.2 - z.1.1.1 ∧
      z.1.1.2 - z.2 ≤ h - z.1.1.2 ∧ ε < h - z.1.1.2 := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all
  constructor <;> linarith

/-- Exact literal target old/regular classification. -/
theorem originalClockTrafficRegionIndex_eq_seven_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 7 ↔
      z.1.1.2 - z.2 < z.2 - z.1.1.1 ∧
      h - z.1.1.2 < z.1.1.2 - z.2 ∧ ε < h - z.2 := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Every actual regular clock mask is confined to the same deterministic
compact strip, using only the original legal edge's clock separation. -/
theorem original_regularClock_mask_compact_strip {q : ℕ} {l h ε gap : ℝ}
    {i : Fin 8} (hi : i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 7)
    {z : PhysicalPairPalmMark (Fin q) × ℝ}
    (hmask : originalClockTrafficRegionMask l h ε i z ≠ 0)
    (hgap : gap ≤ z.1.1.2 - z.1.1.1) :
    l + min ε (gap / 2) ≤ z.2 ∧ z.2 ≤ h - min ε (gap / 2) := by
  obtain ⟨hl, hh, ha, hb, hidx⟩ := (originalClockTrafficRegionMask_ne_zero_iff l h ε i z).mp hmask
  have he := min_le_left ε (gap / 2)
  have hg := min_le_right ε (gap / 2)
  rcases hi with rfl | rfl | rfl | rfl
  · obtain ⟨hn, _, hr⟩ := (originalClockTrafficRegionIndex_eq_one_iff l h ε z).mp hidx
    constructor <;> linarith
  · obtain ⟨hn, ho, hr⟩ := (originalClockTrafficRegionIndex_eq_three_iff l h ε z).mp hidx
    constructor <;> linarith
  · obtain ⟨hn, _, hr⟩ := (originalClockTrafficRegionIndex_eq_five_iff l h ε z).mp hidx
    constructor <;> linarith
  · obtain ⟨hn, ho, hr⟩ := (originalClockTrafficRegionIndex_eq_seven_iff l h ε z).mp hidx
    constructor <;> linarith

/-- The actual two old/regular masks internally give a positive lower bound
on both physical clock legs; no separate leg-gap premise is needed downstream. -/
theorem original_oldRegularClock_mask_leg_bounds {q : ℕ} {l h ε gap : ℝ}
    {i : Fin 8} (hi : i = 3 ∨ i = 7)
    {z : PhysicalPairPalmMark (Fin q) × ℝ}
    (hmask : originalClockTrafficRegionMask l h ε i z ≠ 0)
    (hgap : gap ≤ z.1.1.2 - z.1.1.1) :
    min ε gap / 2 ≤ z.2 - z.1.1.1 ∧ min ε gap / 2 ≤ z.1.1.2 - z.2 := by
  obtain ⟨_, _, _, _, hidx⟩ := (originalClockTrafficRegionMask_ne_zero_iff l h ε i z).mp hmask
  have he := min_le_left ε gap
  have hg := min_le_right ε gap
  rcases hi with rfl | rfl
  · obtain ⟨hn, ho, hr⟩ := (originalClockTrafficRegionIndex_eq_three_iff l h ε z).mp hidx
    have hb := source_oldRegular_clock_leg_bounds hn ho hr hgap
    constructor <;> linarith [hb.1, hb.2]
  · obtain ⟨hn, ho, hr⟩ := (originalClockTrafficRegionIndex_eq_seven_iff l h ε z).mp hidx
    have hb := target_oldRegular_clock_leg_bounds hn.le ho hr hgap
    constructor <;> linarith [hb.1, hb.2]

end OTSelector.Reconstruction
