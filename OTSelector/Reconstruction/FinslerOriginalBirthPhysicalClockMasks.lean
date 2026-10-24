import OTSelector.MeasureTheory.FiniteClockWindowPartition
import OTSelector.Reconstruction.FinslerOriginalBirthClockMaskSupport

/-! Actual original birth masks are split into one fixed finite family of
physical-clock windows, retaining the original band energy and both endpoints. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- The original left birth band with one actual finite physical clock window. -/
def originalLeftBirthPhysicalClockMask (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) : ℝ≥0∞ :=
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  D.originalLeftBirthClockMask ε n j i z *
    birthPhysicalClockWindowMask cap (t + (i : ℝ) * (s / 8) + s) s ell (z.2 - S.level - D.lo)

def originalLeftBirthPhysicalClockReference (ε cap : ℝ) (n j i ell : ℕ) : ℝ :=
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  S.level + D.lo + (t + (i : ℝ) * (s / 8) + s + (ell : ℝ) * birthPhysicalClockWindowWidth cap s)

theorem measurable_originalLeftBirthPhysicalClockMask (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalLeftBirthPhysicalClockMask ε cap n j i ell) :=
  (D.measurable_originalLeftBirthClockMask ε n j i).mul
    ((measurable_birthPhysicalClockWindowMask cap _ _ ell).comp ((measurable_snd.sub measurable_const).sub measurable_const))

theorem originalLeftBirthPhysicalClockMask_le_one (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) :
    D.originalLeftBirthPhysicalClockMask ε cap n j i ell z ≤ 1 := by
  exact (mul_le_mul' (D.originalLeftBirthClockMask_le_one ε n j i z)
    (birthPhysicalClockWindowMask_le_one cap _ _ ell _)).trans_eq (one_mul _)

/-- The fixed finite window sum is exactly this same original band mask. -/
theorem sum_originalLeftBirthPhysicalClockMask {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i : ℕ) (z : MarkClock) :
    (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      D.originalLeftBirthPhysicalClockMask ε cap n j i ell z) =
        D.originalLeftBirthClockMask ε n j i z := by
  by_cases hz : D.originalLeftBirthClockMask ε n j i z = 0
  · simp only [originalLeftBirthPhysicalClockMask, hz, zero_mul, Finset.sum_const_zero]
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let u := t + (i : ℝ) * (s / 8)
  let y := z.1.1.1 - S.level - D.lo
  let d := z.2 - z.1.1.1
  have hc := (D.originalLeftBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  have hy : y ∈ Ioc u (u + s / 8) := by
    have hb := hc.2.2.2.2
    change t + (i : ℝ) * (s / 8) < y ∧ y ≤ t + ((i : ℝ) + 1) * (s / 8) at hb
    constructor <;> dsimp [u] <;> linarith [hb.1, hb.2]
  have hd : d ∈ Ioc s (2 * s) := hc.2.1
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hξ : z.2 - S.level - D.lo = y + d := by dsimp [y, d]; ring
  change (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      D.originalLeftBirthClockMask ε n j i z *
        birthPhysicalClockWindowMask cap (u + s) s ell (z.2 - S.level - D.lo)) = _
  rw [hξ]
  exact sum_birthPhysicalClockWindowMask_on_cell hcap hs hy hd _

/-- The actual physical clock belongs to the stated unchanged compact
window; the right side uses the exact reflected Ico convention. -/
theorem originalLeftBirthPhysicalClockMask_clock_mem (ε cap : ℝ) (n j i ell : ℕ)
    (z : MarkClock) (hz : D.originalLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    z.2 ∈ Ioc (D.originalLeftBirthPhysicalClockReference ε cap n j i ell)
      (D.originalLeftBirthPhysicalClockReference ε cap n j i ell +
        birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)) := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let base := t + (i : ℝ) * (s / 8) + s
  have hw : birthPhysicalClockWindowMask cap base s ell (z.2 - S.level - D.lo) ≠ 0 := by
    intro hw
    apply hz
    change D.originalLeftBirthClockMask ε n j i z *
      birthPhysicalClockWindowMask cap base s ell (z.2 - S.level - D.lo) = 0
    rw [hw, mul_zero]
  have hm : (z.2 - S.level - D.lo) ∈ clockGridBand base (birthPhysicalClockWindowWidth cap s) ell := by
    by_contra hn
    exact hw (indicator_of_notMem hn _)
  change base + (ell : ℝ) * birthPhysicalClockWindowWidth cap s < (z.2 - S.level - D.lo) ∧
    (z.2 - S.level - D.lo) ≤ base + ((ell : ℝ) + 1) * birthPhysicalClockWindowWidth cap s at hm
  change _ ∧ _
  dsimp [originalLeftBirthPhysicalClockReference]
  constructor <;> dsimp [base, t, s] at hm ⊢ <;> linarith [hm.1, hm.2]


/-- The original right birth band with one actual finite physical clock window. -/
def originalRightBirthPhysicalClockMask (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) : ℝ≥0∞ :=
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  D.originalRightBirthClockMask ε n j i z *
    birthPhysicalClockWindowMask cap (t + (i : ℝ) * (s / 8) + s) s ell (D.hi - (z.2 - S.level))

def originalRightBirthPhysicalClockReference (ε cap : ℝ) (n j i ell : ℕ) : ℝ :=
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  S.level + D.hi - (t + (i : ℝ) * (s / 8) + s + (ell : ℝ) * birthPhysicalClockWindowWidth cap s)

theorem measurable_originalRightBirthPhysicalClockMask (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalRightBirthPhysicalClockMask ε cap n j i ell) :=
  (D.measurable_originalRightBirthClockMask ε n j i).mul
    ((measurable_birthPhysicalClockWindowMask cap _ _ ell).comp (measurable_const.sub (measurable_snd.sub measurable_const)))

theorem originalRightBirthPhysicalClockMask_le_one (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock) :
    D.originalRightBirthPhysicalClockMask ε cap n j i ell z ≤ 1 := by
  exact (mul_le_mul' (D.originalRightBirthClockMask_le_one ε n j i z)
    (birthPhysicalClockWindowMask_le_one cap _ _ ell _)).trans_eq (one_mul _)

/-- The fixed finite window sum is exactly this same original band mask. -/
theorem sum_originalRightBirthPhysicalClockMask {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i : ℕ) (z : MarkClock) :
    (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      D.originalRightBirthPhysicalClockMask ε cap n j i ell z) =
        D.originalRightBirthClockMask ε n j i z := by
  by_cases hz : D.originalRightBirthClockMask ε n j i z = 0
  · simp only [originalRightBirthPhysicalClockMask, hz, zero_mul, Finset.sum_const_zero]
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let u := t + (i : ℝ) * (s / 8)
  let y := D.hi - (z.1.1.2 - S.level)
  let d := z.1.1.2 - z.2
  have hc := (D.originalRightBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  have hy : y ∈ Ioc u (u + s / 8) := by
    have hb := hc.2.2.2.2
    change t + (i : ℝ) * (s / 8) < y ∧ y ≤ t + ((i : ℝ) + 1) * (s / 8) at hb
    constructor <;> dsimp [u] <;> linarith [hb.1, hb.2]
  have hd : d ∈ Ioc s (2 * s) := hc.2.1
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hξ : D.hi - (z.2 - S.level) = y + d := by dsimp [y, d]; ring
  change (∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
      D.originalRightBirthClockMask ε n j i z *
        birthPhysicalClockWindowMask cap (u + s) s ell (D.hi - (z.2 - S.level))) = _
  rw [hξ]
  exact sum_birthPhysicalClockWindowMask_on_cell hcap hs hy hd _

/-- The actual physical clock belongs to the stated unchanged compact
window; the right side uses the exact reflected Ico convention. -/
theorem originalRightBirthPhysicalClockMask_clock_mem (ε cap : ℝ) (n j i ell : ℕ)
    (z : MarkClock) (hz : D.originalRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    z.2 ∈ Ico (D.originalRightBirthPhysicalClockReference ε cap n j i ell -
      birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j))
      (D.originalRightBirthPhysicalClockReference ε cap n j i ell) := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let base := t + (i : ℝ) * (s / 8) + s
  have hw : birthPhysicalClockWindowMask cap base s ell (D.hi - (z.2 - S.level)) ≠ 0 := by
    intro hw
    apply hz
    change D.originalRightBirthClockMask ε n j i z *
      birthPhysicalClockWindowMask cap base s ell (D.hi - (z.2 - S.level)) = 0
    rw [hw, mul_zero]
  have hm : (D.hi - (z.2 - S.level)) ∈ clockGridBand base (birthPhysicalClockWindowWidth cap s) ell := by
    by_contra hn
    exact hw (indicator_of_notMem hn _)
  change base + (ell : ℝ) * birthPhysicalClockWindowWidth cap s < (D.hi - (z.2 - S.level)) ∧
    (D.hi - (z.2 - S.level)) ≤ base + ((ell : ℝ) + 1) * birthPhysicalClockWindowWidth cap s at hm
  change _ ∧ _
  dsimp [originalRightBirthPhysicalClockReference]
  constructor <;> dsimp [base, t, s] at hm ⊢ <;> linarith [hm.1, hm.2]

/-- The fixed original reference clock has a uniformly positive elapsed
leg for every original endpoint in this actual narrow birth band. -/
theorem originalLeftBirthPhysicalClockReference_elapsed_bounds {ε cap : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalLeftBirthClockMask ε n j i z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    7 / 8 * birthDyadicElapsedScale ε n j ≤ D.originalLeftBirthPhysicalClockReference ε cap n j i ell - z.1.1.1 ∧
      D.originalLeftBirthPhysicalClockReference ε cap n j i ell - z.1.1.1 ≤ 17 / 8 * birthDyadicElapsedScale ε n j := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let u := t + (i : ℝ) * (s / 8)
  let y := z.1.1.1 - S.level - D.lo
  have hc := (D.originalLeftBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  have hy : y ∈ Ioc u (u + s / 8) := by
    have hb := hc.2.2.2.2
    change t + (i : ℝ) * (s / 8) < y ∧ y ≤ t + ((i : ℝ) + 1) * (s / 8) at hb
    constructor <;> dsimp [u] <;> linarith [hb.1, hb.2]
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hb := birthPhysicalClockWindow_reference_elapsed_bounds hcap hs hy hell
  dsimp [originalLeftBirthPhysicalClockReference]
  dsimp [u, y, t, s] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- The actual entire compact physical clock window stays in the same
original inward collar required by the Finsler birth-geometry producer. -/
theorem originalLeftBirthPhysicalClockWindow_inward_bounds {ε cap : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap) (n j i ell : ℕ)
    (hi : i < dyadicBirthBandCount j) (hell : ell < birthPhysicalClockWindowCount cap)
    {c : ℝ} (hc : c ∈ Icc (D.originalLeftBirthPhysicalClockReference ε cap n j i ell)
      (D.originalLeftBirthPhysicalClockReference ε cap n j i ell +
        birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j))) :
    (c - S.level - D.lo) ∈ Icc (birthDyadicShellScale ε n) (4 * birthDyadicShellScale ε n) := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let u := t + (i : ℝ) * (s / 8)
  have hb := birthDyadicClockBand_base_bounds hε n j i hi
  have hclock : (c - S.level - D.lo) ∈ Icc
      (u + s + (ell : ℝ) * birthPhysicalClockWindowWidth cap s)
      (u + s + ((ell : ℝ) + 1) * birthPhysicalClockWindowWidth cap s) := by
    dsimp [originalLeftBirthPhysicalClockReference] at hc
    constructor <;> dsimp [u, s, t] <;> linarith [hc.1, hc.2]
  exact birthPhysicalClockWindow_inward_bounds hcap hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hell hclock


/-- The fixed original reference clock has a uniformly positive elapsed
leg for every original endpoint in this actual narrow birth band. -/
theorem originalRightBirthPhysicalClockReference_elapsed_bounds {ε cap : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalRightBirthClockMask ε n j i z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    7 / 8 * birthDyadicElapsedScale ε n j ≤ z.1.1.2 - D.originalRightBirthPhysicalClockReference ε cap n j i ell ∧
      z.1.1.2 - D.originalRightBirthPhysicalClockReference ε cap n j i ell ≤ 17 / 8 * birthDyadicElapsedScale ε n j := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let u := t + (i : ℝ) * (s / 8)
  let y := D.hi - (z.1.1.2 - S.level)
  have hc := (D.originalRightBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  have hy : y ∈ Ioc u (u + s / 8) := by
    have hb := hc.2.2.2.2
    change t + (i : ℝ) * (s / 8) < y ∧ y ≤ t + ((i : ℝ) + 1) * (s / 8) at hb
    constructor <;> dsimp [u] <;> linarith [hb.1, hb.2]
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hb := birthPhysicalClockWindow_reference_elapsed_bounds hcap hs hy hell
  dsimp [originalRightBirthPhysicalClockReference]
  dsimp [u, y, t, s] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- The actual entire compact physical clock window stays in the same
original inward collar required by the Finsler birth-geometry producer. -/
theorem originalRightBirthPhysicalClockWindow_inward_bounds {ε cap : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap) (n j i ell : ℕ)
    (hi : i < dyadicBirthBandCount j) (hell : ell < birthPhysicalClockWindowCount cap)
    {c : ℝ} (hc : c ∈ Icc (D.originalRightBirthPhysicalClockReference ε cap n j i ell -
      birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j))
      (D.originalRightBirthPhysicalClockReference ε cap n j i ell)) :
    (D.hi - (c - S.level)) ∈ Icc (birthDyadicShellScale ε n) (4 * birthDyadicShellScale ε n) := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let u := t + (i : ℝ) * (s / 8)
  have hb := birthDyadicClockBand_base_bounds hε n j i hi
  have hclock : (D.hi - (c - S.level)) ∈ Icc
      (u + s + (ell : ℝ) * birthPhysicalClockWindowWidth cap s)
      (u + s + ((ell : ℝ) + 1) * birthPhysicalClockWindowWidth cap s) := by
    dsimp [originalRightBirthPhysicalClockReference] at hc
    constructor <;> dsimp [u, s, t] <;> linarith [hc.1, hc.2]
  exact birthPhysicalClockWindow_inward_bounds hcap hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hell hclock

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
