import OTSelector.Reconstruction.FinslerOriginalClockOccupationPathMoment
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Eight literal original-clock regions separate source/target birth and old
traffic, and focal/regular positions. The full original occupation is the
finite region sum almost everywhere in its unchanged physical clock. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- Region codes 0--3 are source-side: birth-focal, birth-regular,
old-focal, old-regular. Codes 4--7 are the corresponding target-side regions.
The nearer clock endpoint chooses the side; ties belong to the source. -/
def originalClockTrafficRegionIndex {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) : Fin 8 :=
  if z.2 - z.1.1.1 ≤ z.1.1.2 - z.2 then
    if z.2 - z.1.1.1 ≤ z.1.1.1 - l then
      if z.1.1.1 - l ≤ ε then 0 else 1
    else if z.2 - l ≤ ε then 2 else 3
  else
    if z.1.1.2 - z.2 ≤ h - z.1.1.2 then
      if h - z.1.1.2 ≤ ε then 4 else 5
    else if h - z.2 ≤ ε then 6 else 7

theorem measurable_originalClockTrafficRegionIndex {q : ℕ} (l h ε : ℝ) :
    Measurable (originalClockTrafficRegionIndex (q := q) l h ε) := by
  unfold originalClockTrafficRegionIndex
  apply Measurable.ite (measurableSet_le (measurable_snd.sub measurable_fst.fst.fst)
    (measurable_fst.fst.snd.sub measurable_snd))
  · apply Measurable.ite (measurableSet_le (measurable_snd.sub measurable_fst.fst.fst)
      (measurable_fst.fst.fst.sub_const l))
    · exact Measurable.ite (measurableSet_le (measurable_fst.fst.fst.sub_const l)
        measurable_const) measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le (measurable_snd.sub_const l)
        measurable_const) measurable_const measurable_const
  · apply Measurable.ite (measurableSet_le (measurable_fst.fst.snd.sub measurable_snd)
      (measurable_const.sub measurable_fst.fst.snd))
    · exact Measurable.ite (measurableSet_le (measurable_const.sub measurable_fst.fst.snd)
        measurable_const) measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le (measurable_const.sub measurable_snd)
        measurable_const) measurable_const measurable_const

/-- The literal region mask retains both original clocks and strict interior
physical times. Removing the single source time changes no clock integral. -/
def originalClockTrafficRegionMask {q : ℕ} (l h ε : ℝ) (i : Fin 8)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) : ℝ≥0∞ :=
  {z | l < z.1.1.1 ∧ z.1.1.2 < h ∧ z.1.1.1 < z.2 ∧ z.2 < z.1.1.2 ∧
    originalClockTrafficRegionIndex l h ε z = i}.indicator (fun _ ↦ 1) z

theorem measurable_originalClockTrafficRegionMask {q : ℕ} (l h ε : ℝ) (i : Fin 8) :
    Measurable (originalClockTrafficRegionMask (q := q) l h ε i) := by
  apply measurable_const.indicator
  exact (measurableSet_lt measurable_const measurable_fst.fst.fst).inter
    ((measurableSet_lt measurable_fst.fst.snd measurable_const).inter
      ((measurableSet_lt measurable_fst.fst.fst measurable_snd).inter
        ((measurableSet_lt measurable_snd measurable_fst.fst.snd).inter
          (measurableSet_eq_fun (measurable_originalClockTrafficRegionIndex l h ε) measurable_const))))

theorem originalClockTrafficRegionMask_le_one {q : ℕ} (l h ε : ℝ) (i : Fin 8)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) : originalClockTrafficRegionMask l h ε i z ≤ 1 := by
  unfold originalClockTrafficRegionMask
  simp only [Set.indicator]
  split_ifs <;> simp

/-- Every original occupied strict-interior clock belongs to one and only one
of the actual eight regions, without choosing or changing an edge. -/
theorem sum_originalClockTrafficRegionMask {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ)
    (hl : l < z.1.1.1) (hh : z.1.1.2 < h)
    (ha : z.1.1.1 < z.2) (hb : z.2 < z.1.1.2) :
    (∑ i : Fin 8, originalClockTrafficRegionMask l h ε i z) = 1 := by
  classical
  simp only [originalClockTrafficRegionMask, hl, hh, ha, hb, true_and,
    Set.indicator, mem_ofPred_eq]
  simp

/-- Exact source birth/focal classification, used by the original dyadic birth masks. -/
theorem originalClockTrafficRegionIndex_eq_zero_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 0 ↔
      z.2 - z.1.1.1 ≤ z.1.1.2 - z.2 ∧
      z.2 - z.1.1.1 ≤ z.1.1.1 - l ∧ z.1.1.1 - l ≤ ε := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all

/-- Exact target birth/focal classification, with the original target clock. -/
theorem originalClockTrafficRegionIndex_eq_four_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 4 ↔
      z.1.1.2 - z.2 < z.2 - z.1.1.1 ∧
      z.1.1.2 - z.2 ≤ h - z.1.1.2 ∧ h - z.1.1.2 ≤ ε := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all
  linarith

/-- Region support is an exact condition on the unchanged paired clocks and time. -/
theorem originalClockTrafficRegionMask_ne_zero_iff {q : ℕ} (l h ε : ℝ) (i : Fin 8)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionMask l h ε i z ≠ 0 ↔
      l < z.1.1.1 ∧ z.1.1.2 < h ∧ z.1.1.1 < z.2 ∧ z.2 < z.1.1.2 ∧
        originalClockTrafficRegionIndex l h ε z = i := by
  classical
  unfold originalClockTrafficRegionMask
  by_cases hz : l < z.1.1.1 ∧ z.1.1.2 < h ∧ z.1.1.1 < z.2 ∧ z.2 < z.1.1.2 ∧
      originalClockTrafficRegionIndex l h ε z = i <;> simp [hz]

/-- Exact source old/focal classification uses the original physical time. -/
theorem originalClockTrafficRegionIndex_eq_two_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 2 ↔
      z.2 - z.1.1.1 ≤ z.1.1.2 - z.2 ∧
      z.1.1.1 - l < z.2 - z.1.1.1 ∧ z.2 - l ≤ ε := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all
  linarith

/-- Exact target old/focal classification uses the original physical time. -/
theorem originalClockTrafficRegionIndex_eq_six_iff {q : ℕ} (l h ε : ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalClockTrafficRegionIndex l h ε z = 6 ↔
      z.1.1.2 - z.2 < z.2 - z.1.1.1 ∧
      h - z.1.1.2 < z.1.1.2 - z.2 ∧ h - z.2 ≤ ε := by
  unfold originalClockTrafficRegionIndex
  split_ifs <;> simp_all
  constructor <;> linarith

end OTSelector.Reconstruction
