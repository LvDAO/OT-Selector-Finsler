import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIntrinsicClockKernel
import OTSelector.Reconstruction.StrictClockWindowCover

/-!
# Common strict windows in the same original calibrated interior

Any two forward target choices whose three clocks lie in the same actual
calibrated interior fit one rational strict clock window compactly inside that
interior. Their original target clocks need no mutual ordering.
-/

open Set Function Module Manifold MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}

/-- The same original calibrated time interval contains one compact rational
strict window for every possible split between two strictly forward targets. -/
theorem exists_original_calibrationInterior_window_for_two_targets
    (hF : F.IsSmoothStronglyConvex)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hw : w ∈ S.labels)
    {ι : Type*} [Fintype ι] {x y z : (ι → ℝ) × ℝ}
    (hx : x.2 - S.level ∈ interior (S.calibrationTimes w))
    (hy : y.2 - S.level ∈ interior (S.calibrationTimes w))
    (hz : z.2 - S.level ∈ interior (S.calibrationTimes w))
    (hxy : x.2 < y.2) (hxz : x.2 < z.2) :
    ∃ q : RationalScalarPairWindow,
      Icc ((q.val.1 : ℝ) - S.level) ((q.val.2.1 : ℝ) - S.level) ⊆
        interior (S.calibrationTimes w) ∧
      (x, y) ∈ physicalSceneStrictClockRegion q ∧
      (x, z) ∈ physicalSceneStrictClockRegion q := by
  let mn := min (x.2 - S.level) (min (y.2 - S.level) (z.2 - S.level))
  let mx := max (x.2 - S.level) (max (y.2 - S.level) (z.2 - S.level))
  have hmn : mn ∈ interior (S.calibrationTimes w) := by
    rcases min_choice (x.2 - S.level) (min (y.2 - S.level) (z.2 - S.level)) with h | h
    · simpa only [mn, h] using hx
    · rcases min_choice (y.2 - S.level) (z.2 - S.level) with h' | h'
      · simpa only [mn, h, h'] using hy
      · simpa only [mn, h, h'] using hz
  have hmx : mx ∈ interior (S.calibrationTimes w) := by
    rcases max_choice (x.2 - S.level) (max (y.2 - S.level) (z.2 - S.level)) with h | h
    · simpa only [mx, h] using hx
    · rcases max_choice (y.2 - S.level) (z.2 - S.level) with h' | h'
      · simpa only [mx, h, h'] using hy
      · simpa only [mx, h, h'] using hz
  obtain ⟨l, r, hmlr, hlr⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hmn)
  obtain ⟨a, hla, ham⟩ := exists_between hmlr.1
  have ha : a ∈ interior (S.calibrationTimes w) := hlr ⟨hla, ham.trans hmlr.2⟩
  obtain ⟨l', r', hmlr', hlr'⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hmx)
  obtain ⟨b, hmb, hbr⟩ := exists_between hmlr'.2
  have hb : b ∈ interior (S.calibrationTimes w) := hlr' ⟨hmlr'.1.trans hmb, hbr⟩
  have hxmn : mn ≤ x.2 - S.level := min_le_left _ _
  have hymn : mn ≤ y.2 - S.level := (min_le_right _ _).trans (min_le_left _ _)
  have hzmn : mn ≤ z.2 - S.level := (min_le_right _ _).trans (min_le_right _ _)
  have hxmx : x.2 - S.level ≤ mx := le_max_left _ _
  have hymx : y.2 - S.level ≤ mx := (le_max_left _ _).trans (le_max_right _ _)
  have hzmx : z.2 - S.level ≤ mx := (le_max_right _ _).trans (le_max_right _ _)
  have hxI : x.2 ∈ Ioo (a + S.level) (b + S.level) := ⟨by linarith, by linarith⟩
  have hyI : y.2 ∈ Ioo (a + S.level) (b + S.level) := ⟨by linarith, by linarith⟩
  have hzI : z.2 ∈ Ioo (a + S.level) (b + S.level) := ⟨by linarith, by linarith⟩
  obtain ⟨q, hql, hqr, hqxy, hqxz⟩ :=
    exists_strictClock_window_for_two_targets hxI hyI hzI hxy hxz
  refine ⟨q, ?_, hqxy, hqxz⟩
  intro t ht
  apply (original_calibrationInterior_ordConnected hF hu hw).out ha hb
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

end OTSelector.Reconstruction
