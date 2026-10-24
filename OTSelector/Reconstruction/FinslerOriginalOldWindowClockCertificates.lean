import OTSelector.Reconstruction.FinslerOriginalOldPhysicalClockMasks

/-! Actual old-region masks supply positive reference legs and the unchanged
opposite support gap on both sides of the original clock strip. -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff ENNReal
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

/-- The actual old left source leg is comparable to the physical inward shell. -/
theorem originalSupportedOldPhysicalClockMask_left_nearLeg
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (hcapU : cap ≤ 1 / 4)
    (n ell : ℕ) (hell : ell < birthPhysicalClockWindowCount cap) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 0 n ell z ≠ 0) :
    birthDyadicShellScale ε n / 4 ≤
      D.originalOldPhysicalClockReference ε cap 0 n ell - z.1.1.1 ∧
    D.originalOldPhysicalClockReference ε cap 0 n ell - z.1.1.1 ≤
      2 * birthDyadicShellScale ε n := by
  have hs := D.originalSupportedOldPhysicalClockMask_support ε cap 0 n ell z hz
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 2 z).mp hs.2.2.1
  have hold := (originalClockTrafficRegionIndex_eq_two_iff _ _ ε z).mp hr.2.2.2.2
  have h := oldPhysicalClockWindow_reference_nearLeg_bounds hcap hcapU
    (birthDyadicShellScale_pos hε n)
    (show 0 < z.1.1.1 - (D.lo + S.level) by linarith [hr.1]) hold.2.1 hell
    (y := z.1.1.1 - (D.lo + S.level)) (d := z.2 - z.1.1.1) (by
      have heq : z.1.1.1 - (D.lo + S.level) + (z.2 - z.1.1.1) =
          D.originalPhysicalClockInward 0 z := by
        dsimp [originalPhysicalClockInward]
        ring
      rw [heq]
      exact hs.2.2.2.2)
  dsimp [originalOldPhysicalClockReference]
  constructor <;> linarith [h.1, h.2]

/-- The actual old right target leg uses the same shell scale and reflected clock. -/
theorem originalSupportedOldPhysicalClockMask_right_nearLeg
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (hcapU : cap ≤ 1 / 4)
    (n ell : ℕ) (hell : ell < birthPhysicalClockWindowCount cap) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 1 n ell z ≠ 0) :
    birthDyadicShellScale ε n / 4 ≤
      z.1.1.2 - D.originalOldPhysicalClockReference ε cap 1 n ell ∧
    z.1.1.2 - D.originalOldPhysicalClockReference ε cap 1 n ell ≤
      2 * birthDyadicShellScale ε n := by
  have hs := D.originalSupportedOldPhysicalClockMask_support ε cap 1 n ell z hz
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 6 z).mp hs.2.2.1
  have hold := (originalClockTrafficRegionIndex_eq_six_iff _ _ ε z).mp hr.2.2.2.2
  have h := oldPhysicalClockWindow_reference_nearLeg_bounds hcap hcapU
    (birthDyadicShellScale_pos hε n)
    (show 0 < D.hi + S.level - z.1.1.2 by linarith [hr.2.1]) hold.2.1 hell
    (y := D.hi + S.level - z.1.1.2) (d := z.1.1.2 - z.2) (by
      have heq : D.hi + S.level - z.1.1.2 + (z.1.1.2 - z.2) =
          D.originalPhysicalClockInward 1 z := by
        dsimp [originalPhysicalClockInward]
        ring
      rw [heq]
      exact hs.2.2.2.2)
  simp only [originalOldPhysicalClockReference, one_ne_zero, ↓reduceIte]
  constructor <;> linarith [h.1, h.2]

/-- Full original source/target support separation controls the whole opposite
leg at the actual left reference. -/
theorem originalSupportedOldPhysicalClockMask_left_opposite_gap
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (ε cap : ℝ) (n ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 0 n ell z ≠ 0) :
    gap / 2 ≤ z.1.1.2 - D.originalOldPhysicalClockReference ε cap 0 n ell := by
  have hs := D.originalSupportedOldPhysicalClockMask_support ε cap 0 n ell z hz
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 2 z).mp hs.2.2.1
  have hnear := ((originalClockTrafficRegionIndex_eq_two_iff _ _ ε z).mp hr.2.2.2.2).1
  have hgap := hbounds.separated _ hs.1 _ hs.2.1
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hr.2.2.1, hr.2.2.2.1])] at hgap
  have hc := D.originalSupportedOldPhysicalClockMask_left_clock_mem ε cap n ell z hz
  linarith [hc.1]

/-- The right opposite leg retains the true source/target support gap. -/
theorem originalSupportedOldPhysicalClockMask_right_opposite_gap
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (ε cap : ℝ) (n ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 1 n ell z ≠ 0) :
    gap / 2 ≤ D.originalOldPhysicalClockReference ε cap 1 n ell - z.1.1.1 := by
  have hs := D.originalSupportedOldPhysicalClockMask_support ε cap 1 n ell z hz
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 6 z).mp hs.2.2.1
  have hnear := ((originalClockTrafficRegionIndex_eq_six_iff _ _ ε z).mp hr.2.2.2.2).1
  have hgap := hbounds.separated _ hs.1 _ hs.2.1
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hr.2.2.1, hr.2.2.2.1])] at hgap
  have hc := D.originalSupportedOldPhysicalClockMask_right_clock_mem ε cap n ell z hz
  linarith [hc.2]

/-- Every closed old source window remains inside the same actual physical shell. -/
theorem originalOldPhysicalClockWindow_left_inward
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (n ell : ℕ)
    (hell : ell < birthPhysicalClockWindowCount cap) {c : ℝ}
    (hc : c ∈ Icc (D.originalOldPhysicalClockReference ε cap 0 n ell)
      (D.originalOldPhysicalClockReference ε cap 0 n ell +
        oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n))) :
    c - S.level - D.lo ∈ Icc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) := by
  apply oldPhysicalClockWindow_inward_bounds hcap (birthDyadicShellScale_pos hε n) hell
  dsimp [originalOldPhysicalClockReference] at hc
  constructor <;> linarith [hc.1, hc.2]

/-- The reflected target window keeps the same closed inward collar. -/
theorem originalOldPhysicalClockWindow_right_inward
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (n ell : ℕ)
    (hell : ell < birthPhysicalClockWindowCount cap) {c : ℝ}
    (hc : c ∈ Icc (D.originalOldPhysicalClockReference ε cap 1 n ell -
      oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n))
      (D.originalOldPhysicalClockReference ε cap 1 n ell)) :
    D.hi - (c - S.level) ∈ Icc (birthDyadicShellScale ε n) (2 * birthDyadicShellScale ε n) := by
  apply oldPhysicalClockWindow_inward_bounds hcap (birthDyadicShellScale_pos hε n) hell
  simp only [originalOldPhysicalClockReference, one_ne_zero, ↓reduceIte] at hc
  constructor <;> linarith [hc.1, hc.2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
