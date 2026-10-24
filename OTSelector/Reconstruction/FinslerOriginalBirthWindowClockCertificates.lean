import OTSelector.Reconstruction.FinslerOriginalSupportedBirthWindowMasks
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation

/-! Literal supported birth windows produce their scalar geometric inputs.
The original support separation and nearer-endpoint mask give the opposite
leg lower bound; no endpoint eligibility premise is supplied. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
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

/-- The old birth mask and its finite band index are internally retained. -/
theorem originalSupportedLeftBirthPhysicalClockMask_birth
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    D.originalLeftBirthClockMask ε n j i z ≠ 0 ∧ i < dyadicBirthBandCount j := by
  have hf := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  have hb : D.originalLeftBirthClockMask ε n j i z ≠ 0 := by
    intro hn
    exact hf.2.2 (by simp [originalLeftBirthPhysicalClockMask, hn])
  exact ⟨hb, (D.originalLeftBirthClockMask_clock_bounds ε n j i z hb).2.2.2⟩

theorem originalSupportedRightBirthPhysicalClockMask_birth
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    D.originalRightBirthClockMask ε n j i z ≠ 0 ∧ i < dyadicBirthBandCount j := by
  have hf := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  have hb : D.originalRightBirthClockMask ε n j i z ≠ 0 := by
    intro hn
    exact hf.2.2 (by simp [originalRightBirthPhysicalClockMask, hn])
  exact ⟨hb, (D.originalRightBirthClockMask_clock_bounds ε n j i z hb).2.2.2⟩

/-- Exact half-open window membership and the original positive short leg. -/
theorem originalSupportedLeftBirthPhysicalClockMask_reference_bounds
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    z.2 ∈ Ioc (D.originalLeftBirthPhysicalClockReference ε cap n j i ell)
      (D.originalLeftBirthPhysicalClockReference ε cap n j i ell +
        birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)) ∧
      7 / 8 * birthDyadicElapsedScale ε n j ≤
        D.originalLeftBirthPhysicalClockReference ε cap n j i ell - z.1.1.1 ∧
      D.originalLeftBirthPhysicalClockReference ε cap n j i ell - z.1.1.1 ≤
        17 / 8 * birthDyadicElapsedScale ε n j := by
  have hf := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  exact ⟨D.originalLeftBirthPhysicalClockMask_clock_mem ε cap n j i ell z hf.2.2,
    D.originalLeftBirthPhysicalClockReference_elapsed_bounds hε hcap n j i ell z
      (D.originalSupportedLeftBirthPhysicalClockMask_birth ε cap n j i ell z hz).1 hell⟩

theorem originalSupportedRightBirthPhysicalClockMask_reference_bounds
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    z.2 ∈ Ico (D.originalRightBirthPhysicalClockReference ε cap n j i ell -
      birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j))
      (D.originalRightBirthPhysicalClockReference ε cap n j i ell) ∧
      7 / 8 * birthDyadicElapsedScale ε n j ≤
        z.1.1.2 - D.originalRightBirthPhysicalClockReference ε cap n j i ell ∧
      z.1.1.2 - D.originalRightBirthPhysicalClockReference ε cap n j i ell ≤
        17 / 8 * birthDyadicElapsedScale ε n j := by
  have hf := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  exact ⟨D.originalRightBirthPhysicalClockMask_clock_mem ε cap n j i ell z hf.2.2,
    D.originalRightBirthPhysicalClockReference_elapsed_bounds hε hcap n j i ell z
      (D.originalSupportedRightBirthPhysicalClockMask_birth ε cap n j i ell z hz).1 hell⟩

/-- Every clock in the actual compact window stays in the same inward collar. -/
theorem originalSupportedLeftBirthPhysicalClockMask_window_inward
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    ∀ c ∈ Icc (D.originalLeftBirthPhysicalClockReference ε cap n j i ell)
      (D.originalLeftBirthPhysicalClockReference ε cap n j i ell +
        birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)),
      (c - S.level - D.lo) ∈ Icc (birthDyadicShellScale ε n)
        (4 * birthDyadicShellScale ε n) := by
  intro c hc
  exact D.originalLeftBirthPhysicalClockWindow_inward_bounds hε hcap n j i ell
    (D.originalSupportedLeftBirthPhysicalClockMask_birth ε cap n j i ell z hz).2 hell hc

theorem originalSupportedRightBirthPhysicalClockMask_window_inward
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    ∀ c ∈ Icc (D.originalRightBirthPhysicalClockReference ε cap n j i ell -
      birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j))
      (D.originalRightBirthPhysicalClockReference ε cap n j i ell),
      (D.hi - (c - S.level)) ∈ Icc (birthDyadicShellScale ε n)
        (4 * birthDyadicShellScale ε n) := by
  intro c hc
  exact D.originalRightBirthPhysicalClockWindow_inward_bounds hε hcap n j i ell
    (D.originalSupportedRightBirthPhysicalClockMask_birth ε cap n j i ell z hz).2 hell hc

/-- The actual left reference is itself in the unchanged inward collar. -/
theorem originalSupportedLeftBirthPhysicalClockMask_reference_inward
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    (D.originalLeftBirthPhysicalClockReference ε cap n j i ell - S.level - D.lo) ∈
      Icc (birthDyadicShellScale ε n) (4 * birthDyadicShellScale ε n) := by
  have hs : 0 < birthDyadicElapsedScale ε n j :=
    (birthDyadicClockBand_base_bounds hε n j i
      (D.originalSupportedLeftBirthPhysicalClockMask_birth ε cap n j i ell z hz).2).1
  have hwid := (birthPhysicalClockWindow_spec hcap hs).2.1
  exact D.originalSupportedLeftBirthPhysicalClockMask_window_inward
    hε hcap n j i ell z hz hell _ ⟨le_rfl, by linarith⟩

/-- The actual reflected right reference is in the same inward collar. -/
theorem originalSupportedRightBirthPhysicalClockMask_reference_inward
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    (D.hi - (D.originalRightBirthPhysicalClockReference ε cap n j i ell - S.level)) ∈
      Icc (birthDyadicShellScale ε n) (4 * birthDyadicShellScale ε n) := by
  have hs : 0 < birthDyadicElapsedScale ε n j :=
    (birthDyadicClockBand_base_bounds hε n j i
      (D.originalSupportedRightBirthPhysicalClockMask_birth ε cap n j i ell z hz).2).1
  have hwid := (birthPhysicalClockWindow_spec hcap hs).2.1
  exact D.originalSupportedRightBirthPhysicalClockMask_window_inward
    hε hcap n j i ell z hz hell _ ⟨by linarith, le_rfl⟩

/-- The unchanged support gap and nearer-source classification force the full
opposite leg bound at the actual reference clock. -/
theorem originalSupportedLeftBirthPhysicalClockMask_opposite_gap
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    gap / 2 ≤ z.1.1.2 - D.originalLeftBirthPhysicalClockReference ε cap n j i ell := by
  have hf := (D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  have hs := D.originalSupportedLeftBirthPhysicalClockMask_support ε cap n j i ell z hz
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 0 z).mp hf.2.1
  have hnear := ((originalClockTrafficRegionIndex_eq_zero_iff _ _ ε z).mp
    hr.2.2.2.2).1
  have hgap := hbounds.separated _ hs.1 _ hs.2.1
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2.2.2.1, hs.2.2.2.2.1])] at hgap
  have hc := D.originalLeftBirthPhysicalClockMask_clock_mem ε cap n j i ell z hf.2.2
  linarith [hc.1]

theorem originalSupportedRightBirthPhysicalClockMask_opposite_gap
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0) :
    gap / 2 ≤ D.originalRightBirthPhysicalClockReference ε cap n j i ell - z.1.1.1 := by
  have hf := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
    ε cap n j i ell z).mp hz
  have hs := D.originalSupportedRightBirthPhysicalClockMask_support ε cap n j i ell z hz
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 4 z).mp hf.2.1
  have hnear := ((originalClockTrafficRegionIndex_eq_four_iff _ _ ε z).mp
    hr.2.2.2.2).1
  have hgap := hbounds.separated _ hs.1 _ hs.2.1
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2.2.2.1, hs.2.2.2.2.1])] at hgap
  have hc := D.originalRightBirthPhysicalClockMask_clock_mem ε cap n j i ell z hf.2.2
  linarith [hc.2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
