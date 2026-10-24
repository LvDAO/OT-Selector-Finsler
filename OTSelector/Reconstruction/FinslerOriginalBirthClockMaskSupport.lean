import OTSelector.Reconstruction.FinslerOriginalBirthClockMasks

/-! # Actual original clock support and physical half-open birth bands -/
open Set Function MeasureTheory Module Manifold
open scoped ContDiff ENNReal BigOperators
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

/-- Literal positive-inward and positive-elapsed meaning of the whole birth mask. -/
theorem originalLeftBirthClockRegionMask_ne_zero_iff (ε : ℝ) (z : MarkClock) :
    D.originalLeftBirthClockRegionMask ε z ≠ 0 ↔
      0 < z.1.1.1 - S.level - D.lo ∧ z.1.1.1 - S.level - D.lo ≤ ε ∧
        0 < z.2 - z.1.1.1 ∧ z.2 - z.1.1.1 ≤ z.1.1.1 - S.level - D.lo :=
  dyadicBirthClockRegionMask_ne_zero_iff ε (D.originalLeftBirthClockCoordinates z)

theorem existsUnique_originalLeftBirthClockCell {ε : ℝ} (hε : 0 < ε)
    {z : MarkClock} (hz : D.originalLeftBirthClockRegionMask ε z ≠ 0) :
    ∃! k : ℕ × ℕ × ℕ, z ∈ D.originalLeftBirthClockCell ε k :=
  existsUnique_dyadicBirthClockCell hε
    ((dyadicBirthClockRegionMask_ne_zero_iff ε (D.originalLeftBirthClockCoordinates z)).mp hz)

/-- Actual inward and elapsed shell bounds, with the genuine finite clock-band index. -/
theorem originalLeftBirthClockMask_clock_bounds
    (ε : ℝ) (n j i : ℕ) (z : MarkClock)
    (hz : D.originalLeftBirthClockMask ε n j i z ≠ 0) :
    let t := birthDyadicShellScale ε n
    let s := birthDyadicElapsedScale ε n j
    (z.1.1.1 - S.level - D.lo) ∈ Ioc t (2 * t) ∧ (z.2 - z.1.1.1) ∈ Ioc s (2 * s) ∧
      z.2 - z.1.1.1 ≤ z.1.1.1 - S.level - D.lo ∧ i < dyadicBirthBandCount j := by
  have h := (D.originalLeftBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Literal positive-inward and positive-elapsed meaning of the whole birth mask. -/
theorem originalRightBirthClockRegionMask_ne_zero_iff (ε : ℝ) (z : MarkClock) :
    D.originalRightBirthClockRegionMask ε z ≠ 0 ↔
      0 < D.hi - (z.1.1.2 - S.level) ∧ D.hi - (z.1.1.2 - S.level) ≤ ε ∧
        0 < z.1.1.2 - z.2 ∧ z.1.1.2 - z.2 ≤ D.hi - (z.1.1.2 - S.level) :=
  dyadicBirthClockRegionMask_ne_zero_iff ε (D.originalRightBirthClockCoordinates z)

theorem existsUnique_originalRightBirthClockCell {ε : ℝ} (hε : 0 < ε)
    {z : MarkClock} (hz : D.originalRightBirthClockRegionMask ε z ≠ 0) :
    ∃! k : ℕ × ℕ × ℕ, z ∈ D.originalRightBirthClockCell ε k :=
  existsUnique_dyadicBirthClockCell hε
    ((dyadicBirthClockRegionMask_ne_zero_iff ε (D.originalRightBirthClockCoordinates z)).mp hz)

/-- Actual inward and elapsed shell bounds, with the genuine finite clock-band index. -/
theorem originalRightBirthClockMask_clock_bounds
    (ε : ℝ) (n j i : ℕ) (z : MarkClock)
    (hz : D.originalRightBirthClockMask ε n j i z ≠ 0) :
    let t := birthDyadicShellScale ε n
    let s := birthDyadicElapsedScale ε n j
    (D.hi - (z.1.1.2 - S.level)) ∈ Ioc t (2 * t) ∧ (z.1.1.2 - z.2) ∈ Ioc s (2 * s) ∧
      z.1.1.2 - z.2 ≤ D.hi - (z.1.1.2 - S.level) ∧ i < dyadicBirthBandCount j := by
  have h := (D.originalRightBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The actual left narrow band is the same original source-clock band used
by the existing dyadic physical mass and finite-band moment estimates. -/
theorem originalLeftBirthClockMask_source_mem_clockGridBand
    (ε : ℝ) (n j i : ℕ) (z : MarkClock)
    (hz : D.originalLeftBirthClockMask ε n j i z ≠ 0) :
    z.1.1.1 - S.level ∈ clockGridBand (D.lo + birthDyadicShellScale ε n)
      (birthDyadicElapsedScale ε n j / 8) i := by
  have h := (D.originalLeftBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  have hc := h.2.2.2.2
  change birthDyadicShellScale ε n + (i : ℝ) * (birthDyadicElapsedScale ε n j / 8) <
      z.1.1.1 - S.level - D.lo ∧ z.1.1.1 - S.level - D.lo ≤
        birthDyadicShellScale ε n + ((i : ℝ) + 1) *
          (birthDyadicElapsedScale ε n j / 8) at hc
  change D.lo + birthDyadicShellScale ε n +
      (i : ℝ) * (birthDyadicElapsedScale ε n j / 8) < z.1.1.1 - S.level ∧
    z.1.1.1 - S.level ≤ D.lo + birthDyadicShellScale ε n +
      ((i : ℝ) + 1) * (birthDyadicElapsedScale ε n j / 8)
  constructor <;> linarith [hc.1, hc.2]

/-- Right inward Ioc bands are exactly reflected physical Ico bands. Both
endpoints are retained with their correct convention, without a null-set premise. -/
theorem originalRightBirthClockMask_target_mem_reflectedClockBand
    (ε : ℝ) (n j i : ℕ) (z : MarkClock)
    (hz : D.originalRightBirthClockMask ε n j i z ≠ 0) :
    z.1.1.2 - S.level ∈ Ico
      (D.hi - (birthDyadicShellScale ε n +
        ((i : ℝ) + 1) * (birthDyadicElapsedScale ε n j / 8)))
      (D.hi - (birthDyadicShellScale ε n +
        (i : ℝ) * (birthDyadicElapsedScale ε n j / 8))) := by
  have h := (D.originalRightBirthClockMask_ne_zero_iff_cell ε n j i z).mp hz
  have hc := h.2.2.2.2
  change birthDyadicShellScale ε n + (i : ℝ) * (birthDyadicElapsedScale ε n j / 8) <
      D.hi - (z.1.1.2 - S.level) ∧ D.hi - (z.1.1.2 - S.level) ≤
        birthDyadicShellScale ε n + ((i : ℝ) + 1) *
          (birthDyadicElapsedScale ε n j / 8) at hc
  constructor <;> linarith [hc.1, hc.2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
