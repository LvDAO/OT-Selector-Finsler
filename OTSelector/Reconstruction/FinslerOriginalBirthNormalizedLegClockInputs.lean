import OTSelector.Reconstruction.FinslerOriginalBirthWindowClockCertificates

/-! Actual supported birth masks supply every scalar endpoint input of the
existing normalized-leg comparison, with fixed constants α=1/2 and β=4. -/
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

/-- The exact scalar inputs for the actual left normalized-leg theorem.
Only the global chosen birth collar is small relative to the original gap. -/
theorem originalSupportedLeftBirthPhysicalClockMask_normalizedLegs_clock_bounds
    {ε cap gap diameter : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hsmall : 8 * ε ≤ gap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    let t := birthDyadicShellScale ε n
    let s := birthDyadicElapsedScale ε n j
    let a := z.1.1.1 - S.level - D.lo
    let r := D.originalLeftBirthPhysicalClockReference ε cap n j i ell - S.level - D.lo
    0 < t ∧ 0 < s ∧ s ≤ t ∧ t / 2 ≤ a ∧ a ≤ r ∧ r ≤ 4 * t ∧
      s / 2 ≤ r - a ∧ r - a ≤ 4 * s ∧
        z.1.1.2 - S.level ∈ Ioo D.lo D.hi ∧
          (S.level : ℝ) + D.lo + 8 * t ≤ z.1.1.2 := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  have hb := D.originalSupportedLeftBirthPhysicalClockMask_birth ε cap n j i ell z hz
  have hbase := birthDyadicClockBand_base_bounds hε n j i hb.2
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs : 0 < s := hbase.1
  have hwid := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hwin := D.originalSupportedLeftBirthPhysicalClockMask_window_inward
    hε hcap n j i ell z hz hell ref ⟨le_rfl, by linarith⟩
  have hband := D.originalLeftBirthClockMask_clock_bounds ε n j i z hb.1
  have hshort := D.originalSupportedLeftBirthPhysicalClockMask_reference_bounds
    hε hcap n j i ell z hz hell
  rcases hshort.2 with ⟨hshortL, hshortU⟩
  have hwinL := hwin.1
  have hsupport := D.originalSupportedLeftBirthPhysicalClockMask_support ε cap n j i ell z hz
  have hfar := D.originalSupportedLeftBirthPhysicalClockMask_opposite_gap
    hbounds ε cap n j i ell z hz
  have hhalf : 2 * t ≤ ε := by
    rw [show t = birthDyadicShellScale ε n from rfl, two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  change 0 < t ∧ 0 < s ∧ s ≤ t ∧ _
  refine ⟨ht, hs, hbase.2.1, ?_, ?_, hwin.2, ?_, ?_, ?_, ?_⟩
  · linarith [hband.1.1]
  · change z.1.1.1 - S.level - D.lo ≤ ref - S.level - D.lo
    change 7 / 8 * s ≤ ref - z.1.1.1 at hshortL
    linarith [hshortL]
  · change s / 2 ≤ (ref - S.level - D.lo) - (z.1.1.1 - S.level - D.lo)
    change 7 / 8 * s ≤ ref - z.1.1.1 at hshortL
    linarith [hshortL]
  · change (ref - S.level - D.lo) - (z.1.1.1 - S.level - D.lo) ≤ 4 * s
    change ref - z.1.1.1 ≤ 17 / 8 * s at hshortU
    linarith [hshortU]
  · exact ⟨by linarith [hsupport.2.2.1, hsupport.2.2.2.1, hsupport.2.2.2.2.1],
      by linarith [hsupport.2.2.2.2.2]⟩
  · change gap / 2 ≤ z.1.1.2 - ref at hfar
    change t ≤ ref - S.level - D.lo at hwinL
    linarith

/-- The reflected original clocks supply the right normalized-leg inputs. -/
theorem originalSupportedRightBirthPhysicalClockMask_normalizedLegs_clock_bounds
    {ε cap gap diameter : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hsmall : 8 * ε ≤ gap)
    (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0)
    (hell : ell < birthPhysicalClockWindowCount cap) :
    let t := birthDyadicShellScale ε n
    let s := birthDyadicElapsedScale ε n j
    let a := D.hi - (z.1.1.2 - S.level)
    let r := D.hi - (D.originalRightBirthPhysicalClockReference ε cap n j i ell - S.level)
    0 < t ∧ 0 < s ∧ s ≤ t ∧ t / 2 ≤ a ∧ a ≤ r ∧ r ≤ 4 * t ∧
      s / 2 ≤ r - a ∧ r - a ≤ 4 * s ∧
        z.1.1.1 - S.level ∈ Ioo D.lo D.hi ∧
          z.1.1.1 ≤ (S.level : ℝ) + D.hi - 8 * t := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  have hb := D.originalSupportedRightBirthPhysicalClockMask_birth ε cap n j i ell z hz
  have hbase := birthDyadicClockBand_base_bounds hε n j i hb.2
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs : 0 < s := hbase.1
  have hwid := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hwin := D.originalSupportedRightBirthPhysicalClockMask_window_inward
    hε hcap n j i ell z hz hell ref ⟨by linarith, le_rfl⟩
  have hband := D.originalRightBirthClockMask_clock_bounds ε n j i z hb.1
  have hshort := D.originalSupportedRightBirthPhysicalClockMask_reference_bounds
    hε hcap n j i ell z hz hell
  rcases hshort.2 with ⟨hshortL, hshortU⟩
  have hwinL := hwin.1
  have hsupport := D.originalSupportedRightBirthPhysicalClockMask_support ε cap n j i ell z hz
  have hfar := D.originalSupportedRightBirthPhysicalClockMask_opposite_gap
    hbounds ε cap n j i ell z hz
  have hhalf : 2 * t ≤ ε := by
    rw [show t = birthDyadicShellScale ε n from rfl, two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  change 0 < t ∧ 0 < s ∧ s ≤ t ∧ _
  refine ⟨ht, hs, hbase.2.1, ?_, ?_, hwin.2, ?_, ?_, ?_, ?_⟩
  · linarith [hband.1.1]
  · change D.hi - (z.1.1.2 - S.level) ≤ D.hi - (ref - S.level)
    change 7 / 8 * s ≤ z.1.1.2 - ref at hshortL
    linarith [hshortL]
  · change s / 2 ≤ (D.hi - (ref - S.level)) - (D.hi - (z.1.1.2 - S.level))
    change 7 / 8 * s ≤ z.1.1.2 - ref at hshortL
    linarith [hshortL]
  · change (D.hi - (ref - S.level)) - (D.hi - (z.1.1.2 - S.level)) ≤ 4 * s
    change z.1.1.2 - ref ≤ 17 / 8 * s at hshortU
    linarith [hshortU]
  · exact ⟨by linarith [hsupport.2.2.1],
      by linarith [hsupport.2.2.2.1, hsupport.2.2.2.2.1, hsupport.2.2.2.2.2]⟩
  · change gap / 2 ≤ ref - z.1.1.1 at hfar
    change t ≤ D.hi - (ref - S.level) at hwinL
    linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
