import OTSelector.Reconstruction.FinslerOriginalContractiveBirthWindows

/-! Every literal supported birth-window contributor retains its unchanged
original narrow source or reflected target clock band. -/
open Set Function MeasureTheory Matrix Module Manifold
open scoped ENNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

def originalLeftBirthNarrowClockBand (ε : ℝ) (n j i : ℕ) : Set ℝ :=
  {c | c - S.level ∈ clockGridBand (D.lo + birthDyadicShellScale ε n)
    (birthDyadicElapsedScale ε n j / 8) i}

def originalRightBirthNarrowClockBand (ε : ℝ) (n j i : ℕ) : Set ℝ :=
  {c | c - S.level ∈ Ico
    (D.hi - (birthDyadicShellScale ε n +
      ((i : ℝ) + 1) * (birthDyadicElapsedScale ε n j / 8)))
    (D.hi - (birthDyadicShellScale ε n +
      (i : ℝ) * (birthDyadicElapsedScale ε n j / 8)))}

theorem measurableSet_originalLeftBirthNarrowClockBand (ε : ℝ) (n j i : ℕ) :
    MeasurableSet (D.originalLeftBirthNarrowClockBand ε n j i) :=
  measurableSet_Ioc.preimage (measurable_id.sub_const (S.level : ℝ))

theorem measurableSet_originalRightBirthNarrowClockBand (ε : ℝ) (n j i : ℕ) :
    MeasurableSet (D.originalRightBirthNarrowClockBand ε n j i) :=
  measurableSet_Ico.preimage (measurable_id.sub_const (S.level : ℝ))

theorem originalSupportedLeftBirthPhysicalClockWeight_source_mem_band
    (ε cap : ℝ) (n j i ell : ℕ)
    (z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ)
    (hz : D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell z ≠ 0) :
    z.1.1.1 ∈ D.originalLeftBirthNarrowClockBand ε n j i := by
  have hm := D.originalSupportedLeftBirthPhysicalClockWeight_mask_ne_zero ε cap n j i ell z hz
  have hb := (D.originalSupportedLeftBirthPhysicalClockMask_birth ε cap n j i ell z hm).1
  exact D.originalLeftBirthClockMask_source_mem_clockGridBand ε n j i z hb

theorem originalSupportedRightBirthPhysicalClockWeight_target_mem_band
    (ε cap : ℝ) (n j i ell : ℕ)
    (z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ)
    (hz : D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell z ≠ 0) :
    z.1.1.2 ∈ D.originalRightBirthNarrowClockBand ε n j i := by
  have hm := D.originalSupportedRightBirthPhysicalClockWeight_mask_ne_zero ε cap n j i ell z hz
  have hb := (D.originalSupportedRightBirthPhysicalClockMask_birth ε cap n j i ell z hm).1
  exact D.originalRightBirthClockMask_target_mem_reflectedClockBand ε n j i z hb

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
