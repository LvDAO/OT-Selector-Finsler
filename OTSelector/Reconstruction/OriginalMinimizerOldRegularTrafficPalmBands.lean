import OTSelector.Reconstruction.FinslerOriginalOldWindowEligibility
import OTSelector.Reconstruction.OriginalSameResidueClockBandEnergyBudget
import OTSelector.Reconstruction.FinslerOriginalEndpointBirthMass
import OTSelector.Reconstruction.OriginalPalmClockBandMass

/-! Literal old-focal occupied masks lie in a cumulative original endpoint band.
The original source or target may approach its focal endpoint arbitrarily. -/
open Set Function MeasureTheory Matrix Module Manifold
open scoped ENNReal ContDiff Topology Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- Every true left old-window contributor has source inward clock strictly
between zero and twice the current shell scale, with its literal clock window. -/
theorem originalSupportedLeftOldPhysicalClockMask_focal_band_support
    (ε cap : ℝ) (n ell : ℕ) (m : PhysicalPairPalmMark (Fin q)) (c : ℝ)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 0 n ell (m,c)≠0) :
    m.1.1-S.level-D.lo∈Ioo 0 (2*birthDyadicShellScale ε n)∧
      c∈Icc (D.originalOldPhysicalClockReference ε cap 0 n ell)
        (D.originalOldPhysicalClockReference ε cap 0 n ell+
          oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)) := by
  have hs:=D.originalSupportedOldPhysicalClockMask_support ε cap 0 n ell (m,c) hz
  have hr:=(originalClockTrafficRegionMask_ne_zero_iff _ _ ε 2 (m,c)).mp hs.2.2.1
  have hc:=D.originalSupportedOldPhysicalClockMask_left_clock_mem ε cap n ell (m,c) hz
  have hshell:=hs.2.2.2.1
  change c-S.level-D.lo∈Ioc _ _ at hshell
  exact ⟨⟨by linarith [hr.1],by linarith [hr.2.2.1,hshell.2]⟩,hc.1.le,hc.2⟩

/-- The reflected true right old-window contributor retains its original
target inward clock and the forward physical clock interval. -/
theorem originalSupportedRightOldPhysicalClockMask_focal_band_support
    (ε cap : ℝ) (n ell : ℕ) (m : PhysicalPairPalmMark (Fin q)) (c : ℝ)
    (hz : D.originalSupportedOldPhysicalClockMask ε cap 1 n ell (m,c)≠0) :
    D.hi-(m.1.2-S.level)∈Ioo 0 (2*birthDyadicShellScale ε n)∧
      c∈Icc (D.originalOldPhysicalClockReference ε cap 1 n ell-
          oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n))
        (D.originalOldPhysicalClockReference ε cap 1 n ell) := by
  have hs:=D.originalSupportedOldPhysicalClockMask_support ε cap 1 n ell (m,c) hz
  have hr:=(originalClockTrafficRegionMask_ne_zero_iff _ _ ε 6 (m,c)).mp hs.2.2.1
  have hc:=D.originalSupportedOldPhysicalClockMask_right_clock_mem ε cap n ell (m,c) hz
  have hshell:=hs.2.2.2.1
  change D.hi-(c-S.level)∈Ioc _ _ at hshell
  exact ⟨⟨by linarith [hr.2.1],by linarith [hr.2.2.2.1,hshell.2]⟩,hc.1,hc.2.le⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
