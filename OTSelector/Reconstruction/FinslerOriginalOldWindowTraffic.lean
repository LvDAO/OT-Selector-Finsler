import OTSelector.Reconstruction.FinslerOriginalOldWindowClockCertificates
import OTSelector.Reconstruction.FinslerOriginalCompletePathClockPieces

/-! The exact finite physical old-clock cover reads the same original
complete-path piece, with unchanged physical occupation and matching. -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff ENNReal BigOperators
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

/-- Literal original physical occupation in one supported old-clock window. -/
def originalSupportedOldPhysicalClockWeight (ε cap : ℝ) (side : Fin 2) (n ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
    D.originalSupportedOldPhysicalClockMask ε cap side n ell z

theorem measurable_originalSupportedOldPhysicalClockWeight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (ε cap : ℝ) (side : Fin 2) (n ell : ℕ) :
    Measurable (D.originalSupportedOldPhysicalClockWeight ε cap side n ell) :=
  (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
    (D.measurable_originalSupportedOldPhysicalClockMask ε cap side n ell)

def originalOldWindowAbsoluteTraffic
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (ε cap : ℝ) (side : Fin 2) (n ell : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (D.originalSupportedOldPhysicalClockWeight ε cap side n ell) s

theorem measurable_originalOldWindowAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (ε cap : ℝ) (side : Fin 2) (n ell : ℕ) :
    Measurable (D.originalOldWindowAbsoluteTraffic η ε cap side n ell) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (D.measurable_originalSupportedOldPhysicalClockWeight hF hw ε cap side n ell)

/-- Exact finite physical-clock decomposition of the original supported old
piece in every scene, before any expectation or field event. -/
theorem sum_originalOldWindowAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (side : Fin 2) (n : ℕ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∑ ell : Fin (birthPhysicalClockWindowCount cap),
      D.originalOldWindowAbsoluteTraffic η ε cap side n ell s) =
        D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr (side, n))) s := by
  let d := fun z : MarkClock ↦ originalSeedPathOffset S w z.2 z.1
  let parts := fun ell : Fin (birthPhysicalClockWindowCount cap) ↦
    D.originalSupportedOldPhysicalClockWeight ε cap side n ell
  have hp : ∀ ell, Measurable (parts ell) := fun ell ↦
    D.measurable_originalSupportedOldPhysicalClockWeight hF hw ε cap side n ell
  have hweights (z : MarkClock) : (∑' ell, parts ell z) =
      D.originalClockPieceSupportedWeight ε (.inl (.inr (side, n))) z := by
    have hs : (∑ ell : Fin (birthPhysicalClockWindowCount cap),
        D.originalSupportedOldPhysicalClockMask ε cap side n ell z) =
          originalPairClockSupportMask _ μ ν z * D.originalFocalOldPieceMask ε side n z :=
      (Fin.sum_univ_eq_sum_range (fun ell : ℕ ↦
        D.originalSupportedOldPhysicalClockMask ε cap side n ell z) _).trans
          (D.sum_originalSupportedOldPhysicalClockMask hε hcap side n z)
    rw [tsum_fintype]
    change (∑ ell : Fin (birthPhysicalClockWindowCount cap),
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
        D.originalSupportedOldPhysicalClockMask ε cap side n ell z) = _
    rw [← Finset.mul_sum, hs]
    dsimp [originalClockPieceSupportedWeight, originalClockTrafficPieceWeight,
      originalClockTrafficPieceMask]
    ac_rfl
  have hr := legalMarkedCompletePathTraffic_tsum_weights d
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal parts hp s
  rw [tsum_fintype] at hr
  change (∑ ell : Fin (birthPhysicalClockWindowCount cap),
    legalMarkedCompletePathTraffic _ d _ (parts ell) s) = _
  rw [← hr]
  apply congrArg (fun f ↦ legalMarkedCompletePathTraffic _ d (fun x ↦ ENNReal.ofReal (η x)) f s)
  exact funext hweights

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
