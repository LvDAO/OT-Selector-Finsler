import OTSelector.Reconstruction.FinslerOriginalBirthNormalizedLegClockInputs
import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes
import OTSelector.Reconstruction.FinslerOriginalCommonCutCompliance

/-! The original half-open occupation multiplies the literal supported window
mask. Nonzero weights retain the same paired mark and both original clocks. -/
open Set Function MeasureTheory Matrix Module Manifold
open scoped ENNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "MarkClock" => PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ

/-- Actual original occupation in one supported closer-source birth window. -/
def originalSupportedLeftBirthPhysicalClockWeight (ε cap : ℝ) (n j i ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
    D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z

/-- Actual original occupation in the reflected closer-target birth window. -/
def originalSupportedRightBirthPhysicalClockWeight (ε cap : ℝ) (n j i ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
    D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z

theorem measurable_originalSupportedLeftBirthPhysicalClockWeight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) :=
  (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
    (D.measurable_originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell)

theorem measurable_originalSupportedRightBirthPhysicalClockWeight
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (ε cap : ℝ) (n j i ell : ℕ) :
    Measurable (D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell) :=
  (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
    (D.measurable_originalSupportedRightBirthPhysicalClockMask ε cap n j i ell)

theorem originalSupportedLeftBirthPhysicalClockWeight_mask_ne_zero
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell z ≠ 0) :
    D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell z ≠ 0 := by
  exact (mul_ne_zero_iff.mp hz).2

theorem originalSupportedRightBirthPhysicalClockWeight_mask_ne_zero
    (ε cap : ℝ) (n j i ell : ℕ) (z : MarkClock)
    (hz : D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell z ≠ 0) :
    D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell z ≠ 0 := by
  exact (mul_ne_zero_iff.mp hz).2

/-- Genuine physical compliance legs give precisely the existing node predicate. -/
theorem mem_normalizedMomentumPhaseEligibleEdges_of_clockCompliance
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (ref h : ℝ) (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : e.1.2 ∈ D.sourcePhaseClocks (ref - S.level))
    (hb : e.2.2 ∈ D.targetPhaseClocks (ref - S.level))
    (hμ : e.1.2 ∈ μ.support) (hν : e.2.2 ∈ ν.support)
    (hleft : (T * originalSeedClockCompliance S w e.1.2 ref * Tᵀ - h • 1).PosSemidef)
    (hright : (T * originalSeedClockCompliance S w ref e.2.2 * Tᵀ - h • 1).PosSemidef) :
    e ∈ D.normalizedMomentumPhaseEligibleEdges T (ref - S.level) h := by
  refine ⟨ha, hb, hμ, hν, ?_, ?_⟩
  · simpa only [sourcePhaseLeg, indicator_of_mem ha, originalSeedClockCompliance] using hleft
  · simpa only [targetPhaseLeg, indicator_of_mem hb, originalSeedClockCompliance] using hright

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
