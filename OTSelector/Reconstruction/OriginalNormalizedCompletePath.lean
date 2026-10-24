import OTSelector.Reconstruction.OriginalFocalComplianceOperatorCurve
import OTSelector.LinearAlgebra.Matrix.ComplianceCongruenceCovariance

/-!
# The same normalized phase trajectory is the original full path

The physical path, its unchanged original momentum, and the same compliance
congruence obey the exact normalized phase identity. This is an identity for each
actual edge and does not replace its path, marks, or matching law.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The unchanged full original path splits at any interior reference clock. -/
theorem originalSeedCompletePath_add_clockCompliance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c d : ℝ}
    (ha : m.1.1 - S.level ∈ Ioo D.lo D.hi)
    (hc : c - S.level ∈ Ioo D.lo D.hi) (hd : d - S.level ∈ Ioo D.lo D.hi) :
    originalSeedCompletePath S w x m c +
      originalSeedClockCompliance S w c d *ᵥ originalSeedPairMomentum S w m =
        originalSeedCompletePath S w x m d := by
  change (x + originalSeedClockCompliance S w m.1.1 c *ᵥ _) + _ =
    x + originalSeedClockCompliance S w m.1.1 d *ᵥ _
  rw [add_assoc, ← Matrix.add_mulVec,
    D.originalSeedClockCompliance_add hF hw ha hc hd]

/-- The literal normalized phase evolution equals the same original physical path. -/
theorem originalNormalizedClockMobility_completePath_identity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (hT : IsUnit T.det)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c ell r : ℝ}
    (ha : m.1.1 - S.level ∈ Ioo D.lo D.hi)
    (hc : c - S.level ∈ Ioo D.lo D.hi)
    (hr : c + ell * r - S.level ∈ Ioo D.lo D.hi) :
    T *ᵥ originalSeedCompletePath S w x m c +
      originalNormalizedClockMobility S w T c ell r
        ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m) =
          T *ᵥ originalSeedCompletePath S w x m (c + ell * r) := by
  let _ := Matrix.invertibleOfIsUnitDet T hT
  rw [originalNormalizedClockMobility, matrixPhaseOperator_apply,
    compliance_congruence_path_offset, ← Matrix.mulVec_add,
    D.originalSeedCompletePath_add_clockCompliance hF hw x m ha hc hr]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
