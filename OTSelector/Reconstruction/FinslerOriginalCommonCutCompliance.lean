import OTSelector.Reconstruction.FinslerOriginalCompletePath
import OTSelector.LinearAlgebra.Matrix.FourLegQuadraticVariation

/-!
# Actual original compliance legs at a physical common cut

Every leg here is the integral of the actual original Finsler kernel over unchanged physical
clock endpoints. Splitting at an active clock gives the actual complete path position and
reconstructs its original full displacement; no geometric model is substituted.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual original compliance between two physical clocks in the fixed original basis. -/
def originalSeedClockCompliance (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (a b : ℝ) : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ :=
  ∫ r in (a - S.level)..(b - S.level), originalSeedKernel S w r

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

theorem posDef_originalSeedClockCompliance (hF : F.IsSmoothStronglyConvex)
    (hw : w ∈ S.labels) {a b : ℝ} (ha : a - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : b - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : a < b) :
    (originalSeedClockCompliance S w a b).PosDef :=
  (D.pair_compliance_posDef hF hw ha hb hab).1

/-- Actual compliance splits exactly at any other interior physical clock. -/
theorem originalSeedClockCompliance_add (hF : F.IsSmoothStronglyConvex)
    (hw : w ∈ S.labels) {a c b : ℝ} (ha : a - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hc : c - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : b - (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    originalSeedClockCompliance S w a c + originalSeedClockCompliance S w c b =
      originalSeedClockCompliance S w a b :=
  intervalIntegral.integral_add_adjacent_intervals
    (D.original_kernel_intervalIntegrable hF hw ha hc)
    (D.original_kernel_intervalIntegrable hF hw hc hb)

/-- The actual momentum reconstructs the full unchanged displacement through the original
complete compliance, even when coefficients degenerate at null focal endpoints. -/
theorem originalSeedClockCompliance_mul_momentum (hF : F.IsSmoothStronglyConvex)
    (hw : w ∈ S.labels) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2) :
    originalSeedClockCompliance S w m.1.1 m.1.2 *ᵥ originalSeedPairMomentum S w m = m.2 := by
  let A := originalSeedClockCompliance S w m.1.1 m.1.2
  have hA : A.PosDef := D.posDef_originalSeedClockCompliance hF hw ha hb hab
  let _ := hA.isUnit.invertible
  change A *ᵥ (A⁻¹ *ᵥ m.2) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The original cost is precisely the compliance energy of its own actual momentum. -/
theorem originalSeedPairQuadratic_eq_compliance_momentum (hF : F.IsSmoothStronglyConvex)
    (hw : w ∈ S.labels) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2) :
    matrixQuadratic (originalSeedPairCoefficient S w m.1) m.2 =
      matrixQuadratic (originalSeedClockCompliance S w m.1.1 m.1.2)
        (originalSeedPairMomentum S w m) :=
  (matrixQuadratic_compliance_momentum
    (D.posDef_originalSeedClockCompliance hF hw ha hb hab) m.2).symm

/-- Splitting at a common cut gives exactly the remainder of the unchanged complete path. -/
theorem originalSeedCompletePath_target_eq_cut_add_leg
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c : ℝ}
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hc : c - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2) :
    x + m.2 = originalSeedCompletePath S w x m c +
      originalSeedClockCompliance S w c m.1.2 *ᵥ originalSeedPairMomentum S w m := by
  rw [← D.originalSeedClockCompliance_mul_momentum hF hw m ha hb hab,
    ← D.originalSeedClockCompliance_add hF hw ha hc hb, Matrix.add_mulVec]
  exact (add_assoc x
    (originalSeedClockCompliance S w m.1.1 c *ᵥ originalSeedPairMomentum S w m)
    (originalSeedClockCompliance S w c m.1.2 *ᵥ originalSeedPairMomentum S w m)).symm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
