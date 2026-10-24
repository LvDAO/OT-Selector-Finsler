import OTSelector.Reconstruction.FinslerOriginalCommonCutLegalCycle
import OTSelector.LinearAlgebra.Matrix.ComplianceCongruenceCovariance

/-!
# Actual original momentum control in an anisotropic phase frame

The original legal kinetic cycle is preserved exactly by the same invertible phase change
applied to its actual path positions and momenta. Normalized positive-leg lower bounds then
give the quantitative phase estimate, with the same original additive cycle defect.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The anisotropic common-cut estimate uses the unchanged original kinetic cycle and actual
Finsler kernel. The four lower bounds are the intermediate local scale conditions which
must be supplied by the actual smooth-pole geometry, rather than final external assumptions. -/
theorem original_normalized_commonCut_legalCycle_momentum_norm_sq_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] (x₁ x₂ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m₁ m₂ : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c D₀ h : ℝ}
    (ha₁ : m₁.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.1 ∈ μ.support)
    (hb₁ : m₁.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.2 ∈ ν.support)
    (ha₂ : m₂.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.1 ∈ μ.support)
    (hb₂ : m₂.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.2 ∈ ν.support)
    (hac₁ : m₁.1.1 < c) (hcb₁ : c < m₁.1.2)
    (hac₂ : m₂.1.1 < c) (hcb₂ : c < m₂.1.2) (hh : 0 < h) (hD₀ : 0 ≤ D₀)
    (hlegA₁ : (T * originalSeedClockCompliance S w m₁.1.1 c * Tᵀ - h • 1).PosSemidef)
    (hlegB₁ : (T * originalSeedClockCompliance S w c m₁.1.2 * Tᵀ - h • 1).PosSemidef)
    (hlegA₂ : (T * originalSeedClockCompliance S w m₂.1.1 c * Tᵀ - h • 1).PosSemidef)
    (hlegB₂ : (T * originalSeedClockCompliance S w c m₂.1.2 * Tᵀ - h • 1).PosSemidef)
    (hcycle : D.originalFocalKinetic gap m₁.1.1 m₁.1.2 m₁.2 +
      D.originalFocalKinetic gap m₂.1.1 m₂.1.2 m₂.2 ≤
      D.originalFocalKinetic gap m₁.1.1 m₂.1.2 (x₂ + m₂.2 - x₁) +
        D.originalFocalKinetic gap m₂.1.1 m₁.1.2 (x₁ + m₁.2 - x₂) + D₀) :
    ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m₁ -
      (Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m₂‖ ^ 2 ≤
      (finrank ℝ S.covector.ker : ℝ) / h ^ 2 *
        ‖T *ᵥ (originalSeedCompletePath S w x₂ m₂ c -
          originalSeedCompletePath S w x₁ m₁ c)‖ ^ 2 + 2 * D₀ / h := by
  have hrec := D.original_commonCut_legalCycle_recast hF hw hbounds x₁ x₂ m₁ m₂
    ha₁ hb₁ ha₂ hb₂ hac₁ hcb₁ hac₂ hcb₂ hcycle
  have htrans := legalTwoCycle_compliance_congruence T
    (originalSeedClockCompliance S w m₁.1.1 c) (originalSeedClockCompliance S w c m₁.1.2)
    (originalSeedClockCompliance S w m₂.1.1 c) (originalSeedClockCompliance S w c m₂.1.2)
    (originalSeedPairMomentum S w m₁) (originalSeedPairMomentum S w m₂)
    (originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c) D₀ hrec
  simpa only [Fintype.card_fin] using
    legalTwoCycle_momentum_norm_sq_le_of_leg_lower_bounds hh hD₀
      hlegA₁ hlegB₁ hlegA₂ hlegB₂
      ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m₁)
      ((Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m₂)
      (T *ᵥ (originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c))
      htrans

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
