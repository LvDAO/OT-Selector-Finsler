import OTSelector.Reconstruction.FinslerOriginalCommonCutCompliance
import OTSelector.LinearAlgebra.Matrix.FourLegMomentumBound
import OTSelector.LinearAlgebra.Matrix.PositiveLegInverseQuadratic

/-!
# Original Finsler legal two-cycles in actual common-cut coordinates

The independently produced original kinetic cycle inequality is rewritten in the literal
positive compliance legs of two actual paths at a common active clock.  Both crossed pairs
are legal automatically.  The paired clocks, physical sources, full displacement, and
original additive defect are retained exactly.
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

/-- The original kinetic legal-cycle inequality is exactly the four-positive-leg inequality
of the actual original paths at any common active physical clock. -/
theorem original_commonCut_legalCycle_recast
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (x₁ x₂ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m₁ m₂ : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c D₀ : ℝ}
    (ha₁ : m₁.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.1 ∈ μ.support)
    (hb₁ : m₁.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.2 ∈ ν.support)
    (ha₂ : m₂.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.1 ∈ μ.support)
    (hb₂ : m₂.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.2 ∈ ν.support)
    (hac₁ : m₁.1.1 < c) (hcb₁ : c < m₁.1.2)
    (hac₂ : m₂.1.1 < c) (hcb₂ : c < m₂.1.2)
    (hcycle : D.originalFocalKinetic gap m₁.1.1 m₁.1.2 m₁.2 +
      D.originalFocalKinetic gap m₂.1.1 m₂.1.2 m₂.2 ≤
      D.originalFocalKinetic gap m₁.1.1 m₂.1.2 (x₂ + m₂.2 - x₁) +
        D.originalFocalKinetic gap m₂.1.1 m₁.1.2 (x₁ + m₁.2 - x₂) + D₀) :
    let A₁ := originalSeedClockCompliance S w m₁.1.1 c
    let B₁ := originalSeedClockCompliance S w c m₁.1.2
    let A₂ := originalSeedClockCompliance S w m₂.1.1 c
    let B₂ := originalSeedClockCompliance S w c m₂.1.2
    let p₁ := originalSeedPairMomentum S w m₁
    let p₂ := originalSeedPairMomentum S w m₂
    let δ := originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c
    matrixQuadratic (A₁ + B₁) p₁ + matrixQuadratic (A₂ + B₂) p₂ ≤
      matrixQuadratic (A₁ + B₂)⁻¹ (δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂) +
        matrixQuadratic (A₂ + B₁)⁻¹ (-δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁) + D₀ := by
  have hc : c - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨by linarith [ha₁.1.1], by linarith [hb₁.1.2]⟩
  let A₁ := originalSeedClockCompliance S w m₁.1.1 c
  let B₁ := originalSeedClockCompliance S w c m₁.1.2
  let A₂ := originalSeedClockCompliance S w m₂.1.1 c
  let B₂ := originalSeedClockCompliance S w c m₂.1.2
  let p₁ := originalSeedPairMomentum S w m₁
  let p₂ := originalSeedPairMomentum S w m₂
  let δ := originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c
  have hown₁ : D.originalFocalKinetic gap m₁.1.1 m₁.1.2 m₁.2 =
      matrixQuadratic (A₁ + B₁) p₁ := by
    rw [D.originalFocalKinetic_eq_of_original_support hbounds ha₁ hb₁ (hac₁.trans hcb₁),
      D.originalSeedPairQuadratic_eq_compliance_momentum hF hw m₁ ha₁.1 hb₁.1 (hac₁.trans hcb₁),
      ← D.originalSeedClockCompliance_add hF hw ha₁.1 hc hb₁.1]
  have hown₂ : D.originalFocalKinetic gap m₂.1.1 m₂.1.2 m₂.2 =
      matrixQuadratic (A₂ + B₂) p₂ := by
    rw [D.originalFocalKinetic_eq_of_original_support hbounds ha₂ hb₂ (hac₂.trans hcb₂),
      D.originalSeedPairQuadratic_eq_compliance_momentum hF hw m₂ ha₂.1 hb₂.1 (hac₂.trans hcb₂),
      ← D.originalSeedClockCompliance_add hF hw ha₂.1 hc hb₂.1]
  have hdisp₁ : x₂ + m₂.2 - x₁ = δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂ := by
    rw [D.originalSeedCompletePath_target_eq_cut_add_leg hF hw x₂ m₂ ha₂.1 hc hb₂.1
      (hac₂.trans hcb₂)]
    change (originalSeedCompletePath S w x₂ m₂ c + B₂ *ᵥ p₂) - x₁ = _
    dsimp only [δ, originalSeedCompletePath]
    change ((x₂ + A₂ *ᵥ p₂) + B₂ *ᵥ p₂) - x₁ =
      ((x₂ + A₂ *ᵥ p₂) - (x₁ + A₁ *ᵥ p₁)) + A₁ *ᵥ p₁ + B₂ *ᵥ p₂
    abel
  have hdisp₂ : x₁ + m₁.2 - x₂ = -δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁ := by
    rw [D.originalSeedCompletePath_target_eq_cut_add_leg hF hw x₁ m₁ ha₁.1 hc hb₁.1
      (hac₁.trans hcb₁)]
    change (originalSeedCompletePath S w x₁ m₁ c + B₁ *ᵥ p₁) - x₂ = _
    dsimp only [δ, originalSeedCompletePath]
    change ((x₁ + A₁ *ᵥ p₁) + B₁ *ᵥ p₁) - x₂ =
      -((x₂ + A₂ *ᵥ p₂) - (x₁ + A₁ *ᵥ p₁)) + A₂ *ᵥ p₂ + B₁ *ᵥ p₁
    abel
  have hcross₁ : D.originalFocalKinetic gap m₁.1.1 m₂.1.2 (x₂ + m₂.2 - x₁) =
      matrixQuadratic (A₁ + B₂)⁻¹ (δ + A₁ *ᵥ p₁ + B₂ *ᵥ p₂) := by
    rw [D.originalFocalKinetic_eq_of_original_support hbounds ha₁ hb₂ (hac₁.trans hcb₂)]
    change matrixQuadratic (originalSeedClockCompliance S w m₁.1.1 m₂.1.2)⁻¹ _ = _
    rw [← D.originalSeedClockCompliance_add hF hw ha₁.1 hc hb₂.1, hdisp₁]
  have hcross₂ : D.originalFocalKinetic gap m₂.1.1 m₁.1.2 (x₁ + m₁.2 - x₂) =
      matrixQuadratic (A₂ + B₁)⁻¹ (-δ + A₂ *ᵥ p₂ + B₁ *ᵥ p₁) := by
    rw [D.originalFocalKinetic_eq_of_original_support hbounds ha₂ hb₁ (hac₂.trans hcb₁)]
    change matrixQuadratic (originalSeedClockCompliance S w m₂.1.1 m₁.1.2)⁻¹ _ = _
    rw [← D.originalSeedClockCompliance_add hF hw ha₂.1 hc hb₁.1, hdisp₂]
  rw [hown₁, hown₂, hcross₁, hcross₂] at hcycle
  exact hcycle

/-- The local phase momentum bound applies to the literal original Finsler momenta and
actual path positions. The cycle premise is the original kinetic inequality itself; the
inverse-leg bound is the intermediate local scale estimate used by the traffic argument. -/
theorem original_commonCut_legalCycle_momentum_norm_sq_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (x₁ x₂ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m₁ m₂ : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c D₀ C : ℝ}
    (ha₁ : m₁.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.1 ∈ μ.support)
    (hb₁ : m₁.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.2 ∈ ν.support)
    (ha₂ : m₂.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.1 ∈ μ.support)
    (hb₂ : m₂.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.2 ∈ ν.support)
    (hac₁ : m₁.1.1 < c) (hcb₁ : c < m₁.1.2)
    (hac₂ : m₂.1.1 < c) (hcb₂ : c < m₂.1.2) (hD₀ : 0 ≤ D₀) (hC : 0 ≤ C)
    (hcycle : D.originalFocalKinetic gap m₁.1.1 m₁.1.2 m₁.2 +
      D.originalFocalKinetic gap m₂.1.1 m₂.1.2 m₂.2 ≤
      D.originalFocalKinetic gap m₁.1.1 m₂.1.2 (x₂ + m₂.2 - x₁) +
        D.originalFocalKinetic gap m₂.1.1 m₁.1.2 (x₁ + m₁.2 - x₂) + D₀)
    (hbound : ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
      matrixQuadratic (originalSeedClockCompliance S w m₁.1.1 c)⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic (originalSeedClockCompliance S w m₂.1.1 c)⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic (originalSeedClockCompliance S w c m₁.1.2)⁻¹ v ≤ C * ∑ j, v j ^ 2 ∧
      matrixQuadratic (originalSeedClockCompliance S w c m₂.1.2)⁻¹ v ≤ C * ∑ j, v j ^ 2) :
    ‖originalSeedPairMomentum S w m₁ - originalSeedPairMomentum S w m₂‖ ^ 2 ≤
      4 * C * (D₀ + C * (finrank ℝ S.covector.ker : ℝ) *
        ‖originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c‖ ^ 2) := by
  have hc : c - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨by linarith [ha₁.1.1], by linarith [hb₁.1.2]⟩
  have hrec := D.original_commonCut_legalCycle_recast hF hw hbounds x₁ x₂ m₁ m₂
    ha₁ hb₁ ha₂ hb₂ hac₁ hcb₁ hac₂ hcb₂ hcycle
  have hn := legalTwoCycle_momentum_norm_sq_le
    (D.posDef_originalSeedClockCompliance hF hw ha₁.1 hc hac₁)
    (D.posDef_originalSeedClockCompliance hF hw hc hb₁.1 hcb₁)
    (D.posDef_originalSeedClockCompliance hF hw ha₂.1 hc hac₂)
    (D.posDef_originalSeedClockCompliance hF hw hc hb₂.1 hcb₂)
    (originalSeedPairMomentum S w m₁) (originalSeedPairMomentum S w m₂)
    (originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c)
    hD₀ hC hrec hbound
  simpa only [Fintype.card_fin] using hn

/-- The actual original geometric local-leg lower bounds imply the original phase momentum
estimate directly, with no inverse-norm premise or substitute matching law. -/
theorem original_commonCut_legalCycle_momentum_norm_sq_le_of_leg_lower_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (x₁ x₂ : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m₁ m₂ : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {c D₀ h : ℝ}
    (ha₁ : m₁.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.1 ∈ μ.support)
    (hb₁ : m₁.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.2 ∈ ν.support)
    (ha₂ : m₂.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.1 ∈ μ.support)
    (hb₂ : m₂.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.2 ∈ ν.support)
    (hac₁ : m₁.1.1 < c) (hcb₁ : c < m₁.1.2)
    (hac₂ : m₂.1.1 < c) (hcb₂ : c < m₂.1.2) (hh : 0 < h) (hD₀ : 0 ≤ D₀)
    (hlegA₁ : (originalSeedClockCompliance S w m₁.1.1 c - h • 1).PosSemidef)
    (hlegB₁ : (originalSeedClockCompliance S w c m₁.1.2 - h • 1).PosSemidef)
    (hlegA₂ : (originalSeedClockCompliance S w m₂.1.1 c - h • 1).PosSemidef)
    (hlegB₂ : (originalSeedClockCompliance S w c m₂.1.2 - h • 1).PosSemidef)
    (hcycle : D.originalFocalKinetic gap m₁.1.1 m₁.1.2 m₁.2 +
      D.originalFocalKinetic gap m₂.1.1 m₂.1.2 m₂.2 ≤
      D.originalFocalKinetic gap m₁.1.1 m₂.1.2 (x₂ + m₂.2 - x₁) +
        D.originalFocalKinetic gap m₂.1.1 m₁.1.2 (x₁ + m₁.2 - x₂) + D₀) :
    ‖originalSeedPairMomentum S w m₁ - originalSeedPairMomentum S w m₂‖ ^ 2 ≤
      (finrank ℝ S.covector.ker : ℝ) / h ^ 2 *
        ‖originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c‖ ^ 2 +
      2 * D₀ / h := by
  have hrec := D.original_commonCut_legalCycle_recast hF hw hbounds x₁ x₂ m₁ m₂
    ha₁ hb₁ ha₂ hb₂ hac₁ hcb₁ hac₂ hcb₂ hcycle
  simpa only [Fintype.card_fin] using
    legalTwoCycle_momentum_norm_sq_le_of_leg_lower_bounds hh hD₀
      hlegA₁ hlegB₁ hlegA₂ hlegB₂
      (originalSeedPairMomentum S w m₁) (originalSeedPairMomentum S w m₂)
      (originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c) hrec

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
