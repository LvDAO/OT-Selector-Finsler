import OTSelector.Reconstruction.RegularClockLegLowerBound
import OTSelector.Reconstruction.FinslerOriginalCommonCutLegalCycle

/-!
# Internal common-cut momentum control on actual regular clock collars

A fixed pair of interior clock collars produces the four compliance lower bounds from the
actual original Finsler kernel. The resulting legal-cycle momentum estimate carries no
separate local inverse or matrix-lower-bound premise. Its cycle premise is the unchanged
original kinetic two-cycle inequality, to be supplied by the stationary optimizer argument.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Clock collars at an actual regular cut internally supply every geometric constant in
this momentum estimate for the original legal kinetic cycle. Endpoints outside the collars
may approach focal endpoints, so long as they remain in their original open support span. -/
theorem exists_original_regularCut_legalCycle_momentum_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {r c s : ℝ} (hr : r - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hc : c - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hs : s - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hrc : r < c) (hcs : c < s) :
    ∃ h : ℝ, h > 0 ∧
      ∀ (x₁ x₂ : Fin (finrank ℝ S.covector.ker) → ℝ)
        (m₁ m₂ : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) {D₀ : ℝ},
      m₁.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.1 ∈ μ.support →
      m₁.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₁.1.2 ∈ ν.support →
      m₂.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.1 ∈ μ.support →
      m₂.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m₂.1.2 ∈ ν.support →
      m₁.1.1 ≤ r → m₂.1.1 ≤ r → s ≤ m₁.1.2 → s ≤ m₂.1.2 → 0 ≤ D₀ →
      D.originalFocalKinetic gap m₁.1.1 m₁.1.2 m₁.2 +
        D.originalFocalKinetic gap m₂.1.1 m₂.1.2 m₂.2 ≤
        D.originalFocalKinetic gap m₁.1.1 m₂.1.2 (x₂ + m₂.2 - x₁) +
          D.originalFocalKinetic gap m₂.1.1 m₁.1.2 (x₁ + m₁.2 - x₂) + D₀ →
      ‖originalSeedPairMomentum S w m₁ - originalSeedPairMomentum S w m₂‖ ^ 2 ≤
        (finrank ℝ S.covector.ker : ℝ) / h ^ 2 *
          ‖originalSeedCompletePath S w x₂ m₂ c - originalSeedCompletePath S w x₁ m₁ c‖ ^ 2 +
        2 * D₀ / h := by
  obtain ⟨h, hh, hlegs⟩ := D.exists_original_commonCut_fourLeg_lower hF hw hr hc hs hrc hcs
  refine ⟨h, hh, fun x₁ x₂ m₁ m₂ {D₀} ha₁ hb₁ ha₂ hb₂ h₁ h₂ h₃ h₄ hD₀ hcycle ↦ ?_⟩
  obtain ⟨hA₁, hB₁, hA₂, hB₂⟩ := hlegs ha₁.1 ha₂.1 hb₁.1 hb₂.1 h₁ h₂ h₃ h₄
  exact D.original_commonCut_legalCycle_momentum_norm_sq_le_of_leg_lower_bounds hF hw hbounds
    x₁ x₂ m₁ m₂ ha₁ hb₁ ha₂ hb₂ (h₁.trans_lt hrc) (hcs.trans_le h₃)
    (h₂.trans_lt hrc) (hcs.trans_le h₄) hh hD₀ hA₁ hB₁ hA₂ hB₂ hcycle

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
