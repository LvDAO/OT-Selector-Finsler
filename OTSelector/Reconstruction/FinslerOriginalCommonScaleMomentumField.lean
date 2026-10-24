import OTSelector.Analysis.LipschitzCommonScaleField
import OTSelector.Reconstruction.FinslerOriginalMinimizerNormalizedField

/-! Common scaling of the actual original minimizer field preserves its scene
measurability and Lipschitz constant and divides its occupied-node error by δ. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The same original occupied node position divided by the common phase scale. -/
def commonScaleNormalizedMomentumNodePosition (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (δ c : ℝ) (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  δ⁻¹ • normalizedMomentumNodePosition S w T c e

/-- Original covariant momentum divided by the identical common phase scale. -/
def commonScaleNormalizedMomentumNodeValue (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (δ : ℝ) (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  δ⁻¹ • normalizedMomentumNodeValue S w T e

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual canonical field in the common position and momentum coordinates. -/
def commonScaleNormalizedMomentumPhaseField
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (δ : ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (x : Fin (finrank ℝ S.covector.ker) → ℝ) : Fin (finrank ℝ S.covector.ker) → ℝ :=
  commonScalePhaseField δ (D.normalizedMomentumPhaseField T cut h L s) x

theorem measurable_commonScaleNormalizedMomentumPhaseField
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (δ : ℝ) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
        D.commonScaleNormalizedMomentumPhaseField T cut h L δ a.1 a.2) :=
  measurable_commonScalePhaseField (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L) δ

theorem lipschitzWith_commonScaleNormalizedMomentumPhaseField
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) {δ : ℝ} (hδ : 0 < δ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LipschitzWith L (D.commonScaleNormalizedMomentumPhaseField T cut h L δ s) :=
  lipschitzWith_commonScalePhaseField hδ (D.lipschitzWith_normalizedMomentumPhaseField T cut h L s)

/-- The actual weighted minimizer internally supplies the common-scale field,
with the same global L and its explicit original error divided by δ. -/
theorem original_minimizer_canonical_commonScale_momentum_field
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {δ : ℝ} (hδ : 0 < δ)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
        D.commonScaleNormalizedMomentumPhaseField T cut h L δ a.1 a.2) ∧
    (∀ s, LipschitzWith L (D.commonScaleNormalizedMomentumPhaseField T cut h L δ s)) ∧
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ‖commonScaleNormalizedMomentumNodeValue S w T δ e -
          D.commonScaleNormalizedMomentumPhaseField T cut h L δ s
            (commonScaleNormalizedMomentumNodePosition S w T δ (cut + S.level) e)‖ ≤ b / δ := by
  dsimp only
  have hfield := D.original_minimizer_canonical_normalized_momentum_field
    hF hw hgap hbounds T hg hgb t Q hmin hcut hh
  refine ⟨D.measurable_commonScaleNormalizedMomentumPhaseField hF hw T hcut h _ δ,
    fun s ↦ D.lipschitzWith_commonScaleNormalizedMomentumPhaseField T cut h _ hδ s, ?_⟩
  filter_upwards [hfield.2.2] with s hs
  intro e he
  exact commonScalePhaseField_node_error hδ (D.normalizedMomentumPhaseField T cut h _ s)
    (hs e he)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
