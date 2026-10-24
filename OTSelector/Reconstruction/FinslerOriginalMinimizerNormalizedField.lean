import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumField
import OTSelector.Reconstruction.FinslerOriginalMinimizerNormalizedRoughMomentum

/-! The actual original minimizer supplies its canonical field in every phase frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Actual weighted minimality gives the same Borel canonical field after
an arbitrary invertible physical phase change, with the original explicit error.
The four normalized leg thresholds are contained in the actual eligible node set. -/
theorem OriginalSeedConditionalMoments.original_minimizer_canonical_normalized_momentum_field
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
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
        D.normalizedMomentumPhaseField T cut h L a.1 a.2) ∧
    (∀ s, LipschitzWith L (D.normalizedMomentumPhaseField T cut h L s)) ∧
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ‖normalizedMomentumNodeValue S w T e - D.normalizedMomentumPhaseField T cut h L s
          (normalizedMomentumNodePosition S w T (cut + S.level) e)‖ ≤ b := by
  dsimp only
  refine ⟨D.measurable_normalizedMomentumPhaseField hF hw T hcut h _,
    D.lipschitzWith_normalizedMomentumPhaseField T cut h _, ?_⟩
  filter_upwards [Q.full_matching,
    D.ae_original_minimizer_normalized_rough_momentum_bound hF hw hgap hbounds T hg hgb
      t Q hmin hcut hh] with s hs hrough
  exact fun e he ↦ D.normalizedMomentumPhaseField_node_error_of_node_bound T cut h _ s hs
    (Real.sqrt_nonneg _) hrough he

end OTSelector.Reconstruction
