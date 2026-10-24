import OTSelector.Reconstruction.FinslerOriginalMinimizerRoughMomentum
import OTSelector.Reconstruction.FinslerOriginalMomentumFieldNodeError
import OTSelector.Reconstruction.FinslerOriginalMeasurablePhaseInverse

/-! The original stationary minimizer produces its actual jointly measurable
Lipschitz momentum field and its true occupied-node error. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Actual weighted minimality gives the measurable canonical field with its
explicit internal geometric Lipschitz constant and `sqrt(|t|)` node error.
No rough-node or field-Lipschitz premise is assumed. -/
theorem OriginalSeedConditionalMoments.original_minimizer_canonical_momentum_field
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
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
      (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ D.momentumPhaseField cut h L a.1 a.2) ∧
    (∀ s, LipschitzWith L (D.momentumPhaseField cut h L s)) ∧
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (D.momentumPhaseNodeMeasure cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ‖originalMomentumNodeValue S w e - D.momentumPhaseField cut h L s
          (originalMomentumNodePosition S w (cut + S.level) e)‖ ≤ b := by
  dsimp only
  refine ⟨D.measurable_momentumPhaseField hF hw hcut h _,
    D.lipschitzWith_momentumPhaseField_everywhere cut h _, ?_⟩
  filter_upwards [Q.full_matching,
    D.ae_original_minimizer_rough_momentum_bound hF hw hgap hbounds hg hgb t Q hmin hcut hh]
    with s hs hrough
  exact fun e he ↦ D.momentumPhaseField_node_error_of_node_bound cut h _ s hs
    (Real.sqrt_nonneg _) hrough he

end OTSelector.Reconstruction
