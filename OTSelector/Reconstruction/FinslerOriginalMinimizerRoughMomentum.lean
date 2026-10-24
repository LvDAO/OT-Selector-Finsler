import OTSelector.Reconstruction.FinslerOriginalMinimizerMomentumNodes
import OTSelector.Reconstruction.FinslerOriginalMomentumField
import Mathlib.Analysis.Real.Sqrt

/-! Minimality supplies the actual rough-node inequality with explicit
geometric Lipschitz constant and perturbation error proportional to sqrt(|t|). -/
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

/-- The actual minimizer gives the node inequality required by the canonical
rough field, with constants derived from the actual internal leg level and probe. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_rough_momentum_bound
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
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (D.momentumPhaseNodeMeasure cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ f ∈ (D.momentumPhaseNodeMeasure cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ‖originalMomentumNodeValue S w e - originalMomentumNodeValue S w f‖ ≤
          L * dist (originalMomentumNodePosition S w (cut + S.level) e)
            (originalMomentumNodePosition S w (cut + S.level) f) + b := by
  dsimp only
  have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  have hA : 0 ≤ (finrank ℝ S.covector.ker : ℝ) / h ^ 2 := by positivity
  have hB : 0 ≤ 8 * |t| * G / h := by positivity
  filter_upwards [D.ae_original_minimizer_momentum_node_sq_bound hF hw hgap hbounds hg hgb
    t Q hmin hcut hh] with s hs
  intro e he f hf
  have hsq := hs e he f hf
  rw [← Real.sq_sqrt hA, ← Real.sq_sqrt hB] at hsq
  rw [← dist_eq_norm (originalMomentumNodePosition S w (cut + S.level) e)
    (originalMomentumNodePosition S w (cut + S.level) f)] at hsq
  have hprod := mul_nonneg (Real.sqrt_nonneg ((finrank ℝ S.covector.ker : ℝ) / h ^ 2))
    (dist_nonneg (x := originalMomentumNodePosition S w (cut + S.level) e)
      (y := originalMomentumNodePosition S w (cut + S.level) f))
  have hcross := mul_nonneg hprod (Real.sqrt_nonneg (8 * |t| * G / h))
  change ‖originalMomentumNodeValue S w e - originalMomentumNodeValue S w f‖ ≤
    Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) *
      dist (originalMomentumNodePosition S w (cut + S.level) e)
        (originalMomentumNodePosition S w (cut + S.level) f) + Real.sqrt (8 * |t| * G / h)
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hprod (Real.sqrt_nonneg _))).mp
  nlinarith only [hsq, hcross]

end OTSelector.Reconstruction
