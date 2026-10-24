import OTSelector.Reconstruction.FinslerOriginalNormalizedEligibleCycleMomentum
import OTSelector.Reconstruction.FinslerOriginalMinimizerTwoCycle

/-! Actual weighted minimality supplies the momentum bound for every pair of
eligible original occupied complete-path nodes, almost surely. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual original minimizer's eligible nodes obey the precise momentum
square estimate. No cyclic-optimality or rough-field premise is supplied. -/
theorem OriginalSeedConditionalMoments.ae_original_minimizer_normalized_momentum_node_sq_bound
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
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ f ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ‖normalizedMomentumNodeValue S w T e - normalizedMomentumNodeValue S w T f‖ ^ 2 ≤
          (finrank ℝ S.covector.ker : ℝ) / h ^ 2 *
            ‖normalizedMomentumNodePosition S w T (cut + S.level) e -
              normalizedMomentumNodePosition S w T (cut + S.level) f‖ ^ 2 + 8 * |t| * G / h := by
  have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  filter_upwards [Q.full_matching,
    D.original_weighted_minimizer_legal_kineticTwoCycle hF hw hgap hbounds hg hgb t Q hmin]
    with s hs hcycle
  intro e he f hf
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  obtain ⟨hefull, heE⟩ := (mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) e).mp he
  obtain ⟨hffull, hfE⟩ := (mem_support_originalCountingNodeRestriction_iff
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.normalizedMomentumPhaseEligibleEdges T cut h) f).mp hf
  have hn := D.normalized_eligible_kineticTwoCycle_momentum_norm_sq_le hF hw hbounds T hcut hh
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg t)) hG) e f heE hfE
    (hcycle e hefull f hffull (by linarith [heE.1.2, hfE.2.1.1])
      (by linarith [hfE.1.2, heE.2.1.1]))
  convert hn using 1
  ring

end OTSelector.Reconstruction
