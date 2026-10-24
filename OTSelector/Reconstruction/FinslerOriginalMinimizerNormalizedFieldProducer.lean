import OTSelector.Reconstruction.FinslerOriginalMinimizerNormalizedField

/-! The actual original Finsler producer yields a genuine weighted minimizer
together with its measurable canonical field in any invertible phase frame and quantitative occupied-node error. -/
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

/-- The general original producer derives the optimizer and normalized field properties
internally. The common-cut level is an internal geometric level of its actual
eligible nodes, not an added final geometric condition. -/
theorem OriginalSeedConditionalMoments.exists_original_minimizer_with_canonical_normalized_momentum_field
    (D : OriginalSeedConditionalMoments S w μ ν)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) (t : ℝ)
    {cut h : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    ∃ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      Q.value t = D.originalWeightedStationaryInf gap g t ∧
      (∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t) ∧
      Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ D.normalizedMomentumPhaseField T cut h L a.1 a.2) ∧
      (∀ s, LipschitzWith L (D.normalizedMomentumPhaseField T cut h L s)) ∧
      ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
        ∀ e ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
          Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
          ‖normalizedMomentumNodeValue S w T e - D.normalizedMomentumPhaseField T cut h L s
            (normalizedMomentumNodePosition S w T (cut + S.level) e)‖ ≤ b := by
  dsimp only
  obtain ⟨Q, hvalue, hmin⟩ := D.exists_original_weighted_stationary_minimizer
    hF hw hq hgap hbounds π hπ horder hg hgb hgc t
  obtain ⟨hm, hL, herror⟩ := D.original_minimizer_canonical_normalized_momentum_field hF hw
    hgap hbounds T hg hgb t Q hmin hcut hh
  exact ⟨Q, hvalue, hmin, hm, hL, herror⟩

end OTSelector.Reconstruction
