import OTSelector.Reconstruction.FinslerOriginalMomentumField

/-! The canonical actual rough momentum field approximates every eligible
original occupied node, with the same vector sup-norm error. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

omit [BorelSpace E] in
/-- The original scalar completed-node construction preserves its actual error
at each node, and the vector field has this same sup-norm error. -/
theorem OriginalSeedConditionalMoments.momentumPhaseField_node_error_of_node_bound
    (D : OriginalSeedConditionalMoments S w μ ν) (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s) {b : ℝ} (hb : 0 ≤ b)
    (hrough : ∀ e ∈ (D.momentumPhaseNodeMeasure cut h s :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ f ∈ (D.momentumPhaseNodeMeasure cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
        ‖originalMomentumNodeValue S w e - originalMomentumNodeValue S w f‖ ≤
          L * dist (originalMomentumNodePosition S w (cut + S.level) e)
            (originalMomentumNodePosition S w (cut + S.level) f) + b)
    {e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)}
    (he : e ∈ (D.momentumPhaseNodeMeasure cut h s :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support) :
    ‖originalMomentumNodeValue S w e -
      D.momentumPhaseField cut h L s (originalMomentumNodePosition S w (cut + S.level) e)‖ ≤ b := by
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hn := isLegalCountingMeasure_originalCountingNodeRestriction
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
    (D.momentumPhaseEligibleEdges cut h)
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  have hi := originalCountingRoughField_node_bounds
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) L
    (originalMomentumNodePosition S w (cut + S.level))
    (fun a ↦ originalMomentumNodeValue S w a i) (D.momentumPhaseNodeMeasure cut h s) hn (b := b)
    (fun a ha b hb' ↦ by
      have hr := hrough a ha b hb'
      have hp := norm_le_pi_norm (originalMomentumNodeValue S w a - originalMomentumNodeValue S w b) i
      have hab := le_abs_self (originalMomentumNodeValue S w a i - originalMomentumNodeValue S w b i)
      simp only [Real.norm_eq_abs, Pi.sub_apply] at hp
      linarith) he
  change |originalMomentumNodeValue S w e i -
    D.momentumPhaseField cut h L s (originalMomentumNodePosition S w (cut + S.level) e) i| ≤ b
  change originalMomentumNodeValue S w e i - b ≤
    D.momentumPhaseField cut h L s (originalMomentumNodePosition S w (cut + S.level) e) i ∧
    D.momentumPhaseField cut h L s (originalMomentumNodePosition S w (cut + S.level) e) i ≤
      originalMomentumNodeValue S w e i at hi
  exact abs_le.mpr ⟨by linarith [hi.2], by linarith [hi.1]⟩

end OTSelector.Reconstruction
