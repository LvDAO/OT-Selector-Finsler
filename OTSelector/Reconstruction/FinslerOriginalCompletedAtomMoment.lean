import OTSelector.Reconstruction.FinslerOriginalCommonScaleAmplitudeMoment

/-!
# Completed-atom node-data first moment for the amplitude

The completed-atom node-data first moment is reduced to the linear actual
node-measure Campbell first moment of the same node data. The key point is that
for a legal counting measure the selected completed atom is an occupied atom of
mass at least one, so its node-data value is dominated by the node-measure
integral of the same nonnegative node data. Hence the completed-atom moment is
at most the linear node-measure Campbell moment, and the latter is the genuine
Poisson/Palm first-moment computation (infinite-volume spatial intensity, so not
reducible to a deterministic volume bound).
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
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
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Completed-atom node-data first moment from the linear node-measure Campbell
first moment. The point-atom domination is the actual counting-measure property
(the selected completed atom is an occupied atom of mass at least one, so its
nonnegative node data is dominated by the node-measure integral of the same
data); the remaining Poisson/Palm input is the linear Campbell moment. -/
theorem amplitudeMoment_of_nodeMeasureCampbellMoment
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
    {cut h : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    {M : ℝ}
    (hdom : ∀ᵐ s ∂(Q.law : Measure
        (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ENNReal.ofReal (‖normalizedMomentumNodeValue S w T
        (originalCountingCompletedAtom
          (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
          (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖ +
        Real.sqrt (8 * |t| * G / h) +
        ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
          Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) *
          ‖normalizedMomentumNodePosition S w T (cut + S.level)
            (originalCountingCompletedAtom
              (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
              (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖) ≤
        ∫⁻ e, ENNReal.ofReal (‖normalizedMomentumNodeValue S w T e‖ +
          Real.sqrt (8 * |t| * G / h) +
          ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) *
            ‖normalizedMomentumNodePosition S w T (cut + S.level) e‖)
          ∂(D.normalizedMomentumPhaseNodeMeasure T cut h s))
    (hCampbell : (∫⁻ s, ∫⁻ e, ENNReal.ofReal (‖normalizedMomentumNodeValue S w T e‖ +
          Real.sqrt (8 * |t| * G / h) +
          ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) *
            ‖normalizedMomentumNodePosition S w T (cut + S.level) e‖)
          ∂(D.normalizedMomentumPhaseNodeMeasure T cut h s)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
      ≤ ENNReal.ofReal M) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    (∫⁻ s, ENNReal.ofReal (‖D.normalizedMomentumPhaseField T cut h L s 0‖)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      ENNReal.ofReal M := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  have hM : (∫⁻ s, ENNReal.ofReal (‖normalizedMomentumNodeValue S w T
        (originalCountingCompletedAtom
          (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
          (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖ +
        Real.sqrt (8 * |t| * G / h) +
        ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
          Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) *
          ‖normalizedMomentumNodePosition S w T (cut + S.level)
            (originalCountingCompletedAtom
              (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
              (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      ENNReal.ofReal M := (lintegral_mono_ae hdom).trans hCampbell
  exact amplitudeMoment_of_completedNodeDataMoment D hF hw hgap hbounds T hg hgb t Q hmin
    hcut hh hM

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
