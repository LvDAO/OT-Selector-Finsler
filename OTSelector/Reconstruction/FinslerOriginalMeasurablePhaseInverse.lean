import OTSelector.Reconstruction.FinslerOriginalMomentumField
import OTSelector.Reconstruction.OriginalCountingFieldEverywhereLipschitz
import OTSelector.Analysis.ContractiveInverseCovariance

/-!
# The measurable inverse of the original Finsler momentum field

The same original occupied-node field is uniformly Lipschitz on every ambient scene.
Its canonical inverse is therefore jointly Borel in the complete original scene and
actual target. On actual full matching scenes, spatial rerooting transports both target
and inverse point by the same subtraction; no independent adaptive scene is introduced.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The unchanged original vector field has the same Lipschitz constant on every ambient
scene, including scenes which are not genuine full original matchings. -/
theorem lipschitzWith_momentumPhaseField_everywhere
    (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    LipschitzWith L (D.momentumPhaseField cut h L s) :=
  lipschitzWith_originalCountingRoughField_vector_everywhere
    (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) L
    (originalMomentumNodePosition S w (cut+S.level)) (originalMomentumNodeValue S w)
    (D.momentumPhaseNodeMeasure cut h s)

/-- The actual original field supplies the literal norm form of the contraction input. -/
theorem momentumPhaseField_lipschitz_everywhere
    (cut h : ℝ) (L : ℝ≥0)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    ∀z y, ‖D.momentumPhaseField cut h L s z-D.momentumPhaseField cut h L s y‖≤
      (L:ℝ)*‖z-y‖ := by
  intro z y
  simpa only [dist_eq_norm] using
    (D.lipschitzWith_momentumPhaseField_everywhere cut h L s).dist_le_mul z y

/-- The canonical inverse of the same original field at the specified physical target. -/
def momentumPhaseInverse (cut h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ]
      (Fin (finrank ℝ S.covector.ker)→ℝ)) (hsmall : ‖R‖*(L:ℝ)≤(1/2:ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (a : Fin (finrank ℝ S.covector.ker)→ℝ) : Fin (finrank ℝ S.covector.ker)→ℝ :=
  phaseInverseAt (D.momentumPhaseField cut h L s)
    (D.momentumPhaseField_lipschitz_everywhere cut h L s) R hsmall a

/-- The same original momentum phase map sends its canonical inverse exactly to target a. -/
theorem momentumPhaseInverse_eq (cut h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ]
      (Fin (finrank ℝ S.covector.ker)→ℝ)) (hsmall : ‖R‖*(L:ℝ)≤(1/2:ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (a : Fin (finrank ℝ S.covector.ker)→ℝ) :
    D.momentumPhaseInverse cut h L R hsmall s a+
      R (D.momentumPhaseField cut h L s (D.momentumPhaseInverse cut h L R hsmall s a))=a :=
  phaseInverseAt_eq (D.momentumPhaseField_lipschitz_everywhere cut h L s) R hsmall a

/-- The actual inverse is jointly Borel in the unchanged whole scene and physical target. -/
theorem measurable_momentumPhaseInverse
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ]
      (Fin (finrank ℝ S.covector.ker)→ℝ)) (hsmall : ‖R‖*(L:ℝ)≤(1/2:ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×
      (Fin (finrank ℝ S.covector.ker)→ℝ) ↦
        D.momentumPhaseInverse cut h L R hsmall a.1 a.2) :=
  measurable_phaseInverseAt (D.measurable_momentumPhaseField hF hw hcut h L)
    measurable_const (D.momentumPhaseField_lipschitz_everywhere cut h L) (fun _ ↦ hsmall)

/-- A measurable mobility depending on the same original scene also gives a jointly
measurable inverse, with no auxiliary random field or selected zero. -/
theorem measurable_momentumPhaseInverse_randomMobility
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)→
      (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ](Fin (finrank ℝ S.covector.ker)→ℝ))
    (hR : Measurable R) (hsmall : ∀s, ‖R s‖*(L:ℝ)≤(1/2:ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×
      (Fin (finrank ℝ S.covector.ker)→ℝ) ↦
        D.momentumPhaseInverse cut h L (R a.1) (hsmall a.1) a.1 a.2) :=
  measurable_phaseInverseAt (D.measurable_momentumPhaseField hF hw hcut h L)
    hR (D.momentumPhaseField_lipschitz_everywhere cut h L) hsmall

/-- The actual inverse-point momentum is measurable on the same original scene and target. -/
theorem measurable_momentum_at_phaseInverse
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ]
      (Fin (finrank ℝ S.covector.ker)→ℝ)) (hsmall : ‖R‖*(L:ℝ)≤(1/2:ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×
      (Fin (finrank ℝ S.covector.ker)→ℝ) ↦
        D.momentumPhaseField cut h L a.1 (D.momentumPhaseInverse cut h L R hsmall a.1 a.2)) :=
  (D.measurable_momentumPhaseField hF hw hcut h L).comp
    (measurable_fst.prodMk (D.measurable_momentumPhaseInverse hF hw hcut h L R hsmall))

/-- A genuine original spatial reroot subtracts v from both the actual target and its
canonical inverse point. This uses the same occupied field and its proved reroot identity. -/
theorem momentumPhaseInverse_reroot
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ]
      (Fin (finrank ℝ S.covector.ker)→ℝ)) (hsmall : ‖R‖*(L:ℝ)≤(1/2:ℝ))
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (hs : IsFullOriginalInputMatching _ s)
    (v a : Fin (finrank ℝ S.covector.ker)→ℝ) :
    D.momentumPhaseInverse cut h L R hsmall (legalMarkedInputSceneReroot _ v s) (a-v)=
      D.momentumPhaseInverse cut h L R hsmall s a-v :=
  phaseInverseAt_translate_covariant
    (D.momentumPhaseField_lipschitz_everywhere cut h L s)
    (D.momentumPhaseField_lipschitz_everywhere cut h L (legalMarkedInputSceneReroot _ v s))
    R hsmall hsmall v (D.momentumPhaseField_reroot hF hw hcut h L s hs v) a

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
