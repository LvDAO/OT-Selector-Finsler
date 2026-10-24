import OTSelector.Reconstruction.FinslerNormalizedPhaseCurveEnvelope
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowColors

/-!
# One original-data event controls every adaptive actual phase curve

The exceptional event uses only complete original input counts on finitely many
fixed candidate sets. Off it, every bounded-speed phase curve and every actual
edge subfamily in its tube have the same count bound. The curve and subfamily may
be selected after observing the matching; neither is assigned a Poisson law.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

theorem measurableSet_normalizedSourcePhaseWalkEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ}
    (z p : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m → Fin (m + 1) →
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) (R : ℝ) :
    MeasurableSet (D.normalizedSourcePhaseWalkEnvelope T cut z p code R) :=
  measurableSet_phaseCellEnvelopeFamily _ (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
    (fun j ↦ D.measurable_normalizedSourcePhaseCenter hF hw T hcut (z code j) (p code j))
    (D.measurableSet_sourcePhaseClocks cut) R

theorem normalizedSourcePhaseWalkEnvelope_intensity_lt_top [SFinite μ]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ}
    (z p : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m → Fin (m + 1) →
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseWalkEnvelope T cut z p code R) < (∞ : ℝ≥0∞) :=
  (D.normalizedSourcePhaseWalkEnvelope_intensity_le hF hw T hcut z p code R).trans_lt
    (ENNReal.mul_lt_top (by simp)
      (D.normalizedSourcePhaseCell_intensity_lt_top hF hw T hcut 0 0 R))

/-- This bad event depends only on unchanged original input counts on fixed phase candidates. -/
def normalizedSourcePhaseCurveBadEvent
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ) (m : ℕ) (r K : ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :=
  ⋃ code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m,
    {s | K * (m : ℝ) ≤ ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
      (D.normalizedSourcePhaseWalkEnvelope T cut (fun code j ↦ phaseWalkPosition code j)
        (fun code j ↦ phaseWalkMomentum code j) code (r + 2) ×ˢ {0})).toReal}

/-- The all-candidate original-input exceptional event is Borel. -/
theorem measurableSet_normalizedSourcePhaseCurveBadEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r K : ℝ) :
    MeasurableSet (D.normalizedSourcePhaseCurveBadEvent T cut m r K) := by
  apply MeasurableSet.iUnion
  intro code
  have hB := D.measurableSet_normalizedSourcePhaseWalkEnvelope hF hw T hcut
    (fun code j ↦ phaseWalkPosition code j) (fun code j ↦ phaseWalkMomentum code j) code (r + 2)
  exact measurableSet_le measurable_const
    (((Measure.measurable_coe (hB.prod (measurableSet_singleton (0 : Fin 2)))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal)

/-- The exceptional probability follows from actual original Poisson inputs with all candidate
rates and cardinalities already produced internally. -/
theorem normalizedSourcePhaseCurveBadEvent_measure_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) (r K : ℝ) :
    let v := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 (r + 2))).toReal
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
      (D.normalizedSourcePhaseCurveBadEvent T cut m r K) ≤
      Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
        (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) - 2 * v * (Real.exp 1 - 1)) * (m : ℝ)) :=
  D.original_source_normalizedPhaseWalkCandidates_count_le_exp hF hw T hcut hm Q
    (fun code j ↦ phaseWalkPosition code j) (fun code j ↦ phaseWalkMomentum code j) (r + 2) K

/-- Off one original-data bad event, every subsequently chosen curve and every actual edge
subfamily in its phase tube have finite count strictly below the same threshold. -/
theorem ae_count_normalizedPathPhaseTube_lt_of_not_badEvent
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {r K : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.normalizedSourcePhaseCurveBadEvent T cut m r K →
      ∀ γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ,
      ‖γ 0‖ ≤ (m : ℝ) →
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        ‖γ a - γ b‖ ≤ (m : ℝ) * |a - b|) →
      ∀ V : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)),
      (∀ e ∈ V, e.1.2 ∈ D.sourcePhaseClocks cut ∧
        ∃ t ∈ Icc (0 : ℝ) 1,
          ‖phasePairVector (normalizedMomentumNodePosition S w T (cut + S.level) e)
            (normalizedMomentumNodeValue S w T e) - γ t‖ ≤ r) →
      (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V < (∞ : ℝ≥0∞) ∧
        ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V).toReal <
          K * (m : ℝ) := by
  let z := fun (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) (j : Fin (m + 1)) ↦
    phaseWalkPosition code j
  let p := fun (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) (j : Fin (m + 1)) ↦
    phaseWalkMomentum code j
  have hB (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) :=
    D.measurableSet_normalizedSourcePhaseWalkEnvelope hF hw T hcut z p code (r + 2)
  have hfinite : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m,
      (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.normalizedSourcePhaseWalkEnvelope T cut z p code (r + 2) ×ˢ {0}) < (∞ : ℝ≥0∞) := by
    apply ae_all_iff.mpr
    intro code
    exact (Q.original_source_exp_moment_of_finite_intensity (hB code)
      (D.normalizedSourcePhaseWalkEnvelope_intensity_lt_top hF hw T hcut z p code (r + 2)).ne
      (show (0 : ℝ) ≤ 0 from le_rfl)).1
  filter_upwards [Q.full_matching, hfinite] with s hsfull hsfin
  intro hsnot γ hroot hLip V hV
  obtain ⟨code, hcontains⟩ := D.exists_normalizedSourcePhaseWalkEnvelope_containing_pathPhaseTube
    hF hw T hcut hm γ hroot hLip hr
  have hsub : V ⊆ Prod.fst ⁻¹' D.normalizedSourcePhaseWalkEnvelope T cut z p code (r + 2) := by
    intro e he
    apply hcontains e.1.1 (physicalPairAnchor e).2 (hV e he).1
    simpa only [normalizedMomentumNodePosition, normalizedMomentumNodeValue,
      originalMomentumNodePosition, originalMomentumNodeValue] using (hV e he).2
  have hle : (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V ≤
      (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (D.normalizedSourcePhaseWalkEnvelope T cut z p code (r + 2) ×ˢ {0}) := by
    apply (measure_mono hsub).trans_eq
    rw [← Measure.fst_apply (hB code), hsfull.source_marginal,
      legalInputColorMeasure_apply_prod _ _ _ (hB code)]
  have hsmall : ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
      (D.normalizedSourcePhaseWalkEnvelope T cut z p code (r + 2) ×ˢ {0})).toReal <
        K * (m : ℝ) := by
    apply lt_of_not_ge
    intro h
    exact hsnot (Set.mem_iUnion.mpr ⟨code, h⟩)
  exact ⟨hle.trans_lt (hsfin code), (ENNReal.toReal_mono (hsfin code).ne hle).trans_lt hsmall⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
