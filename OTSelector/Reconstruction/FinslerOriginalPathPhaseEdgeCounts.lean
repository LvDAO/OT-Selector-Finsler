import OTSelector.Reconstruction.FinslerOriginalPathPhaseSourceContainment
import OTSelector.Reconstruction.FinslerOriginalPhaseCellCounts
import OTSelector.Reconstruction.FinslerOriginalPathMeasurability
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowColors

/-!
# Actual matching phase counts are dominated by complete original-input counts

The phase edge set uses the actual original complete path and actual original
momentum. Its random count is bounded by the unchanged original source count,
so its exponential moment follows without assigning it a Poisson law.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original edges whose path position and actual momentum lie in a fixed phase cell. -/
def sourcePathPhaseEdges (cut : ℝ) (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
  {e | e.1.2 ∈ D.sourcePhaseClocks cut ∧
    ‖originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (cut + S.level) - z₀‖ ≤ R ∧
    ‖originalSeedPairMomentum S w (physicalPairAnchor e).2 - p₀‖ ≤ R}

/-- The actual phase edge set is Borel in the unchanged original endpoints. -/
theorem measurableSet_sourcePathPhaseEdges
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (cut : ℝ)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) (R : ℝ) :
    MeasurableSet (D.sourcePathPhaseEdges cut z₀ p₀ R) := by
  have hm : Measurable (fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      (physicalPairAnchor e).2) := measurable_physicalPairAnchor.snd
  have hX : Measurable (fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (cut + S.level)) :=
    (measurable_originalSeedCompletePath S hF hw).comp
      ((measurable_fst.fst.prodMk hm).prodMk measurable_const)
  have hp := (measurable_originalSeedPairMomentum S hF hw).comp hm
  exact ((D.measurableSet_sourcePhaseClocks cut).preimage measurable_fst.snd).inter
    ((measurableSet_le (hX.sub_const z₀).norm measurable_const).inter
      (measurableSet_le (hp.sub_const p₀).norm measurable_const))

omit [BorelSpace E] in
/-- Every actual phase edge has its actual source in the fixed deterministic source envelope. -/
theorem sourcePathPhaseEdges_subset_sourceEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    D.sourcePathPhaseEdges cut z₀ p₀ R ⊆ Prod.fst ⁻¹'
      markedPhaseSourceCell 1 (D.sourcePhaseLeg cut)
        (D.sourcePhaseCenter cut z₀ p₀) (D.sourcePhaseClocks cut) R := by
  intro e he
  exact D.original_pathPhase_source_mem hF hw hcut e.1.1 z₀ p₀ (physicalPairAnchor e).2
    he.1 hR he.2.1 he.2.2

omit [BorelSpace E] in
/-- Counting selected actual edges in a fixed phase cell is bounded by the complete original
source count. The whole same-input marginal equality supplies this domination. -/
theorem ae_sourcePathPhaseEdges_count_le_original_source
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (D.sourcePathPhaseEdges cut z₀ p₀ R) ≤
      (s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (markedPhaseSourceCell 1 (D.sourcePhaseLeg cut)
          (D.sourcePhaseCenter cut z₀ p₀) (D.sourcePhaseClocks cut) R ×ˢ {0}) := by
  have hB := measurableSet_markedPhaseSourceCell
    (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ)
    (D.measurable_sourcePhaseLeg hF hw hcut) (D.measurable_sourcePhaseCenter hF hw hcut z₀ p₀)
    (D.measurableSet_sourcePhaseClocks cut) R
  filter_upwards [Q.full_matching] with s hs
  calc
    _ ≤ (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (Prod.fst ⁻¹' markedPhaseSourceCell 1 (D.sourcePhaseLeg cut)
          (D.sourcePhaseCenter cut z₀ p₀) (D.sourcePhaseClocks cut) R) :=
      measure_mono (D.sourcePathPhaseEdges_subset_sourceEnvelope hF hw hcut z₀ p₀ hR)
    _ = _ := by
      rw [← Measure.fst_apply hB, hs.source_marginal,
        legalInputColorMeasure_apply_prod _ _ _ hB]

/-- The actual random matching phase count has the original-input exponential bound.
No Poisson distribution or independence is imposed on this matching-dependent count. -/
theorem original_sourcePathPhaseEdges_exp_moment
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (z₀ p₀ : Fin (finrank ℝ S.covector.ker) → ℝ) {R : ℝ} (hR : 0 ≤ R)
    {t : ℝ} (ht : 0 ≤ t) :
    let A := D.sourcePathPhaseEdges cut z₀ p₀ R
    let B := markedPhaseSourceCell 1 (D.sourcePhaseLeg cut)
      (D.sourcePhaseCenter cut z₀ p₀) (D.sourcePhaseClocks cut) R
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) A < (∞ : ℝ≥0∞)) ∧
      Integrable (fun s ↦ Real.exp (t *
        ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) A).toReal))
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, Real.exp (t *
        ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) A).toReal)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
          Real.exp ((((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            B).toReal * (Real.exp t - 1)) := by
  dsimp only
  have hm := D.original_source_phaseCell_exp_moment hF hw hcut Q
    (L := (1 : Matrix (Fin (finrank ℝ S.covector.ker)) _ ℝ)) (by simp)
    (D.measurable_sourcePhaseCenter hF hw hcut z₀ p₀) R ht
  have hle := D.ae_sourcePathPhaseEdges_count_le_original_source hF hw hcut Q z₀ p₀ hR
  have hfin : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (D.sourcePathPhaseEdges cut z₀ p₀ R) < (∞ : ℝ≥0∞) := by
    filter_upwards [hm.1, hle] with s hs h
    exact h.trans_lt hs
  have hmeas : Measurable (fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
      Real.exp (t * ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (D.sourcePathPhaseEdges cut z₀ p₀ R)).toReal)) := by
    exact ((Measure.measurable_coe (D.measurableSet_sourcePathPhaseEdges hF hw cut z₀ p₀ R)).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)).ennreal_toReal.const_mul t |>.exp
  have he : ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Real.exp (t * ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (D.sourcePathPhaseEdges cut z₀ p₀ R)).toReal) ≤
      Real.exp (t * ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
        (markedPhaseSourceCell 1 (D.sourcePhaseLeg cut)
          (D.sourcePhaseCenter cut z₀ p₀) (D.sourcePhaseClocks cut) R ×ˢ {0})).toReal) := by
    filter_upwards [hm.1, hle] with s hs h
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hs.ne h) ht)
  have hI := hm.2.1.mono' hmeas.aestronglyMeasurable
    (he.mono fun s hs ↦ by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hs)
  exact ⟨hfin, hI, (integral_mono_ae hI hm.2.1 he).trans hm.2.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
