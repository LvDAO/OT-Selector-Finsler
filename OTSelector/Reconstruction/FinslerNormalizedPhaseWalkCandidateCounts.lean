import OTSelector.Reconstruction.PhaseCellEnvelopeFamilies
import OTSelector.Finite.LatticeWalkCodes
import OTSelector.Reconstruction.FinslerOriginalNormalizedPhaseSourceContainment
import OTSelector.Probability.FiniteIntensityCandidateUnionBound

/-!
# Actual original-input bounds for all finitely coded phase-cell candidates

Each candidate has m+1 original phase-cell envelopes. Their common intensity and
the finite code cardinality are produced internally, so the full original-input
exceptional event controls every later adaptive choice of a candidate at once.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- A deterministic candidate union of actual source phase-cell envelopes. -/
def normalizedSourcePhaseWalkEnvelope {m : ℕ}
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut : ℝ)
    (z p : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m → Fin (m + 1) →
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) (R : ℝ) :
    Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  phaseCellEnvelopeFamily T⁻¹ (fun a ↦ T * D.sourcePhaseLeg cut a * Tᵀ)
    (fun j ↦ D.normalizedSourcePhaseCenter T cut (z code j) (p code j)) (D.sourcePhaseClocks cut) R

/-- The original intensity of every m-step candidate is at most m+1 times the same
single-cell intensity, independently of its deterministic phase-cell centers. -/
theorem normalizedSourcePhaseWalkEnvelope_intensity_le [SFinite μ]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ}
    (z p : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m → Fin (m + 1) →
      (Fin (finrank ℝ S.covector.ker) → ℝ))
    (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) (R : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseWalkEnvelope T cut z p code R) ≤
      (m + 1 : ℝ≥0∞) * ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
        (D.normalizedSourcePhaseCell T cut 0 0 R) := by
  simpa only [normalizedSourcePhaseWalkEnvelope, normalizedSourcePhaseCell,
    normalizedSourcePhaseCenter_zero, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    prod_volume_phaseCellEnvelopeFamily_le
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
      (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
      (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
      (fun j ↦ D.measurable_normalizedSourcePhaseCenter hF hw T hcut (z code j) (p code j))
      (D.measurableSet_sourcePhaseClocks cut) μ R

/-- The true original Poisson input simultaneously controls all deterministic coded phase
candidates, with both intensity and cardinality estimates proved from the original geometry. -/
theorem original_source_normalizedPhaseWalkCandidates_count_le_exp
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (z p : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m → Fin (m + 1) →
      (Fin (finrank ℝ S.covector.ker) → ℝ)) (R K : ℝ) :
    let v := (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.normalizedSourcePhaseCell T cut 0 0 R)).toReal
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
      (⋃ code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m,
        {s | K * (m : ℝ) ≤ ((s.2 : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))
          (D.normalizedSourcePhaseWalkEnvelope T cut z p code R ×ˢ {0})).toReal}) ≤
      Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
        (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) - 2 * v * (Real.exp 1 - 1)) * (m : ℝ)) := by
  dsimp only
  let v := ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
    (D.normalizedSourcePhaseCell T cut 0 0 R)
  have hv : v < (∞ : ℝ≥0∞) :=
    D.normalizedSourcePhaseCell_intensity_lt_top hF hw T hcut 0 0 R
  have hB (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) :
      MeasurableSet (D.normalizedSourcePhaseWalkEnvelope T cut z p code R) :=
    measurableSet_phaseCellEnvelopeFamily _ (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
      (fun j ↦ D.measurable_normalizedSourcePhaseCenter hF hw T hcut (z code j) (p code j))
      (D.measurableSet_sourcePhaseClocks cut) R
  have hrate (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) :=
    D.normalizedSourcePhaseWalkEnvelope_intensity_le hF hw T hcut z p code R
  have hfin : (m + 1 : ℝ≥0∞) * v ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top (by simp) hv.ne
  have hfinite (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) :
      ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
        (D.normalizedSourcePhaseWalkEnvelope T cut z p code R) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hfin (hrate code)
  have hreal (code : PhaseWalkCode (2 * finrank ℝ S.covector.ker) m) :
      (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
        (D.normalizedSourcePhaseWalkEnvelope T cut z p code R)).toReal ≤
          (2 * v.toReal) * (m : ℝ) := by
    have h := ENNReal.toReal_mono hfin (hrate code)
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_natCast, ENNReal.toReal_one] at h
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [ENNReal.toReal_nonneg (a := v)]
  have h := Q.original_source_candidates_count_le_exp
    (Finset.univ : Finset (PhaseWalkCode (2 * finrank ℝ S.covector.ker) m))
    (fun code ↦ D.normalizedSourcePhaseWalkEnvelope T cut z p code R)
    (fun code _ ↦ hB code) (fun code _ ↦ hfinite code)
    (by simpa only [Finset.card_univ] using
      (card_phaseWalkCode_le_exp (2 * finrank ℝ S.covector.ker) m hm))
    (fun code _ ↦ hreal code) (K := K)
  simpa [v, Nat.cast_mul] using h

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
