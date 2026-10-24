import OTSelector.Reconstruction.FinslerOriginalPhaseBadEventSecondMoment

/-! # One fixed original-input envelope contains every admissible adaptive phase tube -/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

/-- Both physical phase-coordinate projections have norm at most the norm
of their literal common phase vector. -/
theorem norm_position_le_phasePairVector {q : ℕ} (z p : Fin q → ℝ) :
    ‖z‖ ≤ ‖phasePairVector z p‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [phasePairVector_position] using
    norm_le_pi_norm (phasePairVector z p) (phasePositionIndex q i)

theorem norm_momentum_le_phasePairVector {q : ℕ} (z p : Fin q → ℝ) :
    ‖p‖ ≤ ‖phasePairVector z p‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [phasePairVector_momentum] using
    norm_le_pi_norm (phasePairVector z p) (phaseMomentumIndex q i)

/-- The prescribed root and speed bound place every phase curve inside its
single deterministic radius-2m ball before the input is observed. -/
theorem norm_phaseCurve_le_two_mul {q m : ℕ}
    (γ : ℝ → Fin q → ℝ) (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖γ t‖ ≤ 2 * (m : ℝ) := by
  calc
    ‖γ t‖ = ‖(γ t - γ 0) + γ 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖γ t - γ 0‖ + ‖γ 0‖ := norm_add_le _ _
    _ ≤ (m : ℝ) * |t - 0| + (m : ℝ) :=
      add_le_add (hLip t ht 0 ⟨le_rfl, zero_le_one⟩) hroot
    _ ≤ 2 * (m : ℝ) := by
      rw [sub_zero, abs_of_nonneg ht.1]
      nlinarith [mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg (α := ℝ) m)]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The fixed complete original source envelope for all phase curves of scale m. -/
def adaptiveGlobalSourceEnvelope (cut : ℝ) (m : ℕ) (r : ℝ) :
    Set (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) :=
  markedPhaseSourceCell 1 (D.sourcePhaseLeg cut) 0 (D.sourcePhaseClocks cut) (2 * (m : ℝ) + r)

theorem measurableSet_adaptiveGlobalSourceEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    MeasurableSet (D.adaptiveGlobalSourceEnvelope cut m r) :=
  measurableSet_markedPhaseSourceCell 1 (D.measurable_sourcePhaseLeg hF hw hcut)
    measurable_const (D.measurableSet_sourcePhaseClocks cut) _

/-- Original focal determinant integrability supplies finite intensity of the
whole fixed envelope; compactness of its clock-marked shape is unnecessary. -/
theorem adaptiveGlobalSourceEnvelope_intensity_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (m : ℕ) (r : ℝ) :
    ((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
      (D.adaptiveGlobalSourceEnvelope cut m r) < (∞ : ℝ≥0∞) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  exact D.sourcePhaseCell_intensity_lt_top hF hw hcut (by simp) measurable_const _

/-- Every actual path/momentum tube point of any admissible curve belongs
to the same fixed original source envelope, including on its bad event. -/
theorem source_pathPhaseTube_mem_adaptiveGlobalSourceEnvelope
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ}
    (γ : ℝ → Fin (2 * finrank ℝ S.covector.ker) → ℝ)
    (hroot : ‖γ 0‖ ≤ (m : ℝ))
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ s - γ t‖ ≤ (m : ℝ) * |s - t|) {r : ℝ} (hr : 0 ≤ r)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (edge : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : edge.1.1 ∈ D.sourcePhaseClocks cut)
    (htube : ∃ t ∈ Icc (0 : ℝ) 1,
      ‖phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
        (originalSeedPairMomentum S w edge) - γ t‖ ≤ r) :
    (x, edge.1.1) ∈ D.adaptiveGlobalSourceEnvelope cut m r := by
  obtain ⟨t, ht, hnear⟩ := htube
  have hphase : ‖phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
      (originalSeedPairMomentum S w edge)‖ ≤ 2 * (m : ℝ) + r := by
    calc
      _ = ‖(phasePairVector (originalSeedCompletePath S w x edge (cut + S.level))
          (originalSeedPairMomentum S w edge) - γ t) + γ t‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith [norm_phaseCurve_le_two_mul γ hroot hLip ht]
  have hmem := D.original_pathPhase_source_mem hF hw hcut x 0 0 edge ha
    (R := 2 * (m : ℝ) + r) (by positivity)
    (by simpa only [sub_zero] using
      (norm_position_le_phasePairVector _ _).trans hphase)
    (by simpa only [sub_zero] using
      (norm_momentum_le_phasePairVector _ _).trans hphase)
  have hc : D.sourcePhaseCenter cut 0 0 = 0 := by
    funext a
    simp [sourcePhaseCenter]
  simpa only [hc, adaptiveGlobalSourceEnvelope] using hmem

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
