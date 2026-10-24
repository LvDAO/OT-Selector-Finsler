import OTSelector.Reconstruction.FinslerOriginalCompletePathEndpointIdentity
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Every original full path stays within its actual finite length of its source

The bound follows from the same physical clock occupation and genuine original
path derivative. It uses neither a path-diameter moment nor an endpoint proxy.
-/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original full path at every actual clock remains within its own full
physical path length of the unchanged source position. -/
theorem norm_originalSeedCompletePath_sub_source_le_pathLength
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {c : ℝ} (hc : c ∈ Icc m.1.1 m.1.2) :
    ‖originalSeedCompletePath S w x m c - x‖ ≤ originalSeedPairPathLength S w m := by
  have hab : m.1.1 ≤ m.1.2 := hc.1.trans hc.2
  have ho := D.integrable_original_clockOccupation_pathwise hF hw m ha hb hab
  have hspan : ∀ r ∈ Icc m.1.1 c, r - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    intro r hr
    exact ⟨by linarith [ha.1, hr.1], by linarith [hb.2, hr.2, hc.2]⟩
  have hcont : ContinuousOn (originalSeedCompletePath S w x m) (Icc m.1.1 c) :=
    (D.continuousOn_originalSeedCompletePath hF hw x m ha hb).mono
      (Icc_subset_Icc le_rfl hc.2)
  have hdiff : DifferentiableOn ℝ (originalSeedCompletePath S w x m) (Ioo m.1.1 c) := by
    intro r hr
    exact (D.hasDerivAt_originalSeedCompletePath hF hw x m ha
      (hspan r (Ioo_subset_Icc_self hr))).differentiableAt.differentiableWithinAt
  have hnorm : ∀ᵐ r : ℝ, r ∈ Ioo m.1.1 c →
      ‖deriv (originalSeedCompletePath S w x m) r‖ ≤ ‖originalSeedClockOccupation S w r m‖ := by
    apply Filter.Eventually.of_forall
    intro r hr
    rw [(D.hasDerivAt_originalSeedCompletePath hF hw x m ha
      (hspan r (Ioo_subset_Icc_self hr))).deriv,
      originalSeedClockOccupation_eq_indicator_velocity,
      Set.indicator_of_mem (show r ∈ Ico m.1.1 m.1.2 from
        ⟨hr.1.le, hr.2.trans_le hc.2⟩)]
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hc.1 hcont hdiff hnorm
    ho.norm.intervalIntegrable
  rw [originalSeedCompletePath_source] at h
  apply h.trans
  rw [← integral_norm_originalSeedClockOccupation_eq_pathLength S w m hab,
    intervalIntegral.integral_of_le hc.1]
  exact setIntegral_le_integral ho.norm (Filter.Eventually.of_forall (fun r ↦ norm_nonneg _))

/-- The actual original endpoint displacement is bounded by the same full path length. -/
theorem norm_original_pair_displacement_le_pathLength
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2) :
    ‖m.2‖ ≤ originalSeedPairPathLength S w m := by
  have h := D.norm_originalSeedCompletePath_sub_source_le_pathLength hF hw 0 m ha hb
    (right_mem_Icc.mpr hab.le)
  simpa only [D.originalSeedCompletePath_target hF hw 0 m ha hb hab, zero_add, sub_zero] using h

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
