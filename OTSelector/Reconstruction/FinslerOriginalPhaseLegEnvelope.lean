import OTSelector.Reconstruction.OriginalSeedCompliance
import OTSelector.Reconstruction.EndpointWindowDeterminantMoments

/-!
# Original deterministic phase-leg determinant envelopes

Every interior cut uses the genuine original compliance integral. Its active
source and target leg determinants are integrable under the unchanged original
clock laws, including singular ends and interleaved populations.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- The original left source envelope at an actual interior relative cut is
finite. It uses every source allowed by the original clock law before any
adaptive edge family or random phase curve is selected. -/
theorem integrable_original_source_phaseLeg_determinant
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) :
    Integrable ({a : ℝ | a - (S.level : ℝ) < cut}.indicator
      (fun a ↦ (1 + ∫ t in (a - S.level)..cut, originalSeedKernel S w t).det)) μ := by
  have hB : MeasurableSet {a : ℝ | a - (S.level : ℝ) < cut} :=
    measurableSet_lt (measurable_id.sub_const _) measurable_const
  have hm := ((D.original_kernel_moments hF hw hcut).1.1).indicator hB
  apply hm.congr
  filter_upwards [D.support.source.ae_open] with a ha
  by_cases hact : a - (S.level : ℝ) < cut
  · simp only [indicator_of_mem (show a ∈ {a : ℝ | a - (S.level : ℝ) < cut} from hact)]
    rw [abs_compliancePrimitive_eq (fun t ht ↦ (D.original_kernel_regular hF hw).2 t ht |>.posSemidef)
      hcut ha, ite_eq_left hact.le, ← intervalIntegral.integral_symm]
  · simp only [indicator_of_notMem (show a ∉ {a : ℝ | a - (S.level : ℝ) < cut} from hact)]

omit [BorelSpace E] in
/-- The original right target phase envelope is finite at the same actual
cut. The two conditional supports may interleave freely. -/
theorem integrable_original_target_phaseLeg_determinant
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) :
    Integrable ({b : ℝ | cut < b - (S.level : ℝ)}.indicator
      (fun b ↦ (1 + ∫ t in cut..(b - S.level), originalSeedKernel S w t).det)) ν := by
  have hB : MeasurableSet {b : ℝ | cut < b - (S.level : ℝ)} :=
    measurableSet_lt measurable_const (measurable_id.sub_const _)
  have hm := ((D.original_kernel_moments hF hw hcut).2.1).indicator hB
  apply hm.congr
  filter_upwards [D.support.target.ae_open] with b hb
  by_cases hact : cut < b - (S.level : ℝ)
  · simp only [indicator_of_mem (show b ∈ {b : ℝ | cut < b - (S.level : ℝ)} from hact)]
    rw [abs_compliancePrimitive_eq (fun t ht ↦ (D.original_kernel_regular hF hw).2 t ht |>.posSemidef)
      hcut hb, ite_eq_right (not_le.mpr hact)]
  · simp only [indicator_of_notMem (show b ∉ {b : ℝ | cut < b - (S.level : ℝ)} from hact)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
