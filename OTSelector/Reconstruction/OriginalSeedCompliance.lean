import OTSelector.Reconstruction.PairedComplianceMoments
import OTSelector.Geometry.FinslerSeedKernelMeasurabilityComparison

/-!
# The literal original length kernel and all conditional pairings

The moment witness identifies its comparison kernel with the original seed's
intrinsic length Hessian inverse at every time. Marginal moments then control the
actual integral between each paired pair of original potential times, uniformly
over the entire coupling set at this fixed label and root.
-/

open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The literal original label Hessian inverse in one fixed actual finite basis. -/
def originalSeedKernel (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (t : ℝ) :
    Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ :=
  (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
    (fun q ↦ S.curve q.1 q.2) (w, t))⁻¹

namespace OriginalSeedConditionalMoments

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- The comparison computes the literal original kernel for every original time. -/
theorem original_kernel_eq (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    originalSeedKernel S w = D.comparison.intrinsicKernel (Module.finBasis ℝ S.covector.ker) :=
  funext (S.familyLabelKernel_eq_comparison hF (Module.finBasis ℝ S.covector.ker)
    hw D.comparison D.curve_eq D.phase_jet)

omit [BorelSpace E] in
/-- The original kernel itself is continuous and positive on the entire conditional span. -/
theorem original_kernel_regular (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ContinuousOn (originalSeedKernel S w) (Ioo D.lo D.hi) ∧
      ∀ t ∈ Ioo D.lo D.hi, (originalSeedKernel S w t).PosDef := by
  rw [D.original_kernel_eq hF hw]
  have hactive : Ioo D.lo D.hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.support.calibrated
  exact D.comparison.continuousOn_posDef_intrinsicKernel_of_original hF
    (Module.finBasis ℝ S.covector.ker) S.normalization D.curve_eq
    (fun old t _ hx ↦ D.phase_jet old t hx)
    (fun old t ht hx ↦ D.jacobian_pos old t (hactive ht) hx)

omit [BorelSpace E] in
/-- Both moment conclusions hold for the literal original Hessian inverse. -/
theorem original_kernel_moments (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi) :
    OriginalClockComplianceMoments μ S.level (originalSeedKernel S w) root ∧
      OriginalClockComplianceMoments ν S.level (originalSeedKernel S w) root := by
  rw [D.original_kernel_eq hF hw]
  exact ⟨D.source_moments root hroot, D.target_moments root hroot⟩

omit [BorelSpace E] in
/-- The original compliance primitive is strongly measurable under each original
conditional law, including when the endpoint integrand is singular. -/
theorem original_primitive_aestronglyMeasurable
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi) :
    AEStronglyMeasurable (fun x ↦ ∫ t in root..(x - S.level), originalSeedKernel S w t) μ ∧
      AEStronglyMeasurable (fun x ↦ ∫ t in root..(x - S.level), originalSeedKernel S w t) ν := by
  have hcont := continuousOn_compliancePrimitive (D.original_kernel_regular hF hw).1 hroot
  have finish {η : Measure ℝ} (hη : ∀ᵐ t ∂η.map (fun x : ℝ ↦ x - S.level),
      t ∈ Ioo D.lo D.hi) :
      AEStronglyMeasurable
        (fun x ↦ ∫ t in root..(x - S.level), originalSeedKernel S w t) η := by
    have hm := hcont.aestronglyMeasurable
      (μ := η.map (fun x : ℝ ↦ x - S.level)) measurableSet_Ioo
    rw [Measure.restrict_eq_self_of_ae_mem hη] at hm
    exact hm.comp_measurable (measurable_id.sub_const _)
  exact ⟨finish (by simpa only [sub_zero] using D.support.source.seedClock.ae_open),
    finish (by simpa only [sub_zero] using D.support.target.seedClock.ae_open)⟩

omit [BorelSpace E] in
/-- Every coupling of the original conditionals has the same finite bound for the
actual pair compliance integral, with the precise power-sum constant from the paper. -/
theorem paired_original_compliance_moments
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {root : ℝ} (hroot : root ∈ Ioo D.lo D.hi)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π μ ν)
    {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) :
    Integrable (fun p ↦ ‖∫ t in (p.1 - S.level)..(p.2 - S.level),
      originalSeedKernel S w t‖ ^ r) π ∧
      (∫ p, ‖∫ t in (p.1 - S.level)..(p.2 - S.level), originalSeedKernel S w t‖ ^ r ∂π) ≤
        (2 : ℝ) ^ max (r - 1) 0 *
          ((∫ x, ‖∫ t in root..(x - S.level), originalSeedKernel S w t‖ ^ r ∂μ) +
            ∫ y, ‖∫ t in root..(y - S.level), originalSeedKernel S w t‖ ^ r ∂ν) := by
  obtain ⟨hmμ, hmν⟩ := D.original_primitive_aestronglyMeasurable hF hw hroot
  obtain ⟨hμ, hν⟩ := D.original_kernel_moments hF hw hroot
  have hpair := paired_norm_sub_rpow_integrable_bound hπ hmμ hmν hr0.le
    (hμ.2 r hr0 hr2) (hν.2 r hr0 hr2)
  have ha : ∀ᵐ p ∂π, p.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_Ioo.preimage (measurable_id.sub_const _))).mp
    rw [hπ.1]
    exact D.support.source.ae_open
  have hb : ∀ᵐ p ∂π, p.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_Ioo.preimage (measurable_id.sub_const _))).mp
    rw [hπ.2]
    exact D.support.target.ae_open
  have heq : (fun p : ℝ × ℝ ↦
      ‖(∫ t in root..(p.2 - S.level), originalSeedKernel S w t) -
        ∫ t in root..(p.1 - S.level), originalSeedKernel S w t‖ ^ r) =ᵐ[π]
      (fun p ↦ ‖∫ t in (p.1 - S.level)..(p.2 - S.level), originalSeedKernel S w t‖ ^ r) := by
    filter_upwards [ha, hb] with p ha hb
    have hK := (D.original_kernel_regular hF hw).1
    rw [intervalIntegral.integral_interval_sub_left
      ((hK.mono (ordConnected_Ioo.uIcc_subset hroot hb)).intervalIntegrable (μ := volume))
      ((hK.mono (ordConnected_Ioo.uIcc_subset hroot ha)).intervalIntegrable (μ := volume))]
  exact ⟨hpair.1.congr heq, (integral_congr_ae heq) ▸ hpair.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
