import OTSelector.Reconstruction.OriginalIIDFinalValueFieldProbe
import OTSelector.Reconstruction.FinslerOriginalClosedWindowPressureIdentification
import OTSelector.Reconstruction.FinslerOriginalSeedComparisonConstruction

/-! A continuous original seed probe gives exactly the final physical-root reverse comparison. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : F.CalibratedLevelSeedPatch u} {w : S.covector.ker} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {a : M → Z} {b : Z × ℝ → M}

/-- The bounded continuous physical probe read along the original complete seed,
using the original potential clocks and level shift. -/
def originalCompleteSeedPhysicalProbe (S : F.CalibratedLevelSeedPatch u) (w : S.covector.ker)
    (hw : w ∈ S.labels) (hF : F.IsSmoothStronglyConvex) (f : M × M →ᵇ ℝ) : ℝ × ℝ →ᵇ ℝ :=
  f.compContinuous ⟨(fun p ↦ (S.curve w (p.1-S.level),S.curve w (p.2-S.level))),
    ((continuous_curve_of_seed S hF hw).comp (continuous_fst.sub continuous_const)).prodMk
      ((continuous_curve_of_seed S hF hw).comp (continuous_snd.sub continuous_const))⟩

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Reading a physical test along one seed preserves its original uniform bound. -/
theorem norm_originalCompleteSeedPhysicalProbe_le (S : F.CalibratedLevelSeedPatch u) (w : S.covector.ker)
    (hw : w ∈ S.labels) (hF : F.IsSmoothStronglyConvex) (f : M × M →ᵇ ℝ) :
    ‖originalCompleteSeedPhysicalProbe S w hw hF f‖ ≤ ‖f‖ :=
  f.norm_compContinuous_le _

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Z] in
/-- The actual full inverse on the regular domain and original support span
identify the physical final probe with the continuous complete-seed probe,
both in every genuine candidate value and at every original finite pressure scale.
This discharges the readout adaptation of the pending local reverse theorem. -/
theorem OriginalSeedConditionalMoments.original_focal_physical_reverse_of_seed_probe_reverse
    (D : OriginalSeedConditionalMoments S w α β) (hw : w ∈ S.labels)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x ≤ u y) ↔ u y-u x=dist x y)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x,u x)=x)
    (f : M × M →ᵇ ℝ) (gap : ℝ)
    (hseedReverse : ∀ Qseed : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β
        (D.originalFocalKinetic gap)
        (fun x y ↦ f (S.curve w (x-S.level),S.curve w (y-S.level))),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
        (D.originalFocalKinetic gap)
        (fun x y ↦ f (S.curve w (x-S.level),S.curve w (y-S.level))) R t) ≤ Qseed.value t) :
    ∀ Qphysical : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f (a (S.curve w 0))),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f (a (S.curve w 0))) R t) ≤ Qphysical.value t := by
  have hends := D.support.original_inverse_ae hF hcomplete hu horder hinv hw
  intro Q t
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hs : ∀ᵐ m ∂η, b (a (S.curve w 0),m.1.1) = S.curve w (m.1.1-S.level) := by
    apply ae_of_ae_map (μ := η) (f := fun m ↦ m.1.1)
      (p := fun x ↦ b (a (S.curve w 0),x) = S.curve w (x-S.level)) measurable_fst.fst.aemeasurable
    rw [Q.source_clock]
    exact hends.1
  have ht : ∀ᵐ m ∂η, b (a (S.curve w 0),m.1.2) = S.curve w (m.1.2-S.level) := by
    apply ae_of_ae_map (μ := η) (f := fun m ↦ m.1.2)
      (p := fun y ↦ b (a (S.curve w 0),y) = S.curve w (y-S.level)) measurable_fst.snd.aemeasurable
    rw [Q.target_clock]
    exact hends.2
  have heq : ∀ᵐ m ∂η, f (S.curve w (m.1.1-S.level),S.curve w (m.1.2-S.level)) =
      originalPhysicalRootProbe b f (a (S.curve w 0)) m.1.1 m.1.2 := by
    filter_upwards [hs,ht] with m h₀ h₁
    simp only [originalPhysicalRootProbe,h₀,h₁]
  let Qseed : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β
      (D.originalFocalKinetic gap)
      (fun x y ↦ f (S.curve w (x-S.level),S.curve w (y-S.level))) := Q.withAEEqProbe heq
  have hscale (R : ℝ) : legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
      (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f (a (S.curve w 0))) R t =
      legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
      (D.originalFocalKinetic gap) (fun x y ↦ f (S.curve w (x-S.level),S.curve w (y-S.level))) R t := by
    apply legalMarkedScalePressure_congr_of_ae_on_legal
    filter_upwards [ae_fst_of_ae hends.1,ae_snd_of_ae hends.2] with p h₀ h₁
    intro _
    exact ⟨fun _ ↦ rfl,by simp only [originalPhysicalRootProbe,h₀,h₁]⟩
  rw [show (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
      (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f (a (S.curve w 0))) R t) =
      (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id α β
      (D.originalFocalKinetic gap) (fun x y ↦ f (S.curve w (x-S.level),S.curve w (y-S.level))) R t) from funext hscale]
  exact (hseedReverse Qseed t).trans_eq (Q.withAEEqProbe_value heq t)

end OTSelector.Reconstruction
