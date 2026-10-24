import OTSelector.Reconstruction.FinslerOriginalCenteredClockOccupation

/-!
# The same original clock occupation has finite total absolute traffic

Integrating the actual occupied compliance velocity over original physical
clock equals the original compliance path length. Its established Palm first
moment therefore supplies joint clock/Palm integrability, including focal
endpoint degeneration and without a displacement second moment.
-/
open Set Function MeasureTheory Manifold Matrix Module
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The occupation is exactly the original compliance velocity on the
half-open physical clock interval and vanishes elsewhere. -/
theorem originalSeedClockOccupation_eq_indicator_velocity
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) (c : ℝ) :
    originalSeedClockOccupation S w c m =
      (Ico m.1.1 m.1.2).indicator
        (fun c ↦ originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m) c := by
  by_cases hc : m.1.1 ≤ c ∧ c < m.1.2 <;>
    simp [originalSeedClockOccupation, originalSeedCrossingMomentum, originalClockCrossingSet,
      Set.indicator, hc]

/-- Total original physical-clock speed equals the unchanged original
compliance path length, with no change to either clock endpoint. -/
theorem integral_norm_originalSeedClockOccupation_eq_pathLength
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (hab : m.1.1 ≤ m.1.2) :
    (∫ c, ‖originalSeedClockOccupation S w c m‖) = originalSeedPairPathLength S w m := by
  have he : (fun c ↦ ‖originalSeedClockOccupation S w c m‖) =
      (Ico m.1.1 m.1.2).indicator
        (fun c ↦ ‖originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m‖) := by
    funext c
    rw [originalSeedClockOccupation_eq_indicator_velocity]
    by_cases hc : c ∈ Ico m.1.1 m.1.2 <;> simp [hc]
  rw [he, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_comp_sub_right
    (fun c ↦ ‖originalSeedKernel S w c *ᵥ originalSeedPairMomentum S w m‖) (S.level : ℝ)

/-- The complete original clock/edge occupation readout is measurable,
including its actual half-open crossing event and original kernel. -/
theorem measurable_originalSeedClockOccupation
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedClockOccupation S w z.2 z.1) := by
  have hK : Measurable (originalSeedKernel S w) := by
    have h := (S.measurable_familyLabelKernel hF (Module.finBasis ℝ S.covector.ker)).comp
      ((measurable_const : Measurable (fun _ : ℝ ↦ (⟨w, hw⟩ : S.labels))).prodMk measurable_id)
    change Measurable (fun t : ℝ ↦ originalSeedKernel S w t)
    simpa only [originalSeedKernel, Function.comp_def, id_eq] using h
  have hmul : Continuous (fun z :
      Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ z.1 *ᵥ z.2) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hv : Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedKernel S w (z.2 - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w z.1) :=
    hmul.measurable.comp ((hK.comp (measurable_snd.sub_const (S.level : ℝ))).prodMk
      ((measurable_originalSeedPairMomentum S hF hw).comp measurable_fst))
  have hB : MeasurableSet {z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ |
      z.1.1.1 ≤ z.2 ∧ z.2 < z.1.1.2} :=
    (measurableSet_le measurable_fst.fst.fst measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.fst.snd)
  convert hv.indicator hB using 1
  funext z
  exact originalSeedClockOccupation_eq_indicator_velocity S w z.1 z.2

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Each actual interior original path is integrable in its original
physical clock; the original kernel is continuous on that unchanged interval. -/
theorem integrable_original_clockOccupation_pathwise
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 ≤ m.1.2) :
    Integrable (fun c ↦ originalSeedClockOccupation S w c m) := by
  have hK := (D.original_kernel_regular hF hw).1
  have hsub : MapsTo (fun c : ℝ ↦ c - (S.level : ℝ))
      (Icc m.1.1 m.1.2) (Ioo D.lo D.hi) := by
    intro c hc
    exact ⟨by linarith [ha.1, hc.1], by linarith [hb.2, hc.2]⟩
  have hkc := hK.comp (continuous_id.sub continuous_const).continuousOn hsub
  have hmul : Continuous (fun z :
      Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ z.1 *ᵥ z.2) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hv : ContinuousOn
      (fun c ↦ originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)
      (Icc m.1.1 m.1.2) :=
    hmul.comp_continuousOn (hkc.prodMk continuousOn_const)
  have hi : IntegrableOn
      (fun c ↦ originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)
      (Icc m.1.1 m.1.2) volume := hv.integrableOn_Icc
  have hic : IntegrableOn
      (fun c ↦ originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)
      (Ico m.1.1 m.1.2) := hi.mono_set Ico_subset_Icc_self
  have he := (integrable_indicator_iff measurableSet_Ico).mpr hic
  apply he.congr
  exact .of_forall fun c ↦ (originalSeedClockOccupation_eq_indicator_velocity S w m c).symm

/-- The original weighted energy and conditional geometric moments imply
finite total absolute clock occupation on the same genuine true Palm. -/
theorem integrable_original_clockOccupation_prod
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    Integrable
      (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
        originalSeedClockOccupation S w z.2 z.1)
      ((legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).prod volume) := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  have ha : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.1), a - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      rw [Q.source_clock]
      exact D.support.source.ae_open
    exact ae_of_ae_map measurable_fst.fst.aemeasurable h
  have hb : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have h : ∀ᵐ b ∂η.map (fun m ↦ m.1.2), b - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      rw [Q.target_clock]
      exact D.support.target.ae_open
    exact ae_of_ae_map measurable_fst.snd.aemeasurable h
  apply (integrable_prod_iff
    (measurable_originalSeedClockOccupation S hF hw).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ha, hb, Q.ae_palm_forward] with m ha hb hf
    exact D.integrable_original_clockOccupation_pathwise hF hw m ha hb hf.le
  · apply (D.integrable_pathLength_of_original_weighted_stationary hF hw hbounds Q).congr
    filter_upwards [Q.ae_palm_forward] with m hm
    exact (integral_norm_originalSeedClockOccupation_eq_pathLength S w m hm.le).symm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
