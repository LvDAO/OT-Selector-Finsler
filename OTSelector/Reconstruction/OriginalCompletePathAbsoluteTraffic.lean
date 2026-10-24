import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell
import OTSelector.Reconstruction.FinslerOriginalPathMeasurability

/-!
# Actual complete-path absolute traffic has finite first moment

The genuine original weighted energy already supplies total Palm/clock path integrability.
The exact original Campbell law then gives finite complete-path absolute traffic in each
compact physical smoothing kernel, including actual focal endpoints.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual complete original path's offset is jointly Borel in its full paired mark and
the unchanged original physical clock. -/
theorem measurable_originalSeedPathOffset_joint (S : CalibratedLevelSeedPatch F u)
    (hF : F.IsSmoothStronglyConvex) {w : S.covector.ker} (hw : w ∈ S.labels) :
    Measurable (fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1) :=
  (measurable_originalSeedCompletePath S hF hw).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

/-- Complete-path absolute traffic of the unchanged first matching, observed through a
nonnegative physical kernel. The actual half-open occupation retains both original clocks. -/
def originalSeedCompletePathAbsoluteTraffic (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker)
    (fun z ↦ originalSeedPathOffset S w z.2 z.1) (fun x ↦ ENNReal.ofReal (η x))
    (fun z ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖) s

theorem measurable_originalSeedCompletePathAbsoluteTraffic
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) :
    Measurable (originalSeedCompletePathAbsoluteTraffic S w η) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The total true-Palm/physical-clock speed is exactly the mean original path length. -/
theorem lintegral_original_clockOccupation_norm_eq_pathLength
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    (∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖
      ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) =
      ENNReal.ofReal (∫ m, originalSeedPairPathLength S w m
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.palm_probability
  have ho := D.integrable_original_clockOccupation_prod hF hw hbounds Q
  have hp := D.integrable_pathLength_of_original_weighted_stationary hF hw hbounds Q
  have hpnonneg : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      0 ≤ originalSeedPairPathLength S w m := by
    filter_upwards [Q.ae_palm_forward] with m hm
    rw [← integral_norm_originalSeedClockOccupation_eq_pathLength S w m hm.le]
    exact integral_nonneg (fun _ ↦ norm_nonneg _)
  calc
    _ = ∫⁻ m, ENNReal.ofReal (originalSeedPairPathLength S w m)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
      apply lintegral_congr_ae
      filter_upwards [ho.prod_right_ae, Q.ae_palm_forward] with m hmi hm
      rw [← ofReal_integral_eq_lintegral_ofReal hmi.norm
        (Eventually.of_forall (fun c ↦ norm_nonneg (originalSeedClockOccupation S w c m))),
        integral_norm_originalSeedClockOccupation_eq_pathLength S w m hm.le]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal hp hpnonneg).symm

/-- The expected actual complete-path absolute traffic is exactly the spatial kernel mass
times the original Palm/clock total speed, with all actual original geometry retained. -/
theorem lintegral_original_completePathAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η) :
    (∫⁻ s, originalSeedCompletePathAbsoluteTraffic S w η s
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      (∫⁻ x, ENNReal.ofReal (η x) ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        ∫⁻ m, ∫⁻ c : ℝ, ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖
          ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law :=
  Q.lintegral_completePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal

/-- Every actual original weighted law has finite first moment of full absolute physical
traffic for each integrable physical kernel. No displacement-square or cycle hypothesis is needed. -/
theorem lintegral_original_completePathAbsoluteTraffic_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηm : Measurable η) (hηi : Integrable η (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) :
    (∫⁻ s, originalSeedCompletePathAbsoluteTraffic S w η s
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) < ⊤ := by
  rw [D.lintegral_original_completePathAbsoluteTraffic hF hw Q hηm]
  have hη : (∫⁻ x, ENNReal.ofReal (η x)
      ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (le_abs_self (η x))))
    exact (hasFiniteIntegral_iff_norm η).mp hηi.hasFiniteIntegral
  have ho := D.integrable_original_clockOccupation_prod hF hw hbounds Q
  have ho' := (hasFiniteIntegral_iff_norm _).mp ho.hasFiniteIntegral
  rw [MeasureTheory.lintegral_prod _
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.aemeasurable] at ho'
  exact ENNReal.mul_lt_top hη ho'

/-- The same actual complete-path absolute traffic is finite in almost every original scene. -/
theorem ae_original_completePathAbsoluteTraffic_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηm : Measurable η) (hηi : Integrable η (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalSeedCompletePathAbsoluteTraffic S w η s < ⊤ :=
  ae_lt_top (measurable_originalSeedCompletePathAbsoluteTraffic S hF hw hηm)
    (D.lintegral_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hηm hηi).ne

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
