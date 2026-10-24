import OTSelector.PointProcess.LocalConfigurationTuple
import OTSelector.PointProcess.LocalConfiguration.MeasureSupport
import OTSelector.Probability.DirichletMarkedCloudMoments

/-!
# The original unweighted target cloud and its actual counting moments

The target array is encoded without resampling. Its weighted measure is carried
by this exact integer cloud. The original joint root/target marginal laws give
local first moments of its point count; no weight lower bound is needed.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped BigOperators Classical ENNReal

noncomputable section
namespace OTSelector.Probability

open PointProcess PointProcess.LocalConfiguration

section WeightedSupport

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] {base : X}

/-- The original weighted measure is carried by precisely the same target array. -/
theorem supportedOnConfiguration_semidiscreteTargetCloud {m : ℕ}
    (p : Fin (m + 1) → ℝ) (Y : Fin (m + 1) → X) (N : ℝ) :
    SupportedOnConfiguration (ofTuple base Y) (semidiscreteLocalTargetCloud p Y N) := by
  apply (supportedOnConfiguration_iff_ae_mem _ _).mpr
  rw [ae_iff]
  let S := Function.support (multiplicity (ofTuple base Y))
  have hS : MeasurableSet S := (isClosed_multiplicity_support _).measurableSet
  change semidiscreteTargetCloud p Y N Sᶜ = 0
  have hmem (j : Fin (m + 1)) : Y j ∈ S :=
    (multiplicity_ofTuple_ne_zero_iff Y (Y j)).mpr ⟨j, rfl⟩
  simp [semidiscreteTargetCloud_eq_sum, Measure.smul_apply,
    Measure.finsetSum_apply, Measure.dirac_apply' _ hS.compl, hmem]

end WeightedSupport

section CountMoments

variable {Ω R X : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}

omit [BorelSpace X] in
/-- The first moment counts each original label once. Only the displayed joint
root/target marginals are used; independence between labels is unnecessary here. -/
theorem lintegral_original_targetConfiguration
    {n : ℕ} (P : Measure Ω) (ρ : Measure R) [SFinite ρ]
    (ν : Measure X) [SFinite ν]
    (U : Ω → R) (Y : Ω → Fin n → X)
    (hobs : ∀ j, MeasurePreserving (fun ω ↦ (U ω, Y ω j)) P (ρ.prod ν))
    (T : R × X → X) (hT : Measurable T) {W : Set X} (hW : MeasurableSet W) :
    (∫⁻ ω, countingMeasure (ofTuple base (fun j ↦ T (U ω, Y ω j))) W ∂P) =
      (n : ℝ≥0∞) * ∫⁻ z, ν {y | T (z, y) ∈ W} ∂ρ := by
  let H := T ⁻¹' W
  have hH : MeasurableSet H := hT hW
  have hm (j : Fin n) : Measurable (fun ω ↦
      W.indicator (fun _ ↦ (1 : ℝ≥0∞)) (T (U ω, Y ω j))) :=
    (measurable_const.indicator hW).comp (hT.comp (hobs j).measurable)
  simp only [countingMeasure_ofTuple, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hW]
  change (∫⁻ ω, ∑ j, W.indicator (fun _ ↦ (1 : ℝ≥0∞))
    (T (U ω, Y ω j)) ∂P) = _
  rw [lintegral_finsetSum _ (fun j _ ↦ hm j)]
  have heq (j : Fin n) :
      (∫⁻ ω, W.indicator (fun _ ↦ (1 : ℝ≥0∞)) (T (U ω, Y ω j)) ∂P) =
        (ρ.prod ν) H := by
    rw [(hobs j).lintegral_comp
      (f := fun v ↦ W.indicator (fun _ ↦ (1 : ℝ≥0∞)) (T v))
      ((measurable_const.indicator hW).comp hT)]
    change (∫⁻ v, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) v ∂(ρ.prod ν)) = _
    simp [lintegral_indicator hH]
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Measure.prod_apply hH]
  rfl

omit [BorelSpace X] in
/-- A uniform original local expected-count bound integrates over any root law. -/
theorem lintegral_original_targetConfiguration_le
    {n : ℕ} (P : Measure Ω) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (ν : Measure X) [SFinite ν]
    (U : Ω → R) (Y : Ω → Fin n → X)
    (hobs : ∀ j, MeasurePreserving (fun ω ↦ (U ω, Y ω j)) P (ρ.prod ν))
    (T : R × X → X) (hT : Measurable T) {W : Set X} (hW : MeasurableSet W)
    {V : ℝ≥0∞} (hb : ∀ᵐ z ∂ρ, (n : ℝ≥0∞) * ν {y | T (z, y) ∈ W} ≤ V) :
    (∫⁻ ω, countingMeasure (ofTuple base (fun j ↦ T (U ω, Y ω j))) W ∂P) ≤ V := by
  rw [lintegral_original_targetConfiguration P ρ ν U Y hobs T hT hW]
  have hm : Measurable (fun z ↦ ν {y | T (z, y) ∈ W}) :=
    measurable_measure_prodMk_left (hT hW)
  rw [← lintegral_const_mul _ hm]
  simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hb

end CountMoments
end OTSelector.Probability
