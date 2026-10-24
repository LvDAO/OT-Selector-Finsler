import OTSelector.PointProcess.LocalConfigurationTightness
import OTSelector.Probability.OriginalTargetConfiguration

/-!
# Tightness of the same original rooted integer target clouds

The spatial target marginal alone bounds the expected local point counts.
The existing integer-cloud compactness theorem gives tightness on the original
varying sample spaces. The weighted target and its atoms are never recoupled.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped BigOperators Classical ENNReal

noncomputable section
namespace OTSelector.Probability

open PointProcess PointProcess.LocalConfiguration

variable {ι B : Type*} [Fintype ι] [MetricSpace B] [ProperSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

local instance originalTargetConfigurationTightnessLocalInst1 : StandardBorelSpace ((ι → ℝ) × B) := inferInstance

local instance originalTargetConfigurationTightnessLocalInst2 : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalTargetConfigurationTightnessLocalInst3 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalTargetConfigurationTightnessLocalInst4 : PolishSpace (LocalConfiguration base) := vaguePolishSpace

/-- The original target labels seen from the same actual spatial root. -/
def cavityRootedTargetConfiguration {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ((ι → ℝ) × B)) (v : Ω × (ι → ℝ)) : LocalConfiguration base :=
  ofTuple base (fun j ↦ cavitySpatialTranslate v.2 (Y v.1 j))

theorem measurable_cavityRootedTargetConfiguration
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Y : Ω → Fin n → ((ι → ℝ) × B)) (hY : ∀ j, Measurable (fun ω ↦ Y ω j)) :
    Measurable (cavityRootedTargetConfiguration base Y) :=
  (measurable_ofTuple base n).comp (measurable_pi_lambda _ fun j ↦
    measurable_cavitySpatialTranslate.comp (measurable_snd.prodMk ((hY j).comp measurable_fst)))

/-- Original normalized spatial marginals give the uniform local counting bound,
allowing spatially dependent marks and arbitrary independent root laws. -/
theorem lintegral_cavityRootedTargetConfiguration_compact_le
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (Y : Ω → Fin (n + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, MeasurePreserving (fun ω ↦ Y ω j) P ν)
    (D : Set (ι → ℝ))
    (hν : ν.map Prod.fst = (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ • volume.restrict D)
    (K : Set ((ι → ℝ) × B)) (hK : IsCompact K) :
    (∫⁻ v, countingMeasure (cavityRootedTargetConfiguration base Y v) (interior K)
      ∂(P.prod ρ)) ≤ ENNReal.ofReal (volume.real (Prod.fst '' K)) := by
  have hobs (j : Fin (n + 1)) :
      MeasurePreserving (fun v : Ω × (ι → ℝ) ↦ (v.2, Y v.1 j)) (P.prod ρ) (ρ.prod ν) :=
    ((MeasurePreserving.id ρ).prod (hY j)).comp (Measure.measurePreserving_swap)
  apply lintegral_original_targetConfiguration_le (P.prod ρ) ρ ν Prod.snd
    (fun v j ↦ Y v.1 j) hobs
    (fun v ↦ cavitySpatialTranslate v.1 v.2) measurable_cavitySpatialTranslate
    isOpen_interior.measurableSet
  apply Eventually.of_forall
  intro z
  have hb := normalized_restrict_marked_translated_mass_le ν D
    (by positivity : 0 < (n : ℝ) + 1) hν K hK z
  have hb' := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ) + 1),
    ofReal_measureReal (measure_ne_top _ _)] at hb'
  simpa only [ENNReal.ofReal_add (by positivity : 0 ≤ (n : ℝ)) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one] using hb'

/-- Actual unweighted target laws are tight on the original varying sample spaces.
No prescribed limiting point process or atom correspondence is assumed. -/
theorem isTightMeasureSet_cavityRootedTargetConfiguration
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ρ : ℕ → Measure (ι → ℝ)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (Y : ∀ n, Ω n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, MeasurePreserving (fun ω ↦ Y n ω j) (P n) (ν n))
    (D : ℕ → Set (ι → ℝ))
    (hν : ∀ n, (ν n).map Prod.fst =
      (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ • volume.restrict (D n)) :
    IsTightMeasureSet (range fun n ↦
      ((P n).prod (ρ n)).map (cavityRootedTargetConfiguration base (Y n))) := by
  let K (j : ℕ) := Metric.closedBall base ((j + 1 : ℕ) : ℝ)
  let V (j : ℕ) := ENNReal.ofReal (volume.real (Prod.fst '' K j))
  apply isTightMeasureSet_of_lintegral_countingMeasure_ball_le _ V
    (fun _ ↦ ENNReal.ofReal_ne_top)
  rintro Q ⟨n, rfl⟩ j
  rw [lintegral_map]
  · calc
      _ ≤ ∫⁻ v, countingMeasure (cavityRootedTargetConfiguration base (Y n) v)
          (interior (K j)) ∂((P n).prod (ρ n)) :=
        lintegral_mono (fun _ ↦ measure_mono Metric.ball_subset_interior_closedBall)
      _ ≤ V j := lintegral_cavityRootedTargetConfiguration_compact_le base (m n)
        (P n) (ρ n) (ν n) (Y n) (hY n) (D n) (hν n) (K j) (isCompact_closedBall _ _)
  · exact (Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
      measurable_countingMeasure
  · exact measurable_cavityRootedTargetConfiguration base (Y n) (fun j ↦ (hY n j).measurable)

end OTSelector.Probability
