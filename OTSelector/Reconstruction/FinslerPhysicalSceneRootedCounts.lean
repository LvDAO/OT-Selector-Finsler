import OTSelector.PointProcess.LocalConfigurationTightness
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSubsequence
import OTSelector.Probability.OriginalTargetConfigurationTightness

/-!
# Original integer target counts under the actual Haar root

The same finite target array, including repeated labels, has local rooted count
moments bounded by spatial window volume when the original root normalization
is the number of labels. These moments give tightness of its integer-cloud
laws without a density or independence assumption on the original targets.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

open PointProcess PointProcess.LocalConfiguration

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι B : Type*} [Fintype ι]
  [MetricSpace B] [ProperSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]

variable (base : (ι → ℝ) × B)

local instance : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance : PolishSpace (LocalConfiguration base) := vaguePolishSpace

/-- Actual integer target counts have a Haar local first moment without any
assumption on the target distribution or independence between labels. -/
theorem lintegral_physicalSceneRootedTargetConfiguration_sourceWindow_le
    {Ω : Type*} {n : ℕ} (Y : Ω → Fin (n + 1) → ((ι → ℝ) × B))
    (w : Ω) (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, countingMeasure (cavityRootedTargetConfiguration base Y (w, z)) (U ×ˢ univ)
      ∂cavityRootMeasure volume D ((n : ℝ) + 1)) ≤ volume U := by
  let loc : Fin (n + 1) → (ι → ℝ) := fun j ↦ (Y w j).1
  have heq (z : ι → ℝ) :
      countingMeasure (cavityRootedTargetConfiguration base Y (w, z)) (U ×ˢ univ) =
        cavityRootWindowReadout Measure.count loc (fun _ ↦ 1) U z := by
    simp only [cavityRootedTargetConfiguration, countingMeasure_ofTuple,
      Measure.finsetSum_apply, Measure.dirac_apply' _ (hU.prod MeasurableSet.univ),
      cavityRootWindowReadout, lintegral_fintype, Measure.count_singleton,
      cavitySpatialTranslate, loc]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hmem : (Y w j).1 - z ∈ U <;> simp [hmem]
  simp_rw [heq]
  rw [cavityRootMeasure, lintegral_smul_measure]
  calc
    _ ≤ (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ *
        ∫⁻ z, cavityRootWindowReadout Measure.count loc (fun _ ↦ 1) U z ∂volume :=
      mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _
    _ = (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ * (volume U * (n + 1 : ℝ≥0∞)) := by
      rw [lintegral_cavityRootWindowReadout volume Measure.count loc
        (measurable_of_finite _) (fun _ ↦ 1) measurable_const U hU]
      simp
    _ = volume U := by
      have hn : ENNReal.ofReal ((n : ℝ) + 1) = (n + 1 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one]
        simp
      rw [hn, mul_left_comm, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]


/-- The same actual integer labels have tight rooted laws; no target marginal
law is needed because the original root is Haar normalized at the label count. -/
theorem isTightMeasureSet_physicalSceneRootedTargetConfiguration
    {I : Type*} {Ω : I → Type*} [∀ k, MeasurableSpace (Ω k)]
    (m : I → ℕ) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (Y : ∀ k, Ω k → Fin (m k + 1) → ((ι → ℝ) × B))
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (D : I → Set (ι → ℝ)) :
    IsTightMeasureSet (range (fun k ↦
      ((P k).prod (cavityRootMeasure volume (D k) ((m k : ℝ) + 1))).map
        (cavityRootedTargetConfiguration base (Y k)))) := by
  apply isTightMeasureSet_of_lintegral_countingMeasure_ball_le _
    (fun n ↦ volume (Metric.ball base.1 ((n + 1 : ℕ) : ℝ)))
    (fun _ ↦ measure_ball_lt_top.ne)
  rintro _ ⟨k, rfl⟩ n
  have hconfig := measurable_cavityRootedTargetConfiguration base (Y k) (hY k)
  have hm : Measurable (fun config : LocalConfiguration base ↦
      countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ))) :=
    (Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp measurable_countingMeasure
  rw [lintegral_map hm hconfig]
  let ρ := cavityRootMeasure volume (D k) ((m k : ℝ) + 1)
  have : SFinite ρ := by dsimp only [ρ, cavityRootMeasure]; infer_instance
  have hprod := lintegral_prod (μ := P k) (ν := ρ)
    ((fun config ↦ countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ))) ∘
      cavityRootedTargetConfiguration base (Y k)) (hm.comp hconfig).aemeasurable
  dsimp only [Function.comp_def] at hprod
  rw [hprod]
  calc
    _ ≤ ∫⁻ w, ∫⁻ z, countingMeasure (cavityRootedTargetConfiguration base (Y k) (w, z))
        (Metric.ball base.1 ((n + 1 : ℕ) : ℝ) ×ˢ univ) ∂ρ ∂P k := by
      apply lintegral_mono
      intro w
      apply lintegral_mono
      intro z
      apply measure_mono
      intro y hy
      have hy' : y ∈ Metric.ball base.1 ((n + 1 : ℕ) : ℝ) ×ˢ
          Metric.ball base.2 ((n + 1 : ℕ) : ℝ) := by
        simpa only [ball_prod_same] using hy
      exact ⟨hy'.1, mem_univ _⟩
    _ ≤ ∫⁻ _ : Ω k, volume (Metric.ball base.1 ((n + 1 : ℕ) : ℝ)) ∂P k := by
      apply lintegral_mono
      intro w
      exact lintegral_physicalSceneRootedTargetConfiguration_sourceWindow_le
        base (Y k) w (D k) _ Metric.isOpen_ball.measurableSet
    _ = _ := by simp

end OTSelector.Reconstruction
