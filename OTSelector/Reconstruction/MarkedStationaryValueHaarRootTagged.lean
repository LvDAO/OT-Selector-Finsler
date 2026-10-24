import OTSelector.Reconstruction.MarkedStationaryValueHaarRootStationarity
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Macroscopic tags fixed by limiting physical reroots

The finite macroscopic root changes by a deterministic displacement tending to
zero. The original joint scene law is retained: a varying continuous action is
passed through weak convergence using its deterministic-parameter product law.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

section ParameterAction
variable {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
  [MeasurableSpace T] [MeasurableSpace X] [BorelSpace T] [BorelSpace X]
  [PseudoMetrizableSpace T] [PseudoMetrizableSpace X]
  [SecondCountableTopology T] [SecondCountableTopology X]

/-- A deterministic varying action parameter can be kept jointly with the
original scene law while passing to a weak limit. -/
theorem tendsto_map_of_parameter_action
    {δ : ℕ → T} {δ₀ : T} (hδ : Tendsto δ atTop (𝓝 δ₀))
    (μ : ℕ → ProbabilityMeasure X) {ν : ProbabilityMeasure X}
    (hμ : Tendsto μ atTop (𝓝 ν))
    {action : T × X → X} (haction : Continuous action) :
    Tendsto (fun n ↦ (μ n).map (f := fun x ↦ action (δ n, x))
      (haction.measurable.comp measurable_prodMk_left).aemeasurable)
      atTop (𝓝 (ν.map (f := fun x ↦ action (δ₀, x)) (haction.measurable.comp
        (measurable_const.prodMk measurable_id)).aemeasurable)) := by
  have hproduct : Tendsto (fun n ↦ (diracProba (δ n)).prod (μ n)) atTop
      (𝓝 ((diracProba δ₀).prod ν)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (diracProba δ₀, ν)).comp
      (((continuous_diracProba.tendsto δ₀).comp hδ).prodMk_nhds hμ)
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hproduct haction
  have heq (d : T) (p : ProbabilityMeasure X) :
      ((diracProba d).prod p).map haction.measurable.aemeasurable =
        p.map (f := fun x ↦ action (d, x))
          (haction.measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable := by
    apply Subtype.ext
    change ((Measure.dirac d).prod (p : Measure X)).map action =
      (p : Measure X).map (fun x ↦ action (d, x))
    rw [Measure.dirac_prod, Measure.map_map haction.measurable measurable_prodMk_left]
    rfl
  simpa only [heq] using hmap
end ParameterAction

/-- The actual independent Haar-root law yields joint stationarity when its
finite action changes the macroscopic tag by a deterministic vanishing amount.
No finite-sample frozen-coefficient premise is imposed. -/
theorem measurePreserving_of_haarCubeAverageLaw_tendsto_parameterAction
    {ι T X : Type*} [Fintype ι]
    [TopologicalSpace T] [TopologicalSpace X]
    [MeasurableSpace T] [MeasurableSpace X] [BorelSpace T] [BorelSpace X]
    [PseudoMetrizableSpace T] [PseudoMetrizableSpace X]
    [SecondCountableTopology T] [SecondCountableTopology X]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (scene : ∀ n, Ω n × (ι → ℝ) → X) (hscene : ∀ n, Measurable (scene n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hlarge : Tendsto R atTop atTop)
    (μ : ℕ → ProbabilityMeasure X) {ν : ProbabilityMeasure X}
    (hlaw : ∀ n, (μ n : Measure X) = haarCubeAverageLaw (P n) (scene n) (R n))
    (hlim : Tendsto μ atTop (𝓝 ν))
    {δ : ℕ → T} {δ₀ : T} (hδ : Tendsto δ atTop (𝓝 δ₀))
    {action : T × X → X} (haction : Continuous action) (v : ι → ℝ)
    (hcocycle : ∀ n w z, action (δ n, scene n (w, z)) = scene n (w, z + v)) :
    MeasurePreserving (fun x ↦ action (δ₀, x)) (ν : Measure X) (ν : Measure X) := by
  have hmap := tendsto_map_of_parameter_action hδ μ hlim haction
  have hsame : Tendsto (fun n ↦ (μ n).map (f := fun x ↦ action (δ n, x))
      (haction.measurable.comp measurable_prodMk_left).aemeasurable) atTop (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    have hold := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f
    have herr : Tendsto (fun n ↦
        (∫ x, f (action (δ n, x)) ∂(μ n : Measure X)) -
          ∫ x, f x ∂(μ n : Measure X)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' ?_
        ((tendsto_haarCube_boundaryError (Fintype.card ι) ‖f‖ ‖v‖).comp hlarge)
      filter_upwards [hlarge.eventually (eventually_ge_atTop ‖v‖)] with n hn
      rw [hlaw n]
      exact norm_integral_haarCubeAverageLaw_reroot_sub_le (P n) (hscene n)
        (haction.measurable.comp measurable_prodMk_left) v (hcocycle n)
        (hR n) (norm_nonneg _) hn
        (fun i ↦ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        f.continuous.measurable (norm_nonneg _) f.norm_coe_le_norm
    have hsum := herr.add hold
    simp only [zero_add, sub_add_cancel] at hsum
    have heq : (fun n ↦ ∫ x, f x ∂Measure.map (fun x ↦ action (δ n, x)) (μ n : Measure X)) =
        (fun n ↦ ∫ x, f (action (δ n, x)) ∂(μ n : Measure X)) := by
      funext n
      exact integral_map (haction.measurable.comp measurable_prodMk_left).aemeasurable
        f.continuous.measurable.aestronglyMeasurable
    change Tendsto (fun n ↦ ∫ x, f x ∂Measure.map (fun x ↦ action (δ n, x)) (μ n : Measure X))
      atTop (𝓝 (∫ x, f x ∂(ν : Measure X)))
    rw [heq]
    exact hsum
  have heq := tendsto_nhds_unique hmap hsame
  refine ⟨haction.measurable.comp (measurable_const.prodMk measurable_id), ?_⟩
  exact congrArg (fun p : ProbabilityMeasure X ↦ (p : Measure X)) heq

end OTSelector.Reconstruction

open TopologicalSpace
namespace OTSelector.Reconstruction

/-- The original macroscopic Haar root is z/scale. A microscopic reroot v
changes it by v/scale, which vanishes. Thus the limiting joint law retains and
fixes that original root while rerooting the actual scene. -/
theorem measurePreserving_macroRoot_of_haarCubeAverageLaw_tendsto
    {ι X : Type*} [Fintype ι] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetrizableSpace X] [SecondCountableTopology X]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (scene : ∀ n, Ω n × (ι → ℝ) → X) (hscene : ∀ n, Measurable (scene n))
    (R scale : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hlarge : Tendsto R atTop atTop)
    (hscale : Tendsto scale atTop atTop)
    (μ : ℕ → ProbabilityMeasure ((ι → ℝ) × X)) {ν : ProbabilityMeasure ((ι → ℝ) × X)}
    (hlaw : ∀ n, (μ n : Measure ((ι → ℝ) × X)) = haarCubeAverageLaw (P n)
      (fun p ↦ ((fun i ↦ p.2 i / scale n), scene n p)) (R n))
    (hlim : Tendsto μ atTop (𝓝 ν))
    {shift : X → X} (hshift : Continuous shift) (v : ι → ℝ)
    (hcocycle : ∀ n w z, shift (scene n (w, z)) = scene n (w, z + v)) :
    MeasurePreserving (Prod.map id shift) (ν : Measure ((ι → ℝ) × X)) (ν : Measure _) := by
  let δ : ℕ → (ι → ℝ) := fun n i ↦ v i / scale n
  have hδ : Tendsto δ atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_const_nhds.div_atTop hscale
  let action : (ι → ℝ) × ((ι → ℝ) × X) → ((ι → ℝ) × X) :=
    fun p ↦ (p.2.1 + p.1, shift p.2.2)
  have ha : Continuous action :=
    (continuous_snd.fst.add continuous_fst).prodMk (hshift.comp continuous_snd.snd)
  have hs (n : ℕ) : Measurable
      (fun p : Ω n × (ι → ℝ) ↦ ((fun i ↦ p.2 i / scale n), scene n p)) := by
    exact (measurable_pi_lambda _ (fun i ↦
      (measurable_pi_apply i |>.comp measurable_snd).div_const (scale n))).prodMk (hscene n)
  have hc (n : ℕ) (w : Ω n) (z : ι → ℝ) :
      action (δ n, ((fun i ↦ z i / scale n), scene n (w, z))) =
        ((fun i ↦ (z + v) i / scale n), scene n (w, z + v)) := by
    apply Prod.ext
    · funext i
      exact (add_div (z i) (v i) (scale n)).symm
    · exact hcocycle n w z
  have h := measurePreserving_of_haarCubeAverageLaw_tendsto_parameterAction P
    (fun n p ↦ ((fun i ↦ p.2 i / scale n), scene n p)) hs
    R hR hlarge μ hlaw hlim hδ ha v hc
  change MeasurePreserving (fun p : (ι → ℝ) × X ↦ (p.1 + 0, shift p.2)) _ _ at h
  change MeasurePreserving (fun p : (ι → ℝ) × X ↦ (p.1, shift p.2)) _ _
  simpa only [add_zero] using h

end OTSelector.Reconstruction
