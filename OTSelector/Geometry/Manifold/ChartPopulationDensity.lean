import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ChartPopulationDensity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ChartPopulationDensity`; the selected original proof blocks follow. -/
section

/-!
Conditions: A density measure, a measurable chart/inverse on the indicated sets, an almost-everywhere left inverse and the stated transported reference density.

Objects: Chart density and Radon–Nikodym formula, including the chart-domain indicator.

Proof detail: Use map-withDensity under the almost-everywhere inverse, restrict to the actual target set and identify the Radon–Nikodym derivative.

Sources: D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40 (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27).
Relation: Measure-transport corollary; no measurability of the inverse outside its declared domain is inserted.
-/

/-!
# Original population densities in genuine manifold charts

An original density with respect to a volume measure pushes through a genuine
chart by composing that density with the inverse chart. The volume's actual
coordinate density is retained, including the chart target restriction. No global
measurability of either total chart function is needed.
-/

open Set MeasureTheory Manifold
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

/-- Weighting commutes with an almost-everywhere invertible measurable pushforward.
Only the original measure's almost-everywhere inverse is required. -/
theorem map_withDensity_of_ae_leftInverse
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} {g : Y → X} {d : X → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g (μ.map f))
    (hd : Measurable d) (hinv : ∀ᵐ x ∂μ, g (f x) = x) :
    (μ.withDensity d).map f = (μ.map f).withDensity (fun y ↦ d (g y)) := by
  refine Measure.ext_of_lintegral _ (fun φ hφ ↦ ?_)
  have hφf : AEMeasurable (fun x ↦ φ (f x)) μ := hφ.comp_aemeasurable hf
  have hdg : AEMeasurable (fun y ↦ d (g y)) (μ.map f) :=
    hd.comp_aemeasurable hg
  have hprod : AEMeasurable (fun y ↦ d (g y) * φ y) (μ.map f) :=
    hdg.mul hφ.aemeasurable
  rw [lintegral_map' hφ.aemeasurable
      (hf.mono_ac (withDensity_absolutelyContinuous μ d)),
    lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable hφf,
    lintegral_withDensity_eq_lintegral_mul₀ hdg hφ.aemeasurable]
  change (∫⁻ x, d x * φ (f x) ∂μ) =
    ∫⁻ y, d (g y) * φ y ∂μ.map f
  rw [lintegral_map' hprod hf]
  apply lintegral_congr_ae
  filter_upwards [hinv] with x hx
  rw [hx]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]

/-- The original population has coordinate density equal to its physical density
composed with the actual inverse chart times the volume's coordinate density. -/
theorem map_extChartAt_withDensity_of_volume_density
    (old : M) (ω : Measure M) (m : Measure E)
    {ρ : M → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    {v : E → ℝ}
    (hv : AEMeasurable v (m.restrict (extChartAt 𝓘(ℝ, E) old).target))
    (hvolume : (ω.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) =
        (m.restrict (extChartAt 𝓘(ℝ, E) old).target).withDensity
          (fun y ↦ ENNReal.ofReal (v y))) :
    ((ω.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) =
      (m.restrict (extChartAt 𝓘(ℝ, E) old).target).withDensity
        (fun y ↦ ENNReal.ofReal (ρ ((extChartAt 𝓘(ℝ, E) old).symm y) * v y)) := by
  let χ := extChartAt 𝓘(ℝ, E) old
  have hS : MeasurableSet χ.source := (isOpen_extChartAt_source old).measurableSet
  have hT : MeasurableSet χ.target := (isOpen_extChartAt_target old).measurableSet
  have hf : AEMeasurable χ (ω.restrict χ.source) :=
    (continuousOn_extChartAt old).aemeasurable hS
  have hi : AEMeasurable χ.symm ((ω.restrict χ.source).map χ) := by
    rw [hvolume]
    exact ((continuousOn_extChartAt_symm old).aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hinv : ∀ᵐ x ∂ω.restrict χ.source, χ.symm (χ x) = x := by
    filter_upwards [ae_restrict_mem hS] with x hx
    exact χ.left_inv hx
  have hd : Measurable (fun x ↦ ENNReal.ofReal (ρ x)) := hρ.ennreal_ofReal
  rw [restrict_withDensity hS, map_withDensity_of_ae_leftInverse _ hf hi hd hinv,
    hvolume]
  have hρi : AEMeasurable (fun y ↦ ENNReal.ofReal (ρ (χ.symm y)))
      (m.restrict χ.target) :=
    hd.comp_aemeasurable ((continuousOn_extChartAt_symm old).aemeasurable hT)
  rw [← withDensity_mul₀ hv.ennreal_ofReal hρi]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    change ENNReal.ofReal (v y) * ENNReal.ofReal (ρ (χ.symm y)) =
      ENNReal.ofReal (ρ (χ.symm y) * v y)
    rw [ENNReal.ofReal_mul (hρ0 (χ.symm y)), mul_comm])

/-- The coordinate Radon--Nikodym density is the physical density times the actual
volume factor on the chart target, and zero off that target. -/
theorem rnDeriv_map_extChartAt_withDensity_of_volume_density
    (old : M) (ω : Measure M) (m : Measure E) [SigmaFinite m]
    {ρ : M → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    {v : E → ℝ}
    (hv : AEMeasurable v (m.restrict (extChartAt 𝓘(ℝ, E) old).target))
    (hvolume : (ω.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) =
        (m.restrict (extChartAt 𝓘(ℝ, E) old).target).withDensity
          (fun y ↦ ENNReal.ofReal (v y))) :
    let χ := extChartAt 𝓘(ℝ, E) old
    (((ω.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).restrict χ.source).map χ).rnDeriv m
      =ᵐ[m] χ.target.indicator
        (fun y ↦ ENNReal.ofReal (ρ (χ.symm y) * v y)) := by
  let χ := extChartAt 𝓘(ℝ, E) old
  have hT : MeasurableSet χ.target := (isOpen_extChartAt_target old).measurableSet
  have hi : AEMeasurable χ.symm (m.restrict χ.target) :=
    (continuousOn_extChartAt_symm old).aemeasurable hT
  have hd : AEMeasurable (fun y ↦ ENNReal.ofReal (ρ (χ.symm y) * v y))
      (m.restrict χ.target) := ((hρ.comp_aemeasurable hi).mul hv).ennreal_ofReal
  change _ =ᵐ[m] χ.target.indicator _
  rw [map_extChartAt_withDensity_of_volume_density old ω m hρ hρ0 hv hvolume,
    ← withDensity_indicator hT]
  exact Measure.rnDeriv_withDensity₀ m ((aemeasurable_indicator_iff hT).mpr hd)

end OTSelector.Geometry

end
end
