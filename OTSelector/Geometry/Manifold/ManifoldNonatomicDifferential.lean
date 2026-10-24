import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import OTSelector.Analysis.Calculus.DensityOneDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ManifoldNonatomicDifferential.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ManifoldNonatomicDifferential`; the selected original proof blocks follow. -/
section

/-!
Conditions: A chart-absolutely-continuous measure on a second-countable manifold and an almost-everywhere nonzero actual manifold differential.

Objects: Null scalar level sets and atomless pushforward.

Proof detail: Choose a countable chart cover, transfer to Haar-absolutely-continuous coordinate measures and apply the density-one null-fiber argument chartwise.

Sources: D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22); D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); John M. Lee, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70 (https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10).
Relation: Manifold extension of the locally proved differential atomlessness criterion.
-/

/-!
# Atomless pushforwards from almost-everywhere nonzero manifold differentials

At almost every point of a fixed coordinate fiber, Haar density is one. Chartwise
absolute continuity transfers this fact to the original measure, where the actual
differential is assumed to exist and be nonzero. Constancy on the density-one fiber
forces that same differential to vanish. A countable chart subcover makes every
original fiber null, hence the scalar pushforward has no atoms.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] in
private theorem coordinate_fderiv_ne_zero_of_mfderiv_ne_zero
    (old : M) {u : M → ℝ} {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hne : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x ≠ 0) {g : E → ℝ}
    (hg : g =ᶠ[𝓝 (extChartAt 𝓘(ℝ, E) old x)]
      u ∘ (extChartAt 𝓘(ℝ, E) old).symm) :
    DifferentiableAt ℝ g (extChartAt 𝓘(ℝ, E) old x) ∧
      fderiv ℝ g (extChartAt 𝓘(ℝ, E) old x) ≠ 0 := by
  let χ := extChartAt 𝓘(ℝ, E) old
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := 1) old).contMDiffAt
    ((isOpen_extChartAt_target old).mem_nhds (χ.map_source hx))).mdifferentiableAt
      one_ne_zero
  have hc := (contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1)
    (by simpa only [extChartAt_source] using hx)).mdifferentiableAt one_ne_zero
  have hd' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (χ.symm (χ x)) := by
    rwa [χ.left_inv hx]
  have hg₀ : DifferentiableAt ℝ (u ∘ χ.symm) (χ x) :=
    mdifferentiableAt_iff_differentiableAt.mp (hd'.comp (χ x) hi)
  refine ⟨hg₀.congr_of_eventuallyEq hg, ?_⟩
  intro hz
  have hzero : fderiv ℝ (u ∘ χ.symm) (χ x) = 0 := hg.fderiv_eq.symm.trans hz
  have hid : (u ∘ χ.symm) ∘ χ =ᶠ[𝓝 x] u := by
    filter_upwards [(isOpen_extChartAt_source old).mem_nhds hx] with q hq
    exact congrArg u (χ.left_inv hq)
  have hchain := mfderiv_comp x hg₀.mdifferentiableAt hc
  rw [mfderiv_eq_fderiv, hzero, ContinuousLinearMap.zero_comp] at hchain
  exact hne (hid.mfderiv_eq.symm.trans hchain)

private theorem measure_chart_fiber_eq_zero_of_ae_mfderiv_ne_zero
    (m : Measure E) [IsAddHaarMeasure m] (μ : Measure M) (old : M)
    (hchart : (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : Continuous u)
    (hd : ∀ᵐ x ∂μ, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hne : ∀ᵐ x ∂μ, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x ≠ 0) (c : ℝ) :
    μ ((extChartAt 𝓘(ℝ, E) old).source ∩ u ⁻¹' {c}) = 0 := by
  classical
  let χ := extChartAt 𝓘(ℝ, E) old
  let g : E → ℝ := χ.target.piecewise (u ∘ χ.symm) 0
  have hgt : ContinuousOn (u ∘ χ.symm) χ.target :=
    hu.comp_continuousOn (continuousOn_extChartAt_symm old)
  have hgm : Measurable g := hgt.measurable_piecewise continuous_zero.continuousOn
    (isOpen_extChartAt_target old).measurableSet
  let T : Set E := χ.target ∩ g ⁻¹' {c}
  have hT : MeasurableSet T := (isOpen_extChartAt_target old).measurableSet.inter
    (hgm (measurableSet_singleton c))
  have hden := (ae_restrict_iff' hT).mp (Besicovitch.ae_tendsto_measure_inter_div m T)
  have hχ : AEMeasurable χ (μ.restrict χ.source) :=
    (continuousOn_extChartAt old).aemeasurable (isOpen_extChartAt_source old).measurableSet
  have hdenμ := ae_of_ae_map hχ (hchart.ae_le hden)
  have hS : MeasurableSet (χ.source ∩ u ⁻¹' {c}) :=
    (isOpen_extChartAt_source old).measurableSet.inter
      (hu.measurable (measurableSet_singleton c))
  have hfalse : ∀ᵐ x ∂μ.restrict (χ.source ∩ u ⁻¹' {c}), False := by
    filter_upwards [ae_restrict_mem hS,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hdenμ,
      hd.filter_mono ae_restrict_le, hne.filter_mono ae_restrict_le] with x hx hdx hdu hnu
    have hgerm : g =ᶠ[𝓝 (χ x)] u ∘ χ.symm := by
      filter_upwards [(isOpen_extChartAt_target old).mem_nhds (χ.map_source hx.1)] with q hq
      exact piecewise_eq_of_mem χ.target (u ∘ χ.symm) 0 hq
    have hxT : χ x ∈ T := by
      refine ⟨χ.map_source hx.1, ?_⟩
      change g (χ x) = c
      rw [hgerm.eq_of_nhds]
      exact (congrArg u (χ.left_inv hx.1)).trans hx.2
    obtain ⟨hgd, hgn⟩ := coordinate_fderiv_ne_zero_of_mfderiv_ne_zero old hx.1 hdu hnu hgerm
    exact hgn (fderiv_eq_zero_of_eqOn_const_of_density_one m (hdx hxT) hxT hgd
      (fun q hq ↦ hq.2))
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ]
    using hfalse

variable [LindelofSpace M]

/-- Each scalar fiber is null when the actual manifold differential exists and is
nonzero almost everywhere for the original measure. Only the coordinate measures,
not the differentiability exceptional sets, are compared with Haar measure. -/
theorem measure_fiber_eq_zero_of_ae_mfderiv_ne_zero
    (m : Measure E) [IsAddHaarMeasure m] (μ : Measure M)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : Continuous u)
    (hd : ∀ᵐ x ∂μ, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hne : ∀ᵐ x ∂μ, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x ≠ 0) (c : ℝ) :
    μ (u ⁻¹' {c}) = 0 := by
  let U : M → Set M := fun x ↦ (extChartAt 𝓘(ℝ, E) x).source
  have hU (x : M) : IsOpen (U x) := isOpen_extChartAt_source x
  have hcover : univ ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨S, hS, hScov⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have hnull : μ (⋃ old ∈ S, U old ∩ u ⁻¹' {c}) = 0 := by
    apply (measure_biUnion_null_iff hS).mpr
    intro old _
    exact measure_chart_fiber_eq_zero_of_ae_mfderiv_ne_zero m μ old (hchart old) hu hd hne c
  apply measure_mono_null _ hnull
  intro x hx
  obtain ⟨old, hoS, hxo⟩ := mem_iUnion₂.mp (hScov (mem_univ x))
  exact mem_iUnion₂.mpr ⟨old, hoS, hxo, hx⟩

/-- A continuous scalar map with nonzero actual manifold differential almost
everywhere for a chartwise absolutely continuous law has an atomless pushforward. -/
theorem nullSingletonClass_map_of_ae_mfderiv_ne_zero
    (m : Measure E) [IsAddHaarMeasure m] (μ : Measure M)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : Continuous u)
    (hd : ∀ᵐ x ∂μ, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (hne : ∀ᵐ x ∂μ, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x ≠ 0) :
    NullSingletonClass (μ.map u) := by
  refine ⟨fun c ↦ ?_⟩
  rw [Measure.map_apply hu.measurable (measurableSet_singleton c)]
  exact measure_fiber_eq_zero_of_ae_mfderiv_ne_zero m μ hchart hu hd hne c

end OTSelector.Geometry

end
end
