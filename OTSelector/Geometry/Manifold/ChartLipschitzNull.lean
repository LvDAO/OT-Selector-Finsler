import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import OTSelector.MeasureTheory.HaarLipschitzDistortion
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ChartLipschitzNull.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ChartLipschitzNull`; the selected original proof blocks follow. -/
section

/-!
Conditions: An output law is chart absolutely continuous and the readout is locally Lipschitz in the stated finite-dimensional charts.

Objects: Transport of source-null sets to output-null images.

Proof detail: Use a countable chart cover and the Lipschitz null-image theorem in each coordinate neighborhood, then apply absolute continuity.

Sources: D. H. Fremlin, Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41 (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38); D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); John M. Lee, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70 (https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10).
Relation: Chartwise null-image corollary; image or inverse measurability is not silently added.
-/

/-!
# Null images of locally Lipschitz manifold readouts

A model-Haar null set has null image for every original chartwise absolutely
continuous manifold measure when the actual readout is locally Lipschitz in legal
output charts. Countable local covering needs no measurable image or inverse map.
-/

open Set Filter Metric Manifold MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]

omit [FiniteDimensional ℝ E] in
/-- Original chartwise absolute continuity transfers null coordinate images back
without requiring measurability of the original set or its image. -/
theorem measure_eq_zero_of_null_chart_image (m : Measure E) (ν : Measure M) (old : M)
    (hac : (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {S : Set M} (hS : S ⊆ (extChartAt 𝓘(ℝ, E) old).source)
    (hzero : m ((extChartAt 𝓘(ℝ, E) old) '' S) = 0) : ν S = 0 := by
  have hχ : AEMeasurable (extChartAt 𝓘(ℝ, E) old)
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source) :=
    (continuousOn_extChartAt old).aemeasurable (isOpen_extChartAt_source old).measurableSet
  have hr : ν.restrict (extChartAt 𝓘(ℝ, E) old).source S = 0 :=
    nonpos_iff_eq_zero.mp ((le_map_apply_image hχ _).trans_eq (hac hzero))
  simpa only [inter_eq_left.mpr hS] using measure_inter_eq_zero_of_restrict hr

/-- A legal Lipschitz coordinate readout sends a model-Haar null set to an original
manifold null set. No injectivity or lower Jacobian bound is used. -/
theorem measure_image_eq_zero_of_chart_lipschitz (m : Measure E) [IsAddHaarMeasure m]
    (ν : Measure M) (old : M)
    (hac : (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {R : E → M} {S : Set E} {C : ℝ≥0}
    (hlegal : MapsTo R S (extChartAt 𝓘(ℝ, E) old).source)
    (hR : LipschitzOnWith C (fun x ↦ extChartAt 𝓘(ℝ, E) old (R x)) S)
    (hzero : m S = 0) : ν (R '' S) = 0 := by
  apply measure_eq_zero_of_null_chart_image m ν old hac
    (by rintro _ ⟨x, hx, rfl⟩; exact hlegal hx)
  rw [image_image]
  exact nonpos_iff_eq_zero.mp
    ((haar_image_le_of_lipschitzOnWith m hR Subset.rfl).trans_eq (by rw [hzero, mul_zero]))

/-- Local Lipschitz readouts in possibly varying output charts preserve Haar-nullity
for every original chartwise absolutely continuous measure. Arbitrary sets are allowed. -/
theorem measure_image_eq_zero_of_locally_chart_lipschitz
    (m : Measure E) [IsAddHaarMeasure m] (ν : Measure M)
    (hac : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {R : E → M} {S : Set E} (hzero : m S = 0)
    (hlocal : ∀ x ∈ S, ∃ (r : ℝ) (C : ℝ≥0) (old : M), 0 < r ∧
      MapsTo R (closedBall x r) (extChartAt 𝓘(ℝ, E) old).source ∧
      LipschitzOnWith C (fun y ↦ extChartAt 𝓘(ℝ, E) old (R y)) (closedBall x r)) :
    ν (R '' S) = 0 := by
  classical
  choose r C old hr hlegal hLip using fun x : S ↦ hlocal x.val x.property
  let U : S → Set E := fun x ↦ ball x.val (r x)
  have hcover : S ⊆ ⋃ x : S, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨D, hD, hDc⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    U (fun _ ↦ isOpen_ball) hcover
  have hn : ν (⋃ x ∈ D, R '' (S ∩ U x)) = 0 := by
    apply (measure_biUnion_null_iff hD).mpr
    intro x hx
    apply measure_image_eq_zero_of_chart_lipschitz m ν (old x) (hac (old x))
      ((hlegal x).mono (fun y hy ↦ ball_subset_closedBall hy.2) Subset.rfl)
      ((hLip x).mono (fun y hy ↦ ball_subset_closedBall hy.2))
    exact measure_mono_null inter_subset_left hzero
  apply measure_mono_null _ hn
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hDc hx)
  exact mem_iUnion₂.mpr ⟨j, hj, mem_image_of_mem R ⟨hx, hxj⟩⟩

end OTSelector.Geometry

end
end
