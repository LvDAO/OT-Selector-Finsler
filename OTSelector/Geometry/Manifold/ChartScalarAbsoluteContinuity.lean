import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Geometry.Manifold.ChartScalarAbsoluteContinuity

## Lemma skeleton

* **Conditions:** A measurable coordinate core contained in the legal target of a genuine manifold chart; the absolute-continuity conclusion has the explicit label/clock observables and coordinate-law domination premise.

* **Objects:** Exact restriction/pushforward identities and transfer of scalar absolute continuity back to the original manifold core.

* **Proof detail:** Write the restricted law on the chart target as the pushforward from its inverse image, map back using the chart inverse identities, then compose the observables and substitute the exact law identities into the domination premise.

## Mathematical sources

- [John M. Lee, Introduction to Smooth Manifolds, second edition (2013)](https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10): Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (adapter): Only legal chart restrictions are used; global measurable inverse/extension assumptions are not invented.
-/

/-!
# Transfer of scalar absolute continuity through genuine coordinate cores

Restricting the original coordinate law to a measurable set in the chart target is
exactly the pushforward of the original law on its inverse-chart image. Mapping back,
and then evaluating any measurable observable, preserves these exact laws. This
transfers label-clock absolute continuity from coordinates to the original manifold.
Only the restrictions of the chart maps to their legal domains are used measurably.
-/

open Set Filter MeasureTheory Manifold

noncomputable section
namespace OTSelector.Geometry

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z]

/-- Restricting the genuine coordinate law to a legal measurable core equals the
coordinate pushforward of the original law restricted to the inverse-chart image. -/
theorem restrict_map_extChartAt_eq_map_chart_core (old : M) (ν : Measure M)
    {K : Set E} (hK : MeasurableSet K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) :
    ((ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old)).restrict K =
    (ν.restrict ((extChartAt 𝓘(ℝ, E) old).symm '' K)).map
      (extChartAt 𝓘(ℝ, E) old) := by
  have hχ : AEMeasurable (extChartAt 𝓘(ℝ, E) old)
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source) :=
    (continuousOn_extChartAt old).aemeasurable (isOpen_extChartAt_source old).measurableSet
  rw [Measure.restrict_map_of_aemeasurable hχ hK,
    Measure.restrict_restrict' (isOpen_extChartAt_source old).measurableSet,
    inter_comm, ← (extChartAt 𝓘(ℝ, E) old).symm_image_eq_source_inter_preimage hKtarget]

/-- Mapping a restricted genuine coordinate law back gives exactly the restricted
original law. No global measurability of either total chart function is assumed. -/
theorem map_symm_extChartAt_restrict_eq_chart_core (old : M) (ν : Measure M)
    {K : Set E} (hK : MeasurableSet K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) :
    (((ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old)).restrict K).map (extChartAt 𝓘(ℝ, E) old).symm =
    ν.restrict ((extChartAt 𝓘(ℝ, E) old).symm '' K) := by
  let χ := extChartAt 𝓘(ℝ, E) old
  have hS : χ.symm '' K ⊆ χ.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact χ.map_target (hKtarget hz)
  have hχ : AEMeasurable χ (ν.restrict (χ.symm '' K)) :=
    AEMeasurable.mono_set hS
      ((continuousOn_extChartAt old).aemeasurable
        (isOpen_extChartAt_source old).measurableSet)
  have hi : AEMeasurable χ.symm
      (((ν.restrict χ.source).map χ).restrict K) :=
    ((continuousOn_extChartAt_symm old).mono hKtarget).aemeasurable hK
  rw [restrict_map_extChartAt_eq_map_chart_core old ν hK hKtarget] at hi ⊢
  rw [AEMeasurable.map_map_of_aemeasurable hi hχ]
  have heq : χ.symm ∘ χ =ᵐ[ν.restrict (χ.symm '' K)] id := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hS
      (ae_restrict_mem (isOpen_extChartAt_source old).measurableSet)] with x hx
    exact χ.left_inv hx
  rw [Measure.map_congr heq, Measure.map_id]

/-- Every measurable original observable has exactly the same restricted law when
evaluated through genuine coordinates and then the inverse chart. -/
theorem map_observable_chart_core_eq (old : M) (ν : Measure M)
    {f : M → Z} (hf : Measurable f) {K : Set E} (hK : MeasurableSet K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) :
    (((ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old)).restrict K).map
      (f ∘ (extChartAt 𝓘(ℝ, E) old).symm) =
    (ν.restrict ((extChartAt 𝓘(ℝ, E) old).symm '' K)).map f := by
  have hi : AEMeasurable (extChartAt 𝓘(ℝ, E) old).symm
      (((ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
        (extChartAt 𝓘(ℝ, E) old)).restrict K) :=
    ((continuousOn_extChartAt_symm old).mono hKtarget).aemeasurable hK
  rw [← AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hi,
    map_symm_extChartAt_restrict_eq_chart_core old ν hK hKtarget]

/-- Label-clock absolute continuity on a compact coordinate core transfers to the
same original population restricted to its actual inverse-chart image. -/
theorem map_label_clock_absolutelyContinuous_of_chart_core (old : M) (ν : Measure M)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hac :
      (((ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
        (extChartAt 𝓘(ℝ, E) old)).restrict K).map
          (fun z ↦ (a ((extChartAt 𝓘(ℝ, E) old).symm z),
            u ((extChartAt 𝓘(ℝ, E) old).symm z))) ≪
      ((((ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
        (extChartAt 𝓘(ℝ, E) old)).restrict K).map
          (fun z ↦ a ((extChartAt 𝓘(ℝ, E) old).symm z))).prod volume) :
    (ν.restrict ((extChartAt 𝓘(ℝ, E) old).symm '' K)).map (fun x ↦ (a x, u x)) ≪
      ((ν.restrict ((extChartAt 𝓘(ℝ, E) old).symm '' K)).map a).prod volume := by
  have hj := map_observable_chart_core_eq old ν (ha.prodMk hu) hK.measurableSet hKtarget
  have hl := map_observable_chart_core_eq old ν ha hK.measurableSet hKtarget
  change _ ≪ _ at hac
  rw [← hj, ← hl]
  exact hac

end OTSelector.Geometry
