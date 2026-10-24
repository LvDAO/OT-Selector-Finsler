import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11ScalarAbsoluteContinuity
import OTSelector.Geometry.Finsler.CalibratedC11ReachCover
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ChartScalarAbsoluteContinuity
import OTSelector.MeasureTheory.LocalJointAbsoluteContinuity
import OTSelector.Probability.ConditionalScalarAbsoluteContinuity
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.InteriorScalarAbsoluteContinuity

* **Conditions:** The actual countable contact-core cover and ordered original labels, with chartwise absolutely continuous original population.
* **Objects:** Joint label–clock AC over the entire calibrated interior and actual scalar conditional AC at almost every original label.
* **Proof detail:** Assemble the core AC statements by countable union, use true label invariance and disintegrate product-null sections.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=20): 452E, p. 20: consistency and strong consistency; 452G(a)–(c), p. 21: probability kernels and concentration on fibers.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerInteriorScalarAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerInteriorScalarAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# Actual scalar conditional volume on the entire calibrated interior

The constructed countable contact cores and actual short geodesic translations give
joint label-potential absolute continuity on the entire two-sided calibrated interior.
Coordinate measures are the original chart laws. Ordered geometric labels supply
the required invariance, and disintegration yields actual scalar conditional densities.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Reconstruction
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M}

/-- Every original chartwise absolutely continuous measure has an absolutely
continuous label-potential law on the entire calibrated interior. All contact cores,
short translations and image-volume estimates are constructed from the geometry. -/
theorem map_label_potential_absolutelyContinuous_on_calibratedInterior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M)
    (hchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instInteriorScalarLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (hinv : let _instInteriorScalarInvariant : MetricSpace M := F.metricSpace
      ∀ x ∈ calibratedInterior u, ∀ y ∈ calibratedInterior u,
        |u y - u x| = dist x y → a y = a x) :
    let _instInteriorScalarStatement : MetricSpace M := F.metricSpace
    (ν.restrict (calibratedInterior u)).map (fun x ↦ (a x, u x)) ≪
      ((ν.restrict (calibratedInterior u)).map a).prod volume := by
  let _instInteriorScalarMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, G, L, δ, B, hdata, hcover, hreach⟩ :=
    hF.exists_countable_trimmed_calibrated_C11_cover hcomplete hu
  let _instInteriorScalarCountable : Countable ι := hcount
  have hlocal (i : ι) :
      (ν.restrict ((extChartAt 𝓘(ℝ, E) (old i)).symm '' K i)).map
        (fun x ↦ (a x, u x)) ≪
      ((ν.restrict ((extChartAt 𝓘(ℝ, E) (old i)).symm '' K i)).map a).prod volume := by
    obtain ⟨hK, ht, hG, _, hL, _, hmatch, _⟩ := hdata i
    apply map_label_clock_absolutelyContinuous_of_chart_core (old i) ν ha
      hu.continuous.measurable hK ht
    apply hF.map_label_potential_absolutelyContinuous_on_C11_core hcomplete (old i) m
      ((ν.restrict (extChartAt 𝓘(ℝ, E) (old i)).source).map
        (extChartAt 𝓘(ℝ, E) (old i))) (hchart (old i)) hK ht hu hG hL hmatch
      (hreach i).1 ?_ ha hinv
    dsimp only
    intro x hx
    obtain ⟨b, _, c, _, hb, hfb, hc, hfc⟩ := (hreach i).2.2 x hx
    exact ⟨b, c, hb, hfb, hc, hfc⟩
  apply map_label_clock_absolutelyContinuous_of_countable_cover ν ha
    hu.continuous.measurable (K := fun i ↦ (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i)
    ?_ (by rw [hcover]) hlocal
  intro i x hx
  rw [← hcover]
  exact mem_iUnion.mpr ⟨i, hx⟩

/-- The already constructed ordered geometric labels automatically supply calibrated
invariance. No additional label-invariance or flow premise is required by this consumer. -/
theorem map_label_potential_absolutelyContinuous_of_ordered_labels
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M)
    (hchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instOrderedScalarLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instOrderedScalarOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    let _instOrderedScalarStatement : MetricSpace M := F.metricSpace
    (ν.restrict (calibratedInterior u)).map (fun x ↦ (a x, u x)) ≪
      ((ν.restrict (calibratedInterior u)).map a).prod volume := by
  let _instOrderedScalarMetric : MetricSpace M := F.metricSpace
  apply hF.map_label_potential_absolutelyContinuous_on_calibratedInterior
    hcomplete m ν hchart hu ha
  dsimp only
  intro x hx y hy hcal
  have hxr := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu hx
  have hyr := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu hy
  rcases le_total (u x) (u y) with hxy | hyx
  · have hs : u y - u x = dist x y := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hcal
    exact ((horder x hxr y hyr).mpr hs).1.symm
  · have hs : u x - u y = dist y x := by
      simpa only [abs_sub_comm (u y) (u x),
        abs_of_nonneg (sub_nonneg.mpr hyx), dist_comm x y] using hcal
    exact ((horder y hyr x hxr).mpr hs).1

/-- On the calibrated interior, both the direct scalar conditional law and the clock
pushforward of the original conditional position law are Lebesgue absolutely continuous. -/
theorem ae_scalarConditionals_absolutelyContinuous_on_calibratedInterior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [IsProbabilityMeasure ν]
    (hchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} (hu : let _instConditionalInteriorLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a : M → Z} (ha : Measurable a)
    (horder : let _instConditionalInteriorOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    let _instConditionalInteriorStatement : MetricSpace M := F.metricSpace
    let _instConditionalInteriorProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instConditionalInteriorBorel : StandardBorelSpace M := inferInstance
    let _instConditionalInteriorNonempty : Nonempty M := nonempty_of_isProbabilityMeasure ν
    ∀ᵐ z ∂(ν.restrict (calibratedInterior u)).map a,
      condDistrib u a (ν.restrict (calibratedInterior u)) z ≪ volume ∧
      (condDistrib id a (ν.restrict (calibratedInterior u)) z).map u ≪ volume := by
  let _instConditionalInteriorMetric : MetricSpace M := F.metricSpace
  let _instConditionalInteriorProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instConditionalInteriorBorel : StandardBorelSpace M := inferInstance
  let _instConditionalInteriorNonempty : Nonempty M := nonempty_of_isProbabilityMeasure ν
  have hjoint := hF.map_label_potential_absolutelyContinuous_of_ordered_labels
    hcomplete m ν hchart hu ha horder
  exact (ae_condDistrib_clock_absolutelyContinuous_of_joint _
    hu.continuous.measurable hjoint).and
    (ae_condDistrib_map_clock_absolutelyContinuous_of_joint _ hu.continuous.measurable hjoint)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
