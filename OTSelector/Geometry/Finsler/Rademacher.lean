import Mathlib.Analysis.Calculus.Rademacher
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.InverseChartLipschitz
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.Rademacher

* **Conditions:** A scalar potential Lipschitz in the original Finsler metric and a measure absolutely continuous in each chart; countability is explicit or derived from completeness.
* **Objects:** Almost-everywhere actual manifold differentiability of the potential and of original distance-to-a-point.
* **Proof detail:** Compose with local inverse-chart Lipschitz maps, apply Euclidean Rademacher and transfer null exceptions through a countable genuine chart cover.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerRademacher.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerRademacher`; the selected original proof blocks follow. -/
section

/-!
# Almost-everywhere differentiability for the original Finsler distance

Actual inverse charts are locally Lipschitz for the original length metric. Rademacher
therefore applies to the coordinate pullback of every original Lipschitz scalar map.
Chartwise absolute continuity transfers the actual derivative back to the original
measure, and a constructed countable open cover assembles the manifold statement.
Completeness gives properness and supplies the required countability automatically.
-/

open Set Filter Metric MeasureTheory Manifold
open scoped Topology NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  (F : ContinuousFinslerNorm E M) (m : Measure E) [m.IsAddHaarMeasure]
  (μ : Measure M)

/-- A scalar function Lipschitz for the original Finsler metric is manifold differentiable
almost everywhere for a measure whose original coordinate laws are Haar absolutely continuous. -/
theorem ae_mdifferentiableAt_scalar_of_lipschitz [SecondCountableTopology M]
    (hchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} {L : ℝ≥0}
    (hu : let _instScalarRademacherMetric : MetricSpace M := F.metricSpace
      LipschitzWith L u) : ∀ᵐ x ∂μ, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  let _instScalarRademacherProofMetric : MetricSpace M := F.metricSpace
  classical
  choose r C hr hball hLip using F.exists_lipschitzOnWith_extChartAt_symm
  let W : M → Set M := fun old ↦ (extChartAt 𝓘(ℝ, E) old).source ∩
    (extChartAt 𝓘(ℝ, E) old) ⁻¹' ball (extChartAt 𝓘(ℝ, E) old old) (r old)
  have hWopen (old : M) : IsOpen (W old) :=
    (continuousOn_extChartAt old).isOpen_inter_preimage (isOpen_extChartAt_source _) isOpen_ball
  have hWmem (old : M) : old ∈ W old :=
    ⟨mem_extChartAt_source old, mem_ball_self (hr old)⟩
  have hlocal (old : M) : ∀ᵐ x ∂μ.restrict (W old),
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
    have hae : ∀ᵐ y ∂m, y ∈ ball (extChartAt 𝓘(ℝ, E) old old) (r old) →
        DifferentiableAt ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) y := by
      filter_upwards [(hu.comp_lipschitzOnWith (hLip old)).ae_differentiableWithinAt_of_mem
        (μ := m)] with y hy hyball
      exact (hy hyball).differentiableAt (isOpen_ball.mem_nhds hyball)
    have hmeas : AEMeasurable (extChartAt 𝓘(ℝ, E) old)
        (μ.restrict (extChartAt 𝓘(ℝ, E) old).source) :=
      (continuousOn_extChartAt old).aemeasurable (isOpen_extChartAt_source _).measurableSet
    have hpre := ae_of_ae_map hmeas ((hchart old).ae_le hae)
    have hpreW := ae_restrict_of_ae_restrict_of_subset
      (show W old ⊆ (extChartAt 𝓘(ℝ, E) old).source from inter_subset_left) hpre
    filter_upwards [hpreW, ae_restrict_mem (hWopen old).measurableSet] with x hx hxW
    apply (mdifferentiableAt_iff_source_of_mem_source
      (show x ∈ (chartAt E old).source by simpa only [extChartAt_source] using hxW.1)).mpr
    simpa using (hx hxW.2).mdifferentiableAt.mdifferentiableWithinAt
      (s := Set.range (𝓘(ℝ, E) : E → E))
  obtain ⟨S, hS, hcover⟩ := countable_cover_nhds (fun x ↦ (hWopen x).mem_nhds (hWmem x))
  have hall := (ae_restrict_biUnion_iff W hS
    (fun x ↦ MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)).mpr (fun old _ ↦ hlocal old)
  simpa only [hcover, Measure.restrict_univ] using hall

/-- Completeness of the original metric supplies properness and a countable cover, so
no separate countable-atlas assumption is needed for the scalar Rademacher theorem. -/
theorem ae_mdifferentiableAt_scalar_of_lipschitz_of_complete
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {u : M → ℝ} {L : ℝ≥0}
    (hu : let _instCompleteScalarRademacherMetric : MetricSpace M := F.metricSpace
      LipschitzWith L u) : ∀ᵐ x ∂μ, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  let _instCompleteScalarRademacherProofMetric : MetricSpace M := F.metricSpace
  let _instCompleteScalarRademacherProper : ProperSpace M := F.properSpace_of_complete hcomplete
  exact F.ae_mdifferentiableAt_scalar_of_lipschitz m μ hchart hu

/-- Every original distance-to-target function is manifold differentiable almost
 everywhere under the original chartwise absolutely continuous measure. -/
theorem ae_mdifferentiableAt_distance_of_complete
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (y : M) :
    let _instDistanceRademacherMetric : MetricSpace M := F.metricSpace
    ∀ᵐ x ∂μ, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z ↦ dist z y) x := by
  let _instDistanceRademacherProofMetric : MetricSpace M := F.metricSpace
  exact F.ae_mdifferentiableAt_scalar_of_lipschitz_of_complete m μ hcomplete hchart
    (LipschitzWith.dist_left y)

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
