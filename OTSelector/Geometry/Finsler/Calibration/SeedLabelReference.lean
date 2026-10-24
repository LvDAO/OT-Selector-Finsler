import Mathlib.MeasureTheory.Measure.Hausdorff
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.MeasureTheory.ConditionalWindowConsistency
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerSeedLabelReference.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerSeedLabelReference`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.SeedLabelReference

* **Conditions:** An actual complete seed, a transverse measure and population labels; the embedding theorem also assumes calibration and injectivity of label plus potential on the regular domain.
* **Objects:** One unscreened transverse label reference and a measurable embedding of the entire actual seed into the existing label space.
* **Proof detail:** Restrict the transverse measure to actual seed labels and push it through the initial curve label; prove injectivity using the common seed level and regular label–clock separation.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.

Source relation (adapter): The selected reference/embedding is independent of a rational clock screen or chart ball. Its RN factors and later window restrictions are outside this extraction.
-/

/-!
# A fixed original label reference for an entire calibrated seed

The complete seed, independently of every rational screening interval and chart
ball, embeds in the original geometric labels. Every actual window reference is
its restriction, so its label Radon--Nikodym factor remains fixed along the seed.
-/

open Set MeasureTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original geometric label reference of the entire seed, with one fixed Haar measure. -/
def populationSeedLabelReference (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (κ : Measure S.covector.ker) : Measure Z :=
  labelReferenceOn κ (fun w ↦ a (S.curve w 0)) S.labels

/-- The unscreened original seed embeds into the original geometric label space. -/
theorem measurableEmbedding_populationSeedLabel (S : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedRefMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    MeasurableEmbedding (fun w : S.labels ↦ a (S.curve w 0)) := by
  let _instSeedRefBorel : StandardBorelSpace S.labels := S.labels_measurable.standardBorel
  have hcont : Continuous (fun w : S.labels ↦ S.curve w 0) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((S.continuous_at_time 0).mono S.labels_subset)
  apply (ha.comp hcont.measurable).measurableEmbedding
  intro w z heq
  apply Subtype.ext
  apply S.initial_injective w.property z.property
  have hreg (v : S.labels) : S.curve v 0 ∈ F.potentialRegularDomain u :=
    hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
      (S.mapsTo_initial_calibratedInterior hF hu v.property)
  have heq' : (⟨S.curve w 0, hreg w⟩ : F.potentialRegularDomain u) =
      ⟨S.curve z 0, hreg z⟩ := by
    apply hinj
    exact Prod.ext heq ((S.potential_initial w.property).trans
      (S.potential_initial z.property).symm)
  exact congrArg Subtype.val heq'







end OTSelector.Reconstruction

end
end
