import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindowLabels.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindowLabels`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindowLabels

* **Conditions:** The existing measurable label map and potential separate regular points and encode ordered calibration on the actual regular domain.
* **Objects:** Labels constant on the actual window curves and a Borel embedding of their screened initial seeds into the same label space.
* **Proof detail:** Apply ordered calibration along each curve, then use the common initial potential level plus label–clock injectivity and Lusin–Souslin.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (derived): The original labels are retained, without selecting a new quotient.
-/

/-!
# Original geometric labels on actual calibrated windows

The existing ordered geometric labels are constant along every actual calibrated
window. Their values on screened seeds give a measurable embedding into the same
label space, using the existing label-potential injectivity and fixed seed level.
-/

open Set Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- Every actual window point has the same existing geometric label as its seed. -/
theorem label_toManifold_eq_initial (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowLabelLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (horder : let _instWindowLabelOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {z : ℝ × P.seed.covector.ker} (hz : z ∈ P.domain) :
    a (P.toManifold z) = a (P.seed.curve z.2 0) := by
  let _instWindowLabelMetric : MetricSpace M := F.metricSpace
  have hleft : (P.left : ℝ) < 0 := by exact_mod_cast P.left_neg
  have hright : (0 : ℝ) < P.right := by exact_mod_cast P.right_pos
  have hzero : (0 : ℝ) ∈ Icc (P.left : ℝ) P.right := ⟨hleft.le, hright.le⟩
  have htime : z.1 ∈ Icc (P.left : ℝ) P.right := ⟨hz.2.1.1.le, hz.2.1.2.le⟩
  have hc := hF.calibrated_window_of_complete_unit_endpoints hu
    (P.seed.complete z.2 hz.2.2.1) (P.seed.unit z.2 hz.2.2.1)
    hz.2.2.2.1 hz.2.2.2.2
  have hreg (t : ℝ) (ht : t ∈ Ioo (P.left : ℝ) P.right) :
      P.seed.curve z.2 t ∈ F.potentialRegularDomain u :=
    hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu (hc.2.2 t ht)
  have hr0 := hreg 0 ⟨hleft, hright⟩
  have hrt := hreg z.1 hz.2.1
  have hd : dist (P.seed.curve z.2 0) (P.seed.curve z.2 z.1) = |z.1| := by
    simpa only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg] using
      hc.2.1.dist_eq ⟨0, hzero⟩ ⟨z.1, htime⟩
  change a (P.seed.curve z.2 z.1) = a (P.seed.curve z.2 0)
  rcases le_total 0 z.1 with ht | ht
  · apply ((horder _ hr0 _ hrt).mpr ?_).1.symm
    rw [hc.1 z.1 htime, hc.1 0 hzero, hd, abs_of_nonneg ht]
    ring
  · apply ((horder _ hrt _ hr0).mpr ?_).1
    rw [hc.1 z.1 htime, hc.1 0 hzero, dist_comm, hd, abs_of_nonpos ht]
    ring

/-- Screened actual seeds embed measurably into the existing geometric label space;
their common original potential value turns label-clock injectivity into label injectivity. -/
theorem measurableEmbedding_seedLabel [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedLabelLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    MeasurableEmbedding (fun w : P.labels ↦ a (P.seed.curve w 0)) := by
  let _instSeedLabelBorel : StandardBorelSpace P.labels := (P.measurableSet_labels hu).standardBorel
  have hcont : Continuous (fun w : P.labels ↦ P.seed.curve w 0) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((P.seed.continuous_at_time 0).mono (fun _ hw ↦ P.seed.labels_subset hw.1))
  apply (ha.comp hcont.measurable).measurableEmbedding
  intro w z heq
  apply Subtype.ext
  apply P.seed.initial_injective w.property.1 z.property.1
  have hreg (v : P.labels) : P.seed.curve v 0 ∈ F.potentialRegularDomain u :=
    hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
      (P.seed.mapsTo_initial_calibratedInterior hF hu v.property.1)
  have heq' : (⟨P.seed.curve w 0, hreg w⟩ : F.potentialRegularDomain u) =
      ⟨P.seed.curve z 0, hreg z⟩ := by
    apply hinj
    exact Prod.ext heq ((P.seed.potential_initial w.property.1).trans
      (P.seed.potential_initial z.property.1).symm)
  exact congrArg Subtype.val heq'

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

end
end
