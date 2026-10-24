import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowLabels
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindowRestriction.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindowRestriction`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindowRestriction

* **Conditions:** An actual calibrated window, existing geometric labels and a measurable label-space piece.
* **Objects:** Borel seed-label slices and restricted windows with their exact time–label product domain and original manifold image.
* **Proof detail:** Restrict by the actual initial label; curve label constancy removes time dependence and ordinary image/preimage identities give the exact image.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.

Source relation (adapter): A measurable restriction adapter of the constructed original windows.
-/

/-!
# Calibrated windows restricted by original geometric labels

A measurable piece of the existing geometric label space restricts only the seed
factor of each actual calibrated window. The resulting Borel parameter domain
keeps its exact time-label product form and its original manifold image.
-/

open Set Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Retained seeds whose original geometric label belongs to the chosen piece. -/
def seedLabelSlice (P : CalibratedSeedWindow F u) (a : M → Z) (B : Set Z) :
    Set P.seed.covector.ker :=
  P.labels ∩ {w | a (P.seed.curve w 0) ∈ B}

/-- The actual window restricted by a piece of the original geometric label space. -/
def labelRestrictedDomain (P : CalibratedSeedWindow F u) (a : M → Z) (B : Set Z) :
    Set (ℝ × P.seed.covector.ker) :=
  P.domain ∩ {z | a (P.toManifold z) ∈ B}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Restriction in the original label space commutes with taking the actual image. -/
theorem image_labelRestrictedDomain (P : CalibratedSeedWindow F u) (a : M → Z)
    (B : Set Z) :
    P.toManifold '' P.labelRestrictedDomain a B = (P.toManifold '' P.domain) ∩ a ⁻¹' B :=
  image_inter_preimage P.toManifold P.domain (a ⁻¹' B)

variable [T2Space M] [PreconnectedSpace M]

omit [BorelSpace E] in
/-- Original window clocks make a whole-label restriction an exact product domain. -/
theorem labelRestrictedDomain_eq_prod (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instLabelRestrictionLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (horder : let _instLabelRestrictionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (B : Set Z) :
    P.labelRestrictedDomain a B =
      (Ioo (P.left : ℝ) P.right ∩ ball P.center.1 (P.seed.radius P.center)) ×ˢ
        (P.seedLabelSlice a B ∩ ball P.center.2 (P.seed.radius P.center)) := by
  ext z
  constructor
  · rintro ⟨hz, hB⟩
    have hz' := P.domain_eq_prod ▸ hz
    refine ⟨hz'.1, ⟨⟨hz'.2.1, ?_⟩, hz'.2.2⟩⟩
    change a (P.seed.curve z.2 0) ∈ B
    rw [← P.label_toManifold_eq_initial hF hcomplete hu horder hz]
    exact hB
  · rintro ⟨ht, ⟨hw, hr⟩⟩
    have hz : z ∈ P.domain := by
      rw [P.domain_eq_prod]
      exact ⟨ht, hw.1, hr⟩
    refine ⟨hz, ?_⟩
    change a (P.toManifold z) ∈ B
    rw [P.label_toManifold_eq_initial hF hcomplete hu horder hz]
    exact hw.2

/-- Fixed-time continuity on legal seeds makes the original label slice Borel. -/
theorem measurableSet_seedLabelSlice [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Z]
    (P : CalibratedSeedWindow F u)
    (hu : let _instSeedSliceLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a) {B : Set Z} (hB : MeasurableSet B) :
    MeasurableSet (P.seedLabelSlice a B) := by
  have hc : Continuous (fun w : P.labels ↦ P.seed.curve w 0) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((P.seed.continuous_at_time 0).mono (fun _ hw ↦ P.seed.labels_subset hw.1))
  have hm : MeasurableSet {w : P.labels | a (P.seed.curve w 0) ∈ B} :=
    hB.preimage (ha.comp hc.measurable)
  have heq : P.seedLabelSlice a B = ((↑) : P.labels → P.seed.covector.ker) ''
      {w : P.labels | a (P.seed.curve w 0) ∈ B} := by
    ext w
    simp only [seedLabelSlice, mem_inter_iff, mem_ofPred_eq, mem_image, Subtype.exists]
    aesop
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe (P.measurableSet_labels hu)).measurableSet_image.mpr hm

/-- Restricting an actual calibrated window by a Borel geometric-label piece is Borel. -/
theorem measurableSet_labelRestrictedDomain [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace Z] (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instRestrictedDomainLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (horder : let _instRestrictedDomainOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {B : Set Z} (hB : MeasurableSet B) :
    MeasurableSet (P.labelRestrictedDomain a B) := by
  rw [P.labelRestrictedDomain_eq_prod hF hcomplete hu horder]
  exact (isOpen_Ioo.measurableSet.inter isOpen_ball.measurableSet).prod
    ((P.measurableSet_seedLabelSlice hu ha hB).inter isOpen_ball.measurableSet)

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

end
end
