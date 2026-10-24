import OTSelector.Geometry.Finsler.Calibration.SeedLabelReference
import OTSelector.MeasureTheory.ConditionalWindowConsistency
import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw

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





/-- The window's label reference is exactly the full seed reference restricted
to labels retained by its endpoint screen and its actual chart ball. -/
theorem populationWindowLabelReference_eq_seed_restrict
    (P : F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedRefWindowMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (κ : Measure P.seed.covector.ker) :
    populationWindowLabelReference (fun _ ↦ P) a (fun _ ↦ κ) 0 =
      (populationSeedLabelReference P.seed a κ).restrict
        ((fun w ↦ a (P.seed.curve w 0)) ''
          (P.labels ∩ ball P.center.2 (P.seed.radius P.center))) :=
  labelReferenceOn_eq_restrict κ (a := fun w ↦ a (P.seed.curve w 0))
    (L := P.labels ∩ ball P.center.2 (P.seed.radius P.center)) P.seed.labels_measurable
    ((P.measurableSet_labels hu).inter isOpen_ball.measurableSet)
    (fun _ hw ↦ hw.1.1)
    (measurableEmbedding_populationSeedLabel P.seed hF hcomplete hu ha hinj)

/-- The fixed full-seed factor is finite almost everywhere and equals every
window factor at its retained labels. Zero physical population density is allowed. -/
theorem ae_populationWindow_rnDeriv_eq_seed
    (P : F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedRNMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (κ : Measure P.seed.covector.ker) [SigmaFinite κ]
    (lambda : Measure Z) [SigmaFinite lambda] :
    ∀ᵐ z ∂lambda, (populationSeedLabelReference P.seed a κ).rnDeriv lambda z <
        (∞ : ℝ≥0∞) ∧
      ∀ w ∈ P.labels ∩ ball P.center.2 (P.seed.radius P.center), a (P.seed.curve w 0) = z →
        (populationWindowLabelReference (fun _ ↦ P) a (fun _ ↦ κ) 0).rnDeriv lambda z =
          (populationSeedLabelReference P.seed a κ).rnDeriv lambda z := by
  have he := measurableEmbedding_populationSeedLabel P.seed hF hcomplete hu ha hinj
  have : SigmaFinite (populationSeedLabelReference P.seed a κ) :=
    sigmaFinite_labelReferenceOn κ P.seed.labels_measurable he
  have hRN := ae_rnDeriv_labelReferenceOn_eq κ lambda
    (a := fun w ↦ a (P.seed.curve w 0))
    (L := P.labels ∩ ball P.center.2 (P.seed.radius P.center)) P.seed.labels_measurable
    ((P.measurableSet_labels hu).inter isOpen_ball.measurableSet)
    (fun _ hw ↦ hw.1.1) he
  filter_upwards [(populationSeedLabelReference P.seed a κ).rnDeriv_lt_top lambda, hRN]
    with z hz hsame
  refine ⟨hz, ?_⟩
  intro w hw hwz
  exact hsame ⟨w, hw, hwz⟩

/-- Haar-almost-everywhere seed geometry transfers to every representative of
an original label wherever its fixed seed reference has nonzero density. -/
theorem ae_populationSeedLabel_property
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedPropertyMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (κ : Measure S.covector.ker) [SigmaFinite κ]
    (lambda : Measure Z) [SigmaFinite lambda] {Good : S.covector.ker → Prop}
    (hgood : ∀ᵐ w ∂κ.restrict S.labels, Good w) :
    ∀ᵐ z ∂lambda, (populationSeedLabelReference S a κ).rnDeriv lambda z ≠ 0 →
      ∀ w ∈ S.labels, a (S.curve w 0) = z → Good w := by
  have he := measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj
  have : SigmaFinite (populationSeedLabelReference S a κ) :=
    sigmaFinite_labelReferenceOn κ S.labels_measurable he
  have hgoodSub := (ae_restrict_iff_subtype S.labels_measurable).mp hgood
  have hgoodLabel : ∀ᵐ z ∂populationSeedLabelReference S a κ,
      ∀ w ∈ S.labels, a (S.curve w 0) = z → Good w := by
    apply he.ae_map_iff.mpr
    filter_upwards [hgoodSub] with x hx
    intro w hw hwx
    have heq : (⟨w, hw⟩ : S.labels) = x := he.injective hwx
    have hval : x.val = w := congrArg Subtype.val heq.symm
    exact hval ▸ hx
  exact Measure.ae_rnDeriv_ne_zero_imp_of_ae lambda hgoodLabel

end OTSelector.Reconstruction
