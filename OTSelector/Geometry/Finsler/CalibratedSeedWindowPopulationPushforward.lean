import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowPopulationDensity
import OTSelector.Geometry.Finsler.CalibratedSeedWindowPushforward
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedJacobianMeasurable
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindowPopulationPushforward.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindowPopulationPushforward`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindowPopulationPushforward

* **Conditions:** The fixed calibrated window/reference, explicit population and chart-volume densities and original geometric label/clock hypotheses.
* **Objects:** The exact physical mass-piece label–clock law with its normalized Jacobian and original density factors.
* **Proof detail:** Apply the embedded window pushforward formula to the explicit physical pullback density and its same original indicator.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (derived): A physical-density specialization of the original window law; it preserves the actual reference normalization.
-/

/-!+# Physical population densities on the original label-clock space

The actual population density and smooth volume factor give the joint density of
every Borel piece of an original calibrated window. The seed Haar reference,
Jacobian normalization and original potential clock are retained exactly.
-/

open Set MeasureTheory Manifold Metric
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original physical density gives the exact joint label-clock law on each
actual window piece, without any chart Radon--Nikodym derivative in the formula. -/
theorem map_labelClock_restrict_eq_withDensity_populationDensity
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPhysicalWindowLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instPhysicalWindowOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : Measure P.seed.covector.ker) [κ.IsAddHaarMeasure]
    (hprod : tubeParameterMeasure P.seed.normalization m =
      (volume : Measure ℝ).prod κ)
    (ωM : Measure M) {ρ : M → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    {v : E → ℝ} (hv : Measurable v)
    (hvolume : let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v y)))
    {C : Set M} (hC : MeasurableSet C) (hCP : C ⊆ P.toManifold '' P.domain) :
    let L := P.labels ∩ ball P.center.2 (P.seed.radius P.center)
    let β := (κ.comap ((↑) : L → P.seed.covector.ker)).map
      (fun w : L ↦ a (P.seed.curve w 0))
    let η := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))
    let q : P.domain → Z × ℝ := fun z ↦
      (a (P.toManifold z), u (P.toManifold z))
    let d : P.domain → ℝ≥0∞ := fun z ↦
      (ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
        ENNReal.ofReal (ρ (P.toManifold z) * v (P.readout z))) *
          (C.indicator (fun _ : M ↦ (1 : ℝ≥0∞))) (P.toManifold z)
    let G := Function.extend q d (fun _ : Z × ℝ ↦ 0)
    IsFiniteMeasure β ∧ Measurable G ∧
      (η.restrict C).map (fun x ↦ (a x, u x)) =
        (β.prod (volume : Measure ℝ)).withDensity G := by
  have hX := P.measurableEmbedding_toManifold hF hcomplete hu
  have hr : Measurable (fun z : P.domain ↦ P.readout z) :=
    (continuousOn_iff_continuous_domRestrict.mp
      (P.lipschitzOn_readout.continuousOn.mono inter_subset_left)).measurable
  have hw : Measurable (fun z : P.domain ↦
      ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
        ENNReal.ofReal (ρ (P.toManifold z) * v (P.readout z))) :=
    (((measurable_parameterizedJacobian P.readout P.seed.normalization).comp
      measurable_subtype_coe).ennreal_ofReal).mul
        (((hρ.comp hX.measurable).mul (hv.comp hr)).ennreal_ofReal)
  exact P.map_labelClock_restrict_eq_withDensity_of_comap hF hcomplete hu ha hinj horder
    m κ hprod (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) _ hw
    (P.comap_toManifold_eq_withDensity_populationDensity hF hcomplete hu m ωM
      hρ hρ0 hv.aemeasurable hvolume) hC hCP

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

end
end
