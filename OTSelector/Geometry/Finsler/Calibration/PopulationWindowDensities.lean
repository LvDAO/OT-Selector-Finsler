import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowPopulationPushforward
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
import OTSelector.MeasureTheory.GeometricWindowNormalization
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationWindowDensities.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationWindowDensities`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.PopulationWindowDensities

* **Conditions:** A fixed calibrated atlas with its normalized Haar product references, an explicit nonnegative physical density times chart-volume factors, and almost-everywhere atlas coverage.
* **Objects:** The actual joint label–clock density as a countable Jacobian-weighted sum, joint absolute continuity, normalized clock sections and equality to the original conditional law.
* **Proof detail:** Apply the window area formula to the given physical measure, disjoint overlaps, weight by transverse RN derivatives and identify sections by disintegration uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213): Section 4.1, conditional-expectation definition and Uniqueness argument, pp. 205–206; Section 4.1.3, Theorems 4.1.16–4.1.18, pp. 214–215.

Source relation (derived): Derives joint AC from the explicit window formulas rather than assuming it. The density retains original physical and chart-volume factors.
-/

/-!
# Original physical conditional densities from the calibrated atlas

The same chosen Haar family gives the original population's conditional clock
density. Every summand consists of its actual normalized Jacobian, physical
density and volume factor. Joint absolute continuity and section normalization
follow from the window formulas rather than additional hypotheses.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
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

/-- Actual physical window densities assemble into the existing conditional law.
The Haar family is fixed independently of the population, so the same family can
be used for both original colors. -/
theorem population_labelClock_window_densities
    (P : ℕ → F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPopulationAtlasLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instPopulationAtlasOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : ∀ j, Measure (P j).seed.covector.ker)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hprod : ∀ j, tubeParameterMeasure (P j).seed.normalization m =
      (volume : Measure ℝ).prod (κ j))
    (ωM : Measure M) (ρ : M → ℝ)
    [IsFiniteMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)))]
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (v : ℕ → E → ℝ) (hv : ∀ j, Measurable (v j))
    (hvolume : ∀ j, let χ := extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v j y)))
    (hcover : ∀ᵐ x ∂ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x)),
      x ∈ ⋃ j, (P j).toManifold '' (P j).domain) :
    let η := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))
    let O := fun j ↦ (P j).toManifold '' (P j).domain
    let C := disjointed O
    let L := fun j ↦ (P j).labels ∩
      ball (P j).center.2 ((P j).seed.radius (P j).center)
    let β := fun j ↦ ((κ j).comap ((↑) : L j → (P j).seed.covector.ker)).map
      (fun w : L j ↦ a ((P j).seed.curve w 0))
    let q := fun j (z : (P j).domain) ↦
      (a ((P j).toManifold z), u ((P j).toManifold z))
    let d := fun j (z : (P j).domain) ↦
      (ENNReal.ofReal (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
        ENNReal.ofReal (ρ ((P j).toManifold z) * v j ((P j).readout z))) *
          ((C j).indicator (fun _ : M ↦ (1 : ℝ≥0∞))) ((P j).toManifold z)
    let G := fun j ↦ Function.extend (q j) (d j) (fun _ : Z × ℝ ↦ 0)
    let lambda := η.map a
    let R := lambda.prod (volume : Measure ℝ)
    let H := fun y : Z × ℝ ↦ ∑' j, (β j).rnDeriv lambda y.1 * G j y
    (∀ j, IsFiniteMeasure (β j)) ∧ (∀ j, Measurable (G j)) ∧
      (∀ j, (η.restrict (C j)).map (fun x ↦ (a x, u x)) =
        ((β j).prod (volume : Measure ℝ)).withDensity (G j)) ∧
      η.map (fun x ↦ (a x, u x)) ≪ R ∧
      Measurable H ∧ R.withDensity H = η.map (fun x ↦ (a x, u x)) ∧
      (∀ᵐ z ∂lambda, ∫⁻ s, H (z, s) ∂volume = 1) ∧
      (∀ᵐ z ∂lambda,
        (volume : Measure ℝ).withDensity (fun s ↦ H (z, s)) = condDistrib u a η z) := by
  let _instPopulationAtlasMetric : MetricSpace M := F.metricSpace
  dsimp only
  let η := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))
  let O := fun j ↦ (P j).toManifold '' (P j).domain
  have hO (j : ℕ) : MeasurableSet (O j) := (P j).measurableSet_image hF hcomplete hu
  have hdata (j : ℕ) := by
    let _instPopulationSeedHaar : (κ j).IsAddHaarMeasure := hκ j
    exact (P j).map_labelClock_restrict_eq_withDensity_populationDensity hF hcomplete hu
      ha hinj horder m (κ j) (hprod j) ωM hρ hρ0 (hv j) (hvolume j)
      (MeasurableSet.disjointed hO j) (disjointed_subset O j)
  refine ⟨fun j ↦ (hdata j).1, fun j ↦ (hdata j).2.1,
    fun j ↦ (hdata j).2.2, ?_⟩
  apply labelClock_geometric_window_densities_of_pieces η ha hu.continuous.measurable
    O hO hcover
  · intro j
    let _instPopulationSeedFinite := (hdata j).1
    infer_instance
  · exact fun j ↦ (hdata j).2.1
  · exact fun j ↦ (hdata j).2.2

end OTSelector.Reconstruction

end
end
