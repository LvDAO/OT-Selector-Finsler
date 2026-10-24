import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowPushforward
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.TubeParameterProduct
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
import OTSelector.MeasureTheory.GeometricWindowDensities
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerGeometricWindowDensities.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerGeometricWindowDensities`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.GeometricWindowDensities

* **Conditions:** A supplied calibrated atlas covers both finite populations, with common label law, chartwise densities and joint label–clock absolute continuity.
* **Objects:** One normalized transverse Haar family, exact window Jacobian-density laws, RN mass-piece formulas and normalized scalar conditional densities.
* **Proof detail:** Disjoint windows, push each actual geometric density through its injective label–clock map, compare transverse RN factors against the common marginal, and sum with disintegration uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213): Section 4.1, conditional-expectation definition and Uniqueness argument, pp. 205–206; Section 4.1.3, Theorems 4.1.16–4.1.18, pp. 214–215.

Source relation (derived): Geometric change of variables is combined with RN and conditional-law uniqueness; original populations and all reference normalization factors remain explicit.
-/

/-!
# Actual geometric formulas for the original conditional clock laws

A supplied original calibrated atlas uses one normalized Haar family for both
populations. Each existing mass-piece RN density is its actual Jacobian and chart
density, extended from legal coordinates, times a shared label-reference factor.
The sum gives the same original conditional laws with unit-mass sections.
-/

open Set MeasureTheory ProbabilityTheory Filter Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The same original atlas and labels admit one Haar family for both original laws.
Each actual mass-piece RN density is the original Jacobian-chart-density extension
multiplied by a shared geometric label-reference factor. Their sum gives the
existing normalized conditional clock laws on the common original label law. -/
theorem exists_labelHaar_geometric_conditional_windows
    (P : ℕ → F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGeometricWindowLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instGeometricWindowOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbalance : μ.map a = ν.map a)
    (hμchart : ∀ j,
      (μ.restrict (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)).source).map
        (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)) ≪ m)
    (hνchart : ∀ j,
      (ν.restrict (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)).source).map
        (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)) ≪ m)
    (hμcover : ∀ᵐ x ∂μ, x ∈ ⋃ j, (P j).toManifold '' (P j).domain)
    (hνcover : ∀ᵐ x ∂ν, x ∈ ⋃ j, (P j).toManifold '' (P j).domain)
    (hμjoint : μ.map (fun x ↦ (a x, u x)) ≪ (μ.map a).prod volume)
    (hνjoint : ν.map (fun x ↦ (a x, u x)) ≪ (ν.map a).prod volume) :
    ∃ κ : ∀ j, Measure (P j).seed.covector.ker,
      (∀ j, (κ j).IsAddHaarMeasure) ∧
      (∀ j, tubeParameterMeasure (P j).seed.normalization m =
        (volume : Measure ℝ).prod (κ j)) ∧
      let O := fun j ↦ (P j).toManifold '' (P j).domain
      let C := disjointed O
      let L := fun j ↦ (P j).labels ∩
        ball (P j).center.2 ((P j).seed.radius (P j).center)
      let β := fun j ↦
        ((κ j).comap ((↑) : L j → (P j).seed.covector.ker)).map
          (fun w : L j ↦ a ((P j).seed.curve w 0))
      let lambda := μ.map a
      let R := lambda.prod (volume : Measure ℝ)
      (∀ j, IsFiniteMeasure (β j)) ∧
      ∀ (η : Measure M) [IsFiniteMeasure η], η = μ ∨ η = ν →
        let q := fun j (z : (P j).domain) ↦
          (a ((P j).toManifold z), u ((P j).toManifold z))
        let d := fun j (z : (P j).domain) ↦
          let χ := extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)
          let ρ := ((η.restrict χ.source).map χ).rnDeriv m
          (ENNReal.ofReal
            (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
              ρ ((P j).readout z)) *
            ((C j).indicator (fun _ : M ↦ (1 : ℝ≥0∞))) ((P j).toManifold z)
        let G := fun j ↦ Function.extend (q j) (d j) (fun _ : Z × ℝ ↦ 0)
        let p := fun j ↦
          ((η.restrict (C j)).map (fun x ↦ (a x, u x))).rnDeriv R
        let H := fun y : Z × ℝ ↦ ∑' j, (β j).rnDeriv lambda y.1 * G j y
        (∀ j, Measurable (G j)) ∧
          (∀ j, (η.restrict (C j)).map (fun x ↦ (a x, u x)) =
            ((β j).prod (volume : Measure ℝ)).withDensity (G j)) ∧
          (∀ j, p j =ᵐ[R] (fun y ↦ (β j).rnDeriv lambda y.1 * G j y)) ∧
          Measurable H ∧ R.withDensity H = η.map (fun x ↦ (a x, u x)) ∧
          (∀ᵐ z ∂lambda, ∫⁻ s, H (z, s) ∂volume = 1) ∧
          (∀ᵐ z ∂lambda,
            (volume : Measure ℝ).withDensity (fun s ↦ H (z, s)) = condDistrib u a η z)
 := by
  classical
  let _instGeometricWindowMetric : MetricSpace M := F.metricSpace
  choose κ hκ hprod using fun j ↦
    exists_tubeParameterMeasure_eq_volume_prod (P j).seed.normalization m
  let O := fun j ↦ (P j).toManifold '' (P j).domain
  let C := disjointed O
  let L := fun j ↦ (P j).labels ∩
    ball (P j).center.2 ((P j).seed.radius (P j).center)
  let β := fun j ↦
    ((κ j).comap ((↑) : L j → (P j).seed.covector.ker)).map
      (fun w : L j ↦ a ((P j).seed.curve w 0))
  let q := fun j (z : (P j).domain) ↦
    (a ((P j).toManifold z), u ((P j).toManifold z))
  let d := fun (η : Measure M) j (z : (P j).domain) ↦
    let χ := extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)
    let ρ := ((η.restrict χ.source).map χ).rnDeriv m
    (ENNReal.ofReal
      (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
        ρ ((P j).readout z)) *
      ((C j).indicator (fun _ : M ↦ (1 : ℝ≥0∞))) ((P j).toManifold z)
  let G := fun (η : Measure M) j ↦ Function.extend (q j) (d η j) (fun _ : Z × ℝ ↦ 0)
  have hO (j : ℕ) : MeasurableSet (O j) := (P j).measurableSet_image hF hcomplete hu
  have hwindow (η : Measure M) [IsFiniteMeasure η]
      (hchart : ∀ j,
        (η.restrict (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)).source).map
          (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)) ≪ m) (j : ℕ) :
      IsFiniteMeasure (β j) ∧ Measurable (G η j) ∧
        (η.restrict (C j)).map (fun x ↦ (a x, u x)) =
          ((β j).prod (volume : Measure ℝ)).withDensity (G η j) := by
    let _instGeometricWindowHaar : (κ j).IsAddHaarMeasure := hκ j
    exact (P j).map_labelClock_restrict_eq_withDensity hF hcomplete hu ha hinj horder m
      (κ j) (hprod j) η (hchart j) (MeasurableSet.disjointed hO j) (disjointed_subset O j)
  have hβ (j : ℕ) : IsFiniteMeasure (β j) := (hwindow μ hμchart j).1
  refine ⟨κ, hκ, hprod, hβ, ?_⟩
  intro η _ hη
  have hdata : η.map a = μ.map a ∧
      (∀ j,
        (η.restrict (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)).source).map
          (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)) ≪ m) ∧
      (∀ᵐ x ∂η, x ∈ ⋃ j, O j) ∧
      η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume := by
    rcases hη with hη | hη
    · subst η
      exact ⟨rfl, hμchart, hμcover, hμjoint⟩
    · subst η
      exact ⟨hbalance.symm, hνchart, hνcover, hνjoint⟩
  obtain ⟨hηmap, hηchart, hηcover, hηjoint⟩ := hdata
  have hG (j : ℕ) : Measurable (G η j) := (hwindow η hηchart j).2.1
  have hpiece (j : ℕ) :
      (η.restrict (C j)).map (fun x ↦ (a x, u x)) =
        ((β j).prod (volume : Measure ℝ)).withDensity (G η j) :=
    (hwindow η hηchart j).2.2
  have hβsigma (j : ℕ) : SigmaFinite (β j) := by
    let _instGeometricSeedFinite : IsFiniteMeasure (β j) := hβ j
    infer_instance
  have hresult := labelClock_geometric_window_densities η ha hu.continuous.measurable
    O hO hηcover hηjoint β hβsigma (G η) hG hpiece
  dsimp only at hresult
  rw [hηmap] at hresult
  exact ⟨hG, hpiece, hresult⟩

end OTSelector.Reconstruction

end
end
