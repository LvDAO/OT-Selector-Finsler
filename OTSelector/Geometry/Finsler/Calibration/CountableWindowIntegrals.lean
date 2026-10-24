import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowFubini
import OTSelector.Geometry.Finsler.CalibratedSeedWindowRestriction
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
import OTSelector.MeasureTheory.CountableWindowIntegrals
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerCountableWindowIntegrals.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerCountableWindowIntegrals`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.CountableWindowIntegrals

* **Conditions:** A countable calibrated atlas covers an S-finite population chartwise absolutely continuous to a fixed Haar measure; measurable original labels encode calibration.
* **Objects:** One normalized transverse Haar family and an exact countable-window formula for every original-label restriction and nonnegative measurable test.
* **Proof detail:** Disjoint the manifold window images, insert their indicators into the actual Jacobian–RN density, apply the local area formula and Tonelli, and sum the original mass pieces.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (derived): The area formula supports each window; disjoint indicators, normalized Haar constants and arbitrary population RN factors are explicit local assembly.
-/

/-!
# Original-law integrals over a countable calibrated atlas

Disjointing the physical window images assigns every covered point to one window.
The corresponding indicator enters the integrand, retaining each original product
domain, normalized Haar reference and actual Jacobian-density weight. One family
of label measures works for all original-label restrictions and nonnegative tests.
-/

open Set MeasureTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- A countable calibrated cover gives an exact global iterated-integral sum without
double counting. Each window retains its own Haar reference, chosen once for every
Borel original-label piece and measurable nonnegative observable. -/
theorem exists_labelHaar_setLIntegral_countable_atlas
    (P : ℕ → F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasIntegralLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (horder : let _instAtlasIntegralOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure] (η : Measure M) [SFinite η]
    (hηchart : ∀ j,
      (η.restrict (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)).source).map
        (extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)) ≪ m)
    (hcover : ∀ᵐ x ∂η, x ∈ ⋃ j, (P j).toManifold '' (P j).domain) :
    let C := disjointed (fun j ↦ (P j).toManifold '' (P j).domain)
    ∃ κ : ∀ j, Measure (P j).seed.covector.ker,
      (∀ j, (κ j).IsAddHaarMeasure) ∧
      (∀ j, tubeParameterMeasure (P j).seed.normalization m =
        (volume : Measure ℝ).prod (κ j)) ∧
      ∀ B : Set Z, MeasurableSet B → ∀ g : M → ℝ≥0∞, Measurable g →
        (∫⁻ x in a ⁻¹' B, g x ∂η) =
          ∑' j,
            let χ := extChartAt 𝓘(ℝ, E) ((P j).toManifold (P j).center)
            let ρ := ((η.restrict χ.source).map χ).rnDeriv m
            ∫⁻ w in (P j).seedLabelSlice a B ∩
                ball (P j).center.2 ((P j).seed.radius (P j).center),
              ∫⁻ t in Ioo ((P j).left : ℝ) (P j).right ∩
                  ball (P j).center.1 ((P j).seed.radius (P j).center),
                (ENNReal.ofReal (parameterizedJacobian (P j).readout
                  (P j).seed.normalization (t, w)) * ρ ((P j).readout (t, w))) *
                  ((C j).indicator g) ((P j).toManifold (t, w)) ∂volume ∂κ j := by
  classical
  dsimp only
  choose κ hκ hprod hformula using fun j ↦
    (P j).exists_labelHaar_setLIntegral_labelRestriction hF hcomplete hu ha horder m η
      (hηchart j)
  refine ⟨κ, hκ, hprod, ?_⟩
  intro B hB g hg
  have hO (j : ℕ) : MeasurableSet ((P j).toManifold '' (P j).domain) :=
    (P j).measurableSet_image hF hcomplete hu
  rw [setLIntegral_eq_tsum_window_indicator η
    (fun j ↦ (P j).toManifold '' (P j).domain) hO hcover (hB.preimage ha) g]
  apply tsum_congr
  intro j
  exact hformula j B hB _ (hg.indicator (MeasurableSet.disjointed hO j))

end OTSelector.Reconstruction

end
end
