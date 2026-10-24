import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.ChartScalarAbsoluteContinuity
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindowVolume.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindowVolume`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindowVolume

* **Conditions:** An actual calibrated window and an S-finite original population chartwise absolutely continuous to the given Haar reference.
* **Objects:** Exact image and pullback laws with original chart RN density times the actual normalized Jacobian, plus AC and reconstruction.
* **Proof detail:** Combine the chart pushforward RN formula with injective area change of variables, then identify measures from their values on measurable window subsets.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (derived): A precise pullback-density assembly from classical area/RN formulas; neither density nor Jacobian is assumed everywhere positive.
-/

/-!
# Exact original measure in actual calibrated window coordinates

The original chartwise absolutely continuous law pulls back to the actual parameter
reference with density equal to its chart Radon--Nikodym derivative times the actual
normalized Jacobian. All identities retain the original measure and normalization;
the density and Jacobian may vanish.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Original mass on every measurable window subpiece is its actual Jacobian-weighted
chart density integral, with the chosen parameter Haar normalization retained. -/
theorem measure_image_eq_lintegral_chartDensity
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowMassLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [SFinite ν]
    (hνchart :
      (ν.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
        (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m)
    {s : Set (ℝ × P.seed.covector.ker)} (hs : MeasurableSet s) (hsD : s ⊆ P.domain) :
    let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
    let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
    ν (P.toManifold '' s) =
      ∫⁻ z in s,
        ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
          ρ (P.readout z) ∂(tubeParameterMeasure P.seed.normalization m) := by
  let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
  let νχ := (ν.restrict χ.source).map χ
  let ρ := νχ.rnDeriv m
  let K := P.readout '' s
  have hK : MeasurableSet K := hs.image_of_continuousOn_injOn
    (P.lipschitzOn_readout.continuousOn.mono (hsD.trans inter_subset_left))
    ((P.injOn_readout hF hcomplete hu).mono hsD)
  have hKt : K ⊆ χ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact χ.map_source (P.mapsTo_chart (hsD hz).1)
  have himage : χ.symm '' K = P.toManifold '' s := by
    rw [show K = P.readout '' s from rfl, image_image]
    apply image_congr
    intro z hz
    exact χ.left_inv (P.mapsTo_chart (hsD hz).1)
  have hi : AEMeasurable χ.symm (νχ.restrict K) :=
    ((continuousOn_extChartAt_symm (P.toManifold P.center)).mono hKt).aemeasurable hK
  have hmass := congrArg (fun η : Measure M ↦ η univ)
    (map_symm_extChartAt_restrict_eq_chart_core (P.toManifold P.center) ν hK hKt)
  change ((νχ.restrict K).map χ.symm) univ = _ at hmass
  rw [Measure.map_apply_of_aemeasurable hi MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Measure.restrict_apply_univ, himage] at hmass
  calc
    ν (P.toManifold '' s) = νχ K := hmass.symm
    _ = ∫⁻ y in K, ρ y ∂m := (Measure.setLIntegral_rnDeriv' hνchart hK).symm
    _ = _ := P.lintegral_image_readout hF hcomplete hu m hs hsD ρ

/-- The actual original-law pullback on the measured domain has the explicitly
constructed chart density times normalized Jacobian as its parameter density. -/
theorem comap_toManifold_eq_withDensity_chartDensity
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowPullbackLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [SFinite ν]
    (hνchart :
      (ν.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
        (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m) :
    let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
    let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
    let μpar := tubeParameterMeasure P.seed.normalization m
    ν.comap (fun z : P.domain ↦ P.toManifold z) =
      (μpar.comap ((↑) : P.domain → ℝ × P.seed.covector.ker)).withDensity
        (fun z ↦ ENNReal.ofReal
          (parameterizedJacobian P.readout P.seed.normalization z) * ρ (P.readout z)) := by
  let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
  let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
  let w := fun z ↦ ENNReal.ofReal
    (parameterizedJacobian P.readout P.seed.normalization z) * ρ (P.readout z)
  have hD := P.measurableSet_domain hu
  have he := P.measurableEmbedding_toManifold hF hcomplete hu
  dsimp only
  ext A hA
  rw [he.comap_apply, withDensity_apply _ hA]
  change ν ((fun z : P.domain ↦ P.toManifold z) '' A) =
    ∫⁻ z in A, w z ∂((tubeParameterMeasure P.seed.normalization m).comap
      ((↑) : P.domain → ℝ × P.seed.covector.ker))
  rw [setLIntegral_subtype hD A w]
  have hs := (MeasurableEmbedding.subtype_coe hD).measurableSet_image.mpr hA
  simpa only [image_image, Function.comp_def] using
    P.measure_image_eq_lintegral_chartDensity hF hcomplete hu m ν hνchart hs
      (Subtype.coe_image_subset _ _)

/-- The actual original-law pullback is absolutely continuous with respect to the
retained parameter reference, without a positive-Jacobian premise. -/
theorem comap_toManifold_absolutelyContinuous
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowACLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [SFinite ν]
    (hνchart :
      (ν.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
        (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m) :
    ν.comap (fun z : P.domain ↦ P.toManifold z) ≪
      (tubeParameterMeasure P.seed.normalization m).comap
        ((↑) : P.domain → ℝ × P.seed.covector.ker) := by
  rw [P.comap_toManifold_eq_withDensity_chartDensity hF hcomplete hu m ν hνchart]
  exact withDensity_absolutelyContinuous _ _

/-- Mapping the actual window pullback reconstructs precisely the original measure
restricted to that window's image. -/
theorem map_comap_toManifold_eq_restrict
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowReconstructionLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) (ν : Measure M) :
    (ν.comap (fun z : P.domain ↦ P.toManifold z)).map
      (fun z : P.domain ↦ P.toManifold z) = ν.restrict (P.toManifold '' P.domain) := by
  rw [(P.measurableEmbedding_toManifold hF hcomplete hu).map_comap]
  congr 1
  ext y
  simp only [mem_range, mem_image, Subtype.exists]
  exact ⟨fun ⟨z, hz, he⟩ ↦ ⟨z, hz, he⟩, fun ⟨z, hz, he⟩ ↦ ⟨z, hz, he⟩⟩

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

end
end
