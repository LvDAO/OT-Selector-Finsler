import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.ChartPopulationDensity
import OTSelector.Geometry.Manifold.ChartScalarAbsoluteContinuity
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphJacobian
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedJacobiDeterminant
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindowPopulationDensity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindowPopulationDensity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindowPopulationDensity

* **Conditions:** An actual calibrated window and an explicitly represented chart population density, optionally factored into physical density and volume factor.
* **Objects:** Original population pullback density as actual Jacobian times physical/chart-volume factors, with a supplied graph determinant factorization variant.
* **Proof detail:** Replace the abstract chart RN representative by the stated withDensity formula, apply the actual area identity and insert the given determinant equality.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.

Source relation (derived): The graph-position determinant variant consumes its stated factorization; it is not inferred from a generic label density.
-/

/-!
# Physical population density in the original calibrated windows

An explicit chart density replaces the abstract Radon--Nikodym factor in the
actual window area formula. Applying the original population density to its
volume measure therefore gives the original physical density, volume factor and
normalized coordinate Jacobian on the same measured window.
-/

open Set MeasureTheory Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual area formula accepts a prescribed coordinate density directly. -/
theorem measure_image_eq_lintegral_of_chartDensity
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instExplicitWindowLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) (d : E → ℝ≥0∞)
    (hchart : let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
      (ν.restrict χ.source).map χ = (m.restrict χ.target).withDensity d)
    {s : Set (ℝ × P.seed.covector.ker)} (hs : MeasurableSet s) (hsD : s ⊆ P.domain) :
    ν (P.toManifold '' s) =
      ∫⁻ z in s,
        ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
          d (P.readout z) ∂(tubeParameterMeasure P.seed.normalization m) := by
  let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
  let νχ := (ν.restrict χ.source).map χ
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
    _ = ∫⁻ y in K, d y ∂m := by
      change ((ν.restrict χ.source).map χ) K = _
      dsimp only at hchart
      rw [hchart, withDensity_apply _ hK, Measure.restrict_restrict_of_subset hKt]
    _ = _ := P.lintegral_image_readout hF hcomplete hu m hs hsD d

/-- The original population's exact window pullback is physical density times
volume factor times the actual normalized Jacobian; abstract chart RN data are
fully eliminated from this formula. -/
theorem comap_toManifold_eq_withDensity_populationDensity
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPopulationWindowLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    {ρ : M → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {v : E → ℝ}
    (hv : AEMeasurable v
      (m.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).target))
    (hvolume : let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v y))) :
    let μpar := tubeParameterMeasure P.seed.normalization m
    (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).comap
      (fun z : P.domain ↦ P.toManifold z) =
      (μpar.comap ((↑) : P.domain → ℝ × P.seed.covector.ker)).withDensity
        (fun z ↦ ENNReal.ofReal
          (parameterizedJacobian P.readout P.seed.normalization z) *
          ENNReal.ofReal (ρ (P.toManifold z) * v (P.readout z))) := by
  let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))
  let d := fun y ↦ ENNReal.ofReal (ρ (χ.symm y) * v y)
  let w := fun z ↦ ENNReal.ofReal
    (parameterizedJacobian P.readout P.seed.normalization z) *
      ENNReal.ofReal (ρ (P.toManifold z) * v (P.readout z))
  have hchart : (ν.restrict χ.source).map χ = (m.restrict χ.target).withDensity d :=
    map_extChartAt_withDensity_of_volume_density (P.toManifold P.center) ωM m
      hρ hρ0 hv hvolume
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
  have hmass := P.measure_image_eq_lintegral_of_chartDensity hF hcomplete hu m ν d
    hchart hs (Subtype.coe_image_subset _ _)
  rw [image_image] at hmass
  refine hmass.trans ?_
  apply setLIntegral_congr_fun hs
  intro z hz
  have hzin : z ∈ P.domain := Subtype.coe_image_subset P.domain A hz
  have hinv : χ.symm (P.readout z) = P.toManifold z :=
    χ.left_inv (P.mapsTo_chart hzin.1)
  change _ * ENNReal.ofReal (ρ (χ.symm (P.readout z)) * _) = _
  rw [hinv]

/-- On a local actual graph chart, the same physical window law has its precise
position-determinant density. Original time is evaluated at the graph clock, and
both its speed factor and the fixed normalization determinant are retained.
The differential data are only required almost everywhere in the actual window. -/
theorem comap_toManifold_eq_withDensity_graphPositionDensity
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [DecidableEq ι]
    (P : CalibratedSeedWindow F u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGraphWindowLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    {ρ : M → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {v : E → ℝ}
    (hv : AEMeasurable v
      (m.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).target))
    (hvolume : let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v y)))
    (bW : Module.Basis ι ℝ P.seed.covector.ker) (bV : Module.Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V))
    (e : OpenPartialHomeomorph (P.seed.covector.ker × ℝ) (P.seed.covector.ker × ℝ))
    (he : (e : P.seed.covector.ker × ℝ → P.seed.covector.ker × ℝ) =
      curveGraphCoordinateMap (A ∘ fun q ↦ P.readout (q.2, q.1)))
    (hdata : let γ : P.seed.covector.ker × ℝ → E := fun q ↦ P.readout (q.2, q.1)
      ∀ᵐ z : P.domain ∂((tubeParameterMeasure P.seed.normalization m).comap
        ((↑) : P.domain → ℝ × P.seed.covector.ker)),
        (z.val.2, z.val.1) ∈ e.source ∧
        DifferentiableAt ℝ γ (z.val.2, z.val.1) ∧
        DifferentiableAt ℝ e.symm (z.val.2, (A (γ (z.val.2, z.val.1))).1) ∧
        (fderiv ℝ (A ∘ γ) (z.val.2, z.val.1) (0, 1)).1 ≠ 0) :
    let γ : P.seed.covector.ker × ℝ → E := fun q ↦ P.readout (q.2, q.1)
    let s := fun z : ℝ × P.seed.covector.ker ↦ (A (P.readout z)).1
    let c := fun z : ℝ × P.seed.covector.ker ↦
      (fderiv ℝ (A ∘ γ) (z.2, z.1) (0, 1)).1
    let J := fun (w : P.seed.covector.ker) (t : ℝ) ↦
      vectorFamilyMatrix bV (fun i ↦
        fderiv ℝ (fun z ↦ (curveGraphPosition (A ∘ γ) e (z, t)).2) w (bW i))
    let D := |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
      (P.seed.normalization.trans A).symm.toLinearEquiv.toLinearMap).det|
    (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).comap
      (fun z : P.domain ↦ P.toManifold z) =
      ((tubeParameterMeasure P.seed.normalization m).comap
        ((↑) : P.domain → ℝ × P.seed.covector.ker)).withDensity
        (fun z ↦ ENNReal.ofReal (|c z| * |(J z.val.2 (s z)).det| * D) *
          ENNReal.ofReal (ρ (P.toManifold z) * v (P.readout z))) := by
  dsimp only
  rw [P.comap_toManifold_eq_withDensity_populationDensity hF hcomplete hu m ωM
    hρ hρ0 hv hvolume]
  apply withDensity_congr_ae
  filter_upwards [hdata] with z hz
  have hJac := (parameterizedJacobian_adaptedGraphTime_data bW bV A P.seed.normalization
    he hz.1 hz.2.1 hz.2.2.1 hz.2.2.2).2
  change parameterizedJacobian P.readout P.seed.normalization z.val = _ at hJac
  rw [hJac]

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

end
end
