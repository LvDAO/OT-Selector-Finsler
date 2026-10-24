import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowRestriction
import OTSelector.Geometry.Finsler.CalibratedSeedWindowVolume
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.TubeParameterProduct
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedJacobianMeasurable
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindowFubini.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindowFubini`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindowFubini

* **Conditions:** A chartwise absolutely continuous original population and a nonnegative measurable physical observable on a Borel window subpiece.
* **Objects:** Exact weighted original-law window integrals and their time-first Haar-label form under geometric label restrictions.
* **Proof detail:** Use the original pullback density, prove only restricted-domain AE measurability where needed, split the actual product reference and apply Tonelli.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (derived): Retains the original RN factor, Jacobian and label normalization; no arbitrary off-domain extension is assumed measurable.
-/

/-!
# Original weighted window integrals in time and label coordinates

The original-law pullback density transfers every nonnegative measurable physical
observable on each Borel window subpiece. On restrictions by existing geometric
labels, the same reference has an exact product normalization and Tonelli gives
the time-first integral. All densities and Jacobians belong to the original law
and map; no arbitrary extension outside the legal domain is assumed measurable.
-/

open Set MeasureTheory Manifold Metric
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [T2Space M] [PreconnectedSpace M] in
/-- The actual Jacobian, chart density and physical observable have an ae-measurable
product on each legal Borel subpiece, using only local continuity of the maps. -/
theorem aemeasurable_chartDensity_mul (P : CalibratedSeedWindow F u)
    (m : Measure E) (ν : Measure M) {s : Set (ℝ × P.seed.covector.ker)}
    (hs : MeasurableSet s) (hsD : s ⊆ P.domain) {g : M → ℝ≥0∞} (hg : Measurable g) :
    let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
    let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
    AEMeasurable (fun z ↦
      (ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
        ρ (P.readout z)) * g (P.toManifold z))
      ((tubeParameterMeasure P.seed.normalization m).restrict s) := by
  have hr := (P.lipschitzOn_readout.continuousOn.mono
    (hsD.trans inter_subset_left)).aemeasurable (μ := tubeParameterMeasure P.seed.normalization m) hs
  have hX := (P.continuousOn_toManifold.mono
    (hsD.trans inter_subset_left)).aemeasurable (μ := tubeParameterMeasure P.seed.normalization m) hs
  have hJ := (measurable_parameterizedJacobian P.readout P.seed.normalization).ennreal_ofReal
  exact (hJ.aemeasurable.mul
    ((Measure.measurable_rnDeriv _ _).comp_aemeasurable hr)).mul (hg.comp_aemeasurable hX)

/-- Every nonnegative measurable physical observable has its exact original-law
weighted integral on any Borel subpiece of the actual calibrated window. -/
theorem setLIntegral_image_eq_chartDensity_mul (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWeightedWindowLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [SFinite ν]
    (hνchart :
      (ν.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
        (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m)
    {s : Set (ℝ × P.seed.covector.ker)} (hs : MeasurableSet s) (hsD : s ⊆ P.domain)
    {g : M → ℝ≥0∞} (hg : Measurable g) :
    let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
    let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
    (∫⁻ x in P.toManifold '' s, g x ∂ν) =
      ∫⁻ z in s,
        (ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
          ρ (P.readout z)) * g (P.toManifold z)
        ∂(tubeParameterMeasure P.seed.normalization m) := by
  let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
  let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
  let w := fun z ↦ ENNReal.ofReal
    (parameterizedJacobian P.readout P.seed.normalization z) * ρ (P.readout z)
  let e := fun z : P.domain ↦ P.toManifold z
  let A : Set P.domain := ((↑) : P.domain → ℝ × P.seed.covector.ker) ⁻¹' s
  have hA : MeasurableSet A := hs.preimage measurable_subtype_coe
  have hcoe : ((↑) : P.domain → ℝ × P.seed.covector.ker) '' A = s := by
    ext z
    exact ⟨fun ⟨q, hq, heq⟩ ↦ heq ▸ hq, fun hz ↦ ⟨⟨z, hsD hz⟩, hz, rfl⟩⟩
  have he := P.measurableEmbedding_toManifold hF hcomplete hu
  have hr : Measurable (fun z : P.domain ↦ P.readout z) :=
    (continuousOn_iff_continuous_domRestrict.mp
      (P.lipschitzOn_readout.continuousOn.mono inter_subset_left)).measurable
  have hw : Measurable (fun z : P.domain ↦ w z) :=
    (((measurable_parameterizedJacobian P.readout P.seed.normalization).comp
      measurable_subtype_coe).ennreal_ofReal).mul ((Measure.measurable_rnDeriv _ _).comp hr)
  have hmp : MeasurePreserving e (ν.comap e) (ν.restrict (P.toManifold '' P.domain)) :=
    ⟨he.measurable, P.map_comap_toManifold_eq_restrict hF hcomplete hu ν⟩
  have himg : e '' A = P.toManifold '' s := by
    rw [← hcoe, image_image]
  calc
    (∫⁻ x in P.toManifold '' s, g x ∂ν) =
        ∫⁻ x in e '' A, g x ∂ν.restrict (P.toManifold '' P.domain) := by
      rw [himg, Measure.restrict_restrict_of_subset (image_mono hsD)]
    _ = ∫⁻ z in A, g (e z) ∂ν.comap e := (hmp.setLIntegral_comp_emb he g A).symm
    _ = ∫⁻ z in A, w z * g (P.toManifold z)
        ∂((tubeParameterMeasure P.seed.normalization m).comap
          ((↑) : P.domain → ℝ × P.seed.covector.ker)) := by
      rw [P.comap_toManifold_eq_withDensity_chartDensity hF hcomplete hu m ν hνchart]
      exact setLIntegral_withDensity_eq_setLIntegral_mul _ hw (hg.comp he.measurable) hA
    _ = _ := by
      rw [setLIntegral_subtype (P.measurableSet_domain hu) A
        (fun z ↦ w z * g (P.toManifold z)), hcoe]

/-- A single normalized label Haar measure gives exact time-first integrals for
all Borel restrictions by the old labels and all measurable physical observables. -/
theorem exists_labelHaar_setLIntegral_labelRestriction
    {Z : Type*} [MeasurableSpace Z] (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowFubiniLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (horder : let _instWindowFubiniOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [SFinite ν]
    (hνchart :
      (ν.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
        (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m) :
    ∃ κ : Measure P.seed.covector.ker, κ.IsAddHaarMeasure ∧
      tubeParameterMeasure P.seed.normalization m = (volume : Measure ℝ).prod κ ∧
      ∀ B : Set Z, MeasurableSet B → ∀ g : M → ℝ≥0∞, Measurable g →
        let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
        let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
        (∫⁻ x in (P.toManifold '' P.domain) ∩ a ⁻¹' B, g x ∂ν) =
          ∫⁻ w in P.seedLabelSlice a B ∩ ball P.center.2 (P.seed.radius P.center),
            ∫⁻ t in Ioo (P.left : ℝ) P.right ∩ ball P.center.1 (P.seed.radius P.center),
              (ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization (t, w)) *
                ρ (P.readout (t, w))) * g (P.toManifold (t, w)) ∂volume ∂κ := by
  obtain ⟨κ, hκ, hprod⟩ := exists_tubeParameterMeasure_eq_volume_prod P.seed.normalization m
  let _instWindowLabelHaar : κ.IsAddHaarMeasure := hκ
  refine ⟨κ, hκ, hprod, ?_⟩
  intro B hB g hg
  have hs := P.measurableSet_labelRestrictedDomain hF hcomplete hu ha horder hB
  have hsD : P.labelRestrictedDomain a B ⊆ P.domain := inter_subset_left
  have hdom := P.labelRestrictedDomain_eq_prod hF hcomplete hu horder B
  rw [← P.image_labelRestrictedDomain a B,
    P.setLIntegral_image_eq_chartDensity_mul hF hcomplete hu m ν hνchart hs hsD hg,
    hprod, hdom]
  apply setLIntegral_prod_symm
  rw [← hdom, ← hprod]
  exact P.aemeasurable_chartDensity_mul m ν hs hsD hg

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

end
end
