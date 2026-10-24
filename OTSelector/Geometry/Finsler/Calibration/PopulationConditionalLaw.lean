import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowLabels
import OTSelector.Geometry.Finsler.Calibration.PopulationWindowDensities
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
import OTSelector.MeasureTheory.ProductReferenceDensity
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationConditionalLaw.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationConditionalLaw`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.PopulationConditionalLaw

* **Conditions:** A fixed calibrated atlas and reference Haar family, with a measurable nonnegative physical density and exact chart-volume formulas; reconstruction also assumes a measurable AE inverse.
* **Objects:** Explicit window pieces, label reference measures and conditional density functions, a packaged population law and all nonnegative-observable reconstruction formulas.
* **Proof detail:** Define first-occurrence mass pieces and zero-extended window densities, invoke the actual geometric density theorem, then change variables through the same label–clock inverse and Tonelli.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.

Source relation (adapter): Definitions package the previously derived formulas; they introduce no replacement population, quotient or coefficient.
-/

/-!
# Explicit physical laws on a fixed original calibrated atlas

The window reference is chosen independently of the population. Its physical
density retains the window indicator, original volume factor and normalized
Jacobian. The sum reconstructs the existing conditional law and all original
nonnegative observables through the same label-clock inverse.
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

/-- The disjoint physical piece assigned to a window in the enumeration. -/
def populationWindowPiece (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) : Set M :=
  disjointed (fun k ↦ (P k).toManifold '' (P k).domain) j

/-- The finite geometric label reference of a window, independent of population density. -/
def populationWindowLabelReference (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (j : ℕ) : Measure Z :=
  let L := (P j).labels ∩ ball (P j).center.2 ((P j).seed.radius (P j).center)
  ((κ j).comap ((↑) : L → (P j).seed.covector.ker)).map
    (fun w : L ↦ a ((P j).seed.curve w 0))

/-- The actual physical window density, extended by zero in the original label and clock. -/
def populationWindowDensity (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ) : Z × ℝ → ℝ≥0∞ :=
  Function.extend
    (fun z : (P j).domain ↦ (a ((P j).toManifold z), u ((P j).toManifold z)))
    (fun z : (P j).domain ↦
      (ENNReal.ofReal (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
        ENNReal.ofReal (ρ ((P j).toManifold z) * v j ((P j).readout z))) *
          ((populationWindowPiece P j).indicator (fun _ : M ↦ (1 : ℝ≥0∞)))
            ((P j).toManifold z)) (fun _ ↦ 0)

/-- The physical conditional density on one original label law. -/
def populationConditionalDensity (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (y : Z × ℝ) : ℝ≥0∞ :=
  ∑' j, (populationWindowLabelReference P a κ j).rnDeriv lambda y.1 *
    populationWindowDensity P a ρ v j y

/-- Exact physical window and conditional laws with a specified common label reference. -/
structure PopulationConditionalWindowLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → Z) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure Z) (η : Measure M) [IsFiniteMeasure η]
    (ρ : M → ℝ) (v : ℕ → E → ℝ) : Prop where
  label_law : η.map a = lambda
  reference_finite : ∀ j, IsFiniteMeasure (populationWindowLabelReference P a κ j)
  window_measurable : ∀ j, Measurable (populationWindowDensity P a ρ v j)
  window_law : ∀ j,
    (η.restrict (populationWindowPiece P j)).map (fun x ↦ (a x, u x)) =
      ((populationWindowLabelReference P a κ j).prod (volume : Measure ℝ)).withDensity
        (populationWindowDensity P a ρ v j)
  window_rnDeriv : ∀ j,
    ((η.restrict (populationWindowPiece P j)).map (fun x ↦ (a x, u x))).rnDeriv
        (lambda.prod (volume : Measure ℝ)) =ᵐ[lambda.prod (volume : Measure ℝ)]
      (fun y ↦ (populationWindowLabelReference P a κ j).rnDeriv lambda y.1 *
        populationWindowDensity P a ρ v j y)
  joint_absolutelyContinuous : η.map (fun x ↦ (a x, u x)) ≪ lambda.prod volume
  density_measurable : Measurable (populationConditionalDensity P a κ lambda ρ v)
  joint_law : (lambda.prod (volume : Measure ℝ)).withDensity
      (populationConditionalDensity P a κ lambda ρ v) = η.map (fun x ↦ (a x, u x))
  normalized : ∀ᵐ z ∂lambda,
    ∫⁻ s, populationConditionalDensity P a κ lambda ρ v (z, s) ∂volume = 1
  conditional_law : ∀ᵐ z ∂lambda,
    (volume : Measure ℝ).withDensity
      (fun s ↦ populationConditionalDensity P a κ lambda ρ v (z, s)) = condDistrib u a η z

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] in
/-- On legal coordinates the extension is exactly the original physical formula. -/
theorem populationWindowDensity_apply (P : ℕ → F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPopulationDensityMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ) (z : (P j).domain) :
    populationWindowDensity P a ρ v j (a ((P j).toManifold z), u ((P j).toManifold z)) =
      (ENNReal.ofReal (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
        ENNReal.ofReal (ρ ((P j).toManifold z) * v j ((P j).readout z))) *
          ((populationWindowPiece P j).indicator (fun _ : M ↦ (1 : ℝ≥0∞)))
            ((P j).toManifold z) := by
  have hreg (y : (P j).domain) : (P j).toManifold y ∈ F.potentialRegularDomain u :=
    hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
      ((P j).mapsTo_calibratedInterior hF hu y.property)
  have hq : Function.Injective (fun y : (P j).domain ↦
      (a ((P j).toManifold y), u ((P j).toManifold y))) := by
    intro x y h
    have hxy := congrArg Subtype.val (hinj (a₁ := ⟨_, hreg x⟩) (a₂ := ⟨_, hreg y⟩) h)
    exact Subtype.ext ((P j).injOn_toManifold hF hcomplete hu x.property y.property hxy)
  exact hq.extend_apply _ _ z

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] in
/-- The same density at the original seed label and translated complete-curve time.
The actual potential clock is the seed level plus the original family time. -/
theorem populationWindowDensity_apply_clock (P : ℕ → F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPopulationClockMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instPopulationClockOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (ρ : M → ℝ) (v : ℕ → E → ℝ) (j : ℕ) (z : (P j).domain) :
    populationWindowDensity P a ρ v j
        (a ((P j).seed.curve z.val.2 0), (P j).seed.level + z.val.1) =
      (ENNReal.ofReal (parameterizedJacobian (P j).readout (P j).seed.normalization z) *
        ENNReal.ofReal (ρ ((P j).seed.curve z.val.2 z.val.1) * v j ((P j).readout z))) *
          ((populationWindowPiece P j).indicator (fun _ : M ↦ (1 : ℝ≥0∞)))
            ((P j).seed.curve z.val.2 z.val.1) := by
  have hlabel := (P j).label_toManifold_eq_initial hF hcomplete hu horder z.property
  have hclock : u ((P j).toManifold z) = (P j).seed.level + z.val.1 :=
    (hF.calibrated_window_of_complete_unit_endpoints hu
      ((P j).seed.complete z.val.2 z.property.2.2.1)
      ((P j).seed.unit z.val.2 z.property.2.2.1)
      z.property.2.2.2.1 z.property.2.2.2.2).1 z.val.1
        ⟨z.property.2.1.1.le, z.property.2.1.2.le⟩
  have h := populationWindowDensity_apply P hF hcomplete hu hinj ρ v j z
  rw [hlabel, hclock] at h
  simpa only [ContinuousFinslerNorm.CalibratedSeedWindow.toManifold] using h

/-- The fixed geometric Haar family gives the physical conditional law on its original marginal. -/
theorem populationConditionalWindowLaw_of_atlas
    (P : ℕ → F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPopulationLawMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instPopulationLawOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : ∀ j, Measure (P j).seed.covector.ker) (hκ : ∀ j, (κ j).IsAddHaarMeasure)
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
      x ∈ ⋃ j, (P j).toManifold '' (P j).domain)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    (hlambda : (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))).map a = lambda) :
    PopulationConditionalWindowLaw P a κ lambda
      (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) ρ v := by
  obtain ⟨hfinite, hG, hpiece, hAC, hH, hden, hnorm, hcond⟩ :=
    population_labelClock_window_densities P hF hcomplete hu ha hinj horder m κ hκ
      hprod ωM ρ hρ hρ0 v hv hvolume hcover
  dsimp only at hfinite hG hpiece hAC hH hden hnorm hcond
  rw [hlambda] at hAC hH hden hnorm hcond
  refine ⟨hlambda, hfinite, hG, hpiece, ?_, hAC, hH, hden, hnorm, hcond⟩
  intro j
  let _instPopulationReferenceFinite :
      IsFiniteMeasure (populationWindowLabelReference P a κ j) := hfinite j
  unfold populationWindowPiece
  rw [hpiece j]
  exact rnDeriv_prod_withDensity lambda (populationWindowLabelReference P a κ j) volume (hG j)

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [BorelSpace M] [MeasurableSpace.CountablySeparated Z] in
/-- The exact physical density reconstructs every original nonnegative observable. -/
theorem PopulationConditionalWindowLaw.lintegral_reconstruction
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    [SigmaFinite lambda] {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (h : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (ha : Measurable a) (hu : Measurable u) {b : Z × ℝ → M} (hb : Measurable b)
    (hbinv : ∀ᵐ x ∂η, b (a x, u x) = x) (g : M → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂η) = ∫⁻ z, ∫⁻ s,
      populationConditionalDensity P a κ lambda ρ v (z, s) * g (b (z, s)) ∂volume ∂lambda := by
  calc
    (∫⁻ x, g x ∂η) = ∫⁻ x, g (b (a x, u x)) ∂η :=
      lintegral_congr_ae (hbinv.mono fun x hx ↦ congrArg g hx.symm)
    _ = ∫⁻ y, g (b y) ∂η.map (fun x ↦ (a x, u x)) :=
      (lintegral_map (hg.comp hb) (ha.prodMk hu)).symm
    _ = ∫⁻ y, g (b y) ∂(lambda.prod volume).withDensity
        (populationConditionalDensity P a κ lambda ρ v) := by rw [h.joint_law]
    _ = ∫⁻ y, populationConditionalDensity P a κ lambda ρ v y * g (b y)
        ∂lambda.prod volume :=
      lintegral_withDensity_eq_lintegral_mul _ h.density_measurable (hg.comp hb)
    _ = _ := lintegral_prod _ (h.density_measurable.mul (hg.comp hb)).aemeasurable

end OTSelector.Reconstruction

end
end
