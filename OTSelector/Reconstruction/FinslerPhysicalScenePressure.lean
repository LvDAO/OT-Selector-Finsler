import OTSelector.Reconstruction.FinslerPhysicalSceneTransport
import OTSelector.Geometry.Finsler.DistanceLocalizationSupportBound
import OTSelector.MeasureTheory.CompactSupportedIntegrability

/-!
# The same original physical pressure in actual seed coordinates

Every fractional coupling in an actual positive-mass root cell has the same
objective in the original physical law and in its Haar-clock scene law.  This
module specializes the full coupling pressure identity to original scaled
distance slack and the same bounded physical probe.  All integrability is
derived from the actual compact source carrier.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationHaarPressureCore

variable (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instScenePressureMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _instScenePressureOrder : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hb : Measurable b)
  (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
  (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
  (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)

include hcomplete hu in
/-- The original compact source gives every actual tilted scene cost an
integrable physical source section, even for an arbitrary fixed physical target. -/
theorem integrable_scene_physical_cost
    {A : Set M} (hA : IsCompact A) (hη₀A : ∀ᵐ x ∂η₀, x ∈ A)
    (L : Set (ℚ → M)) (k t : ℝ)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hgb : ∀ x y, |g x y| ≤ G) (y : M) :
    Integrable (fun x ↦ k * ((F.lengthEDist x y).toReal - u y + u x) + t * g x y)
      (normalizedFiniteLaw (η₀.restrict (a ⁻¹' L))) := by
  let _instScenePressureMetric : MetricSpace M := F.metricSpace
  let _instScenePressureProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePressurePolish : PolishSpace M := inferInstance
  let μ := normalizedFiniteLaw (η₀.restrict (a ⁻¹' L))
  have hμA : ∀ᵐ x ∂μ, x ∈ A := ae_normalizedFiniteLaw (ae_restrict_of_ae hη₀A)
  have hslack : Integrable (fun x ↦ (F.lengthEDist x y).toReal - u y + u x) μ := by
    have hi : IntegrableOn (fun x ↦ (F.lengthEDist x y).toReal - u y + u x) A μ :=
      ((F.continuous_distance_slack hu).comp
        (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact hA
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμA] at hi
  have hprobe : Integrable (fun x ↦ g x y) μ :=
    Integrable.of_bound (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (G : ℝ) (Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using hgb x y)
  exact (hslack.const_mul k).add (hprobe.const_mul t)

include hF hcomplete hu ha hinj horder hb hinv hη₀reg hη₁reg in
/-- The actual scene pressure equals the full original physical coupling
pressure at every target-mass vector.  The cost uses the same original length
distance, potential, probe, target cloud and normalized source restriction. -/
theorem fullSemidiscreteValue_scene_eq_physical
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) (hmass : 0 < lambda.real L)
    {A : Set M} (hA : IsCompact A) (hη₀A : ∀ᵐ x ∂η₀, x ∈ A)
    {n : ℕ}
    (cloud : Fin (n + 1) →
      ((P (D.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ))
    (hcloud : Injective
      (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed ∘ cloud))
    (k t : ℝ) (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hgb : ∀ x y, |g x y| ≤ G)
    (p : Fin (n + 1) → ℝ) (hpm : ∀ j, 0 ≤ p j) :
    let S := (P (D.continuous.coefficient i).seedIndex).seed
    let physical := populationSeedPhysicalMap S
    OTSelector.Probability.fullSemidiscreteValue (D.sceneLaw η₀ i L) cloud
        (fun s y ↦ k * ((F.lengthEDist (physical s) (physical y)).toReal -
          u (physical y) + u (physical s)) + t * g (physical s) (physical y)) p =
      OTSelector.Probability.fullSemidiscreteValue
        (normalizedFiniteLaw (η₀.restrict (a ⁻¹' L))) (physical ∘ cloud)
        (fun x y ↦ k * ((F.lengthEDist x y).toReal - u y + u x) + t * g x y) p := by
  let _instScenePressureMetric : MetricSpace M := F.metricSpace
  let _instScenePressureProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePressurePolish : PolishSpace M := inferInstance
  let S := (P (D.continuous.coefficient i).seedIndex).seed
  let physical := populationSeedPhysicalMap S
  let μ := normalizedFiniteLaw (η₀.restrict (a ⁻¹' L))
  have hsmass := (D.cell_masses hF hcomplete hu ha hinj i hL hsub).2.1
  have hμmass : 0 < (η₀.restrict (a ⁻¹' L)).real univ := by
    simpa only [measureReal_def, Measure.restrict_apply_univ, hsmass] using hmass
  let _instPhysicalProbability : IsProbabilityMeasure μ :=
    normalizedFiniteLaw_probability _ hμmass
  let _instSceneProbability : IsProbabilityMeasure (D.sceneLaw η₀ i L) :=
    (D.sceneLaw_probability hF hcomplete hu ha hinj i hL hsub hmass).1
  have hmap := (D.sceneLaw_physical_recovery hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg i hL hsub).1
  have hcoord := D.map_normalized_physical_eq_sceneLaw hF hcomplete hu ha hinj η₀ i L
  have hinverse := (D.physical_sceneCoordinate_inverse_ae hF hcomplete hu ha hinj
    horder hb hinv hη₀reg hη₁reg i hL hsub).1
  exact fullSemidiscreteValue_comp_of_inverse (measurable_populationSeedPhysicalMap S)
    hmap (D.sceneCoordinate i) (D.measurable_sceneCoordinate hF hcomplete hu ha hinj i)
    hcoord hinverse physical (measurable_populationSeedPhysicalMap S) cloud hcloud
    (fun x y ↦ k * ((F.lengthEDist x y).toReal - u y + u x) + t * g x y)
    (((F.measurable_distance_slack hu).const_mul k).add (hg.const_mul t))
    (fun j ↦ integrable_scene_physical_cost hcomplete hu hA hη₀A L k t g hg G hgb
      (physical (cloud j))) p hpm

end PopulationHaarPressureCore
end OTSelector.Reconstruction
