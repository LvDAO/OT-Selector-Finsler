import OTSelector.Reconstruction.FinslerPhysicalSceneTransport
import OTSelector.Probability.IIDBipartiteAssignment

/-!
# Atomlessness on the actual normalized physical scenes

The original chartwise absolutely continuous populations give atomless actual
scene laws.  Exact physical recovery also makes finite iid scene targets almost
surely physically distinct.  Consequently their scaled original distance-slack
differences are atomless on the actual normalized source scene law.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Finite normalization preserves the original zero mass of every singleton. -/
theorem nullSingletonClass_normalizedFiniteLaw {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NullSingletonClass μ] :
    NullSingletonClass (normalizedFiniteLaw μ) := by
  refine ⟨fun x ↦ ?_⟩
  simp only [normalizedFiniteLaw, Measure.smul_apply, measure_singleton, smul_zero]

/-- A measurable physical image with zero singleton masses forces the actual
coordinate law to have zero singleton masses as well. -/
theorem nullSingletonClass_of_physical_map {X S : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace S]
    (ν : Measure S) (physical : S → X) (hp : Measurable physical)
    [NullSingletonClass (ν.map physical)] : NullSingletonClass ν := by
  refine ⟨fun s ↦ ?_⟩
  have hnull : ν (physical ⁻¹' {physical s}) = 0 := by
    rw [← Measure.map_apply hp (measurableSet_singleton _)]
    exact measure_singleton _
  apply measure_mono_null _ hnull
  intro t ht
  change physical t = physical s
  rw [mem_singleton_iff.mp ht]

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
  (hu : let _instSceneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _instSceneOrder : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hb : Measurable b)
  (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
  (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
  (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
  (m : Measure E) [m.IsAddHaarMeasure]
  (hdim : 2 ≤ Module.finrank ℝ E)

include hF hcomplete hu ha hinj horder hb hinv hη₀reg hη₁reg hdim

/-- Both actual coordinate populations are diffuse because they reconstruct
the normalized restrictions of the original diffuse physical populations. -/
theorem nullSingletonClass_sceneLaws
    (hchart₀ : ∀ old : M, (η₀.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hchart₁ : ∀ old : M, (η₁.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    NullSingletonClass (D.sceneLaw η₀ i L) ∧
      NullSingletonClass (D.sceneLaw η₁ i L) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  have : NullSingletonClass η₀ := nullSingletonClass_of_chartwise_ac m η₀ hdim hchart₀
  have : NullSingletonClass η₁ := nullSingletonClass_of_chartwise_ac m η₁ hdim hchart₁
  obtain ⟨hs, ht⟩ := D.sceneLaw_physical_recovery hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg i hL hsub
  have hp := measurable_populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed
  have hsrc : NullSingletonClass ((D.sceneLaw η₀ i L).map
      (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed)) := by
    rw [hs]
    exact nullSingletonClass_normalizedFiniteLaw _
  have htrg : NullSingletonClass ((D.sceneLaw η₁ i L).map
      (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed)) := by
    rw [ht]
    exact nullSingletonClass_normalizedFiniteLaw _
  exact ⟨nullSingletonClass_of_physical_map _ _ hp,
    nullSingletonClass_of_physical_map _ _ hp⟩

/-- Original scaled slack differences are atomless on the actual normalized
cell source law, with no uniform spatial-law premise. -/
theorem nullSingletonClass_sceneLaw_scaled_distanceSlack_sub
    (hchart₀ : ∀ old : M, (η₀.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    (φ : M → ℝ) {k : ℝ} (hk : k ≠ 0) {y z : M} (hyz : y ≠ z) :
    let _instSceneSlackMetric : MetricSpace M := F.metricSpace
    NullSingletonClass ((D.sceneLaw η₀ i L).map (fun s ↦
      k * (dist (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s) y -
        φ y + φ (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s)) -
      k * (dist (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s) z -
        φ z + φ (populationSeedPhysicalMap
          (P (D.continuous.coefficient i).seedIndex).seed s)))) := by
  exact nullSingletonClass_scene_scaled_distanceSlack_sub hF m η₀ hdim hchart₀ hcomplete
    (a ⁻¹' L) (D.sceneLaw η₀ i L)
    (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed)
    (measurable_populationSeedPhysicalMap _)
    (D.sceneLaw_physical_recovery hF hcomplete hu ha hinj horder hb hinv
      hη₀reg hη₁reg i hL hsub).1 φ hk hyz

/-- Finite iid targets from the actual scene law reconstruct almost surely to
distinct physical points sampled from the original normalized target cell. -/
theorem ae_injective_physical_scene_targets
    (hchart₁ : ∀ old : M, (η₁.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) (hmass : 0 < lambda.real L)
    (n : ℕ) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ D.sceneLaw η₁ i L),
      Injective (fun j ↦
        populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed (y j)) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  let ν := normalizedFiniteLaw (η₁.restrict (a ⁻¹' L))
  let physical := populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed
  have hp : Measurable physical := measurable_populationSeedPhysicalMap _
  have hrec : (D.sceneLaw η₁ i L).map physical = ν :=
    (D.sceneLaw_physical_recovery hF hcomplete hu ha hinj horder hb hinv
      hη₀reg hη₁reg i hL hsub).2
  have : IsProbabilityMeasure (D.sceneLaw η₁ i L) :=
    (D.sceneLaw_probability hF hcomplete hu ha hinj i hL hsub hmass).2
  have : IsProbabilityMeasure ν := by
    rw [← hrec]
    exact Measure.isProbabilityMeasure_map hp.aemeasurable
  have : NullSingletonClass η₁ := nullSingletonClass_of_chartwise_ac m η₁ hdim hchart₁
  have : NullSingletonClass ν := nullSingletonClass_normalizedFiniteLaw _
  have hpres : MeasurePreserving physical (D.sceneLaw η₁ i L) ν := ⟨hp, hrec⟩
  exact (measurePreserving_pi (fun _ : Fin (n + 1) ↦ D.sceneLaw η₁ i L)
    (fun _ : Fin (n + 1) ↦ ν) (fun _ ↦ hpres)).quasiMeasurePreserving.ae
      (OTSelector.Probability.ae_injective_pi_of_nullSingletonClass ν)

/-- The actual random target cloud has atomless original base-cost differences
on the actual coordinate source probability law almost everywhere. -/
theorem ae_scene_target_cloud_base_atomlessness
    (hchart₀ : ∀ old : M, (η₀.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hchart₁ : ∀ old : M, (η₁.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) (hmass : 0 < lambda.real L)
    (n : ℕ) (φ : M → ℝ) {k : ℝ} (hk : k ≠ 0) :
    let _instSceneSlackMetric : MetricSpace M := F.metricSpace
    ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ D.sceneLaw η₁ i L),
      ∀ j l, j ≠ l → NullSingletonClass ((D.sceneLaw η₀ i L).map (fun s ↦
        k * (dist (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s)
            (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed (y j)) -
          φ (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed (y j)) +
          φ (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s)) -
        k * (dist (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s)
            (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed (y l)) -
          φ (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed (y l)) +
          φ (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s)))) := by
  let _instSceneSlackMetric : MetricSpace M := F.metricSpace
  filter_upwards [D.ae_injective_physical_scene_targets hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg m hdim hchart₁ i hL hsub hmass n] with y hy
  intro j l hjl
  exact D.nullSingletonClass_sceneLaw_scaled_distanceSlack_sub hF hcomplete hu ha hinj
    horder hb hinv hη₀reg hη₁reg m hdim hchart₀ i hL hsub φ hk (hy.ne hjl)

end PopulationHaarPressureCore
end OTSelector.Reconstruction
