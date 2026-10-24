import OTSelector.Reconstruction.OriginalIIDFixedSeedFullTail
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals

/-!
# Full energy tails in one fixed original seed scene

The actual source restriction and original seed coordinates stay fixed across
all auxiliary core accuracies. A finite cover by near pieces, read in that same
frame, and the complete non-near complement give both full displacement tails.
The auxiliary core appears only through finite numerical constants and its
explicit original population losses.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal BigOperators
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
  [IsFiniteMeasure lambda] {μ ν : Measure M}
  [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞} [∀ j, SigmaFinite (κ j)]

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _inst : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
include hF hcomplete hu ha hinj horder

/-- Both full rooted displacement tails in one fixed original seed scene
are bounded using any auxiliary accuracy core. Only the numerical constants and
population losses depend on that auxiliary core; the actual scene stays fixed. -/
theorem exists_original_fixed_seed_both_full_longTail_bounds
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0, ∀ (j n : ℕ)
      (Aalloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ l, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        Aalloc z.1 z.2 l)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (Aalloc z)) →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      volume rootDomain = ENNReal.ofReal N → MeasurableSet U → volume U ≠ ⊤ →
      ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      let bound := (D.haar.continuous.count : ℝ≥0∞) *
        ((volume U * (C / ENNReal.ofReal q)) / threshold) +
        volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
          C / ENNReal.ofReal (spatialScale ^ 2 * c))
      ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict (H ×ˢ univ))
        coord u N z (physicalSceneLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ bound) ∧
      ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict (H ×ˢ univ))
        coord u N z (physicalSceneTargetLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ bound) := by
  obtain ⟨q, hq, c, hc, hbound⟩ :=
    D.exists_mean_coupling_fixed_seed_both_full_longTail_bounds
      hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro j n Aalloc halloc hfeas
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
  have hΓ : Measurable Γ := measurable_physicalSceneGlobalAllocationFamily μ Aalloc halloc
    (fun z ↦ z.1) (fun l ↦ (measurable_pi_apply l).comp measurable_fst)
  have hs : (Penv.bind Γ).map Prod.fst = μ := by
    apply Measure.ext_of_lintegral μ
    intro f hf
    rw [lintegral_map hf measurable_fst]
    exact (Measure.lintegral_bind hΓ.aemeasurable
      (hf.comp measurable_fst).aemeasurable).trans
        (lintegral_physicalSceneGlobalAllocationFamily_source_eq_population
          μ ν n Aalloc hfeas f hf)
  have ht : (Penv.bind Γ).map Prod.snd = ν := by
    apply Measure.ext_of_lintegral ν
    intro f hf
    rw [lintegral_map hf measurable_snd]
    exact (Measure.lintegral_bind hΓ.aemeasurable
      (hf.comp measurable_snd).aemeasurable).trans
        (lintegral_physicalSceneGlobalAllocationFamily_target_eq_population
          μ ν n Aalloc hfeas f hf)
  exact hbound j _ Penv Γ hΓ ⟨hs, ht⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
