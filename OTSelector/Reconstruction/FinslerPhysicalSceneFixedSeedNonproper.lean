import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedFullTail
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonproperCutoff

/-!
# Full original fixed-seed nonproper target tails

The original seed source and original coordinate frame remain fixed while an
auxiliary accuracy core bounds target escape. Its number of pieces multiplies
only the vanishing inverse-square radius term; population loss is paid once.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal
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

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

variable (horder : let _inst : MetricSpace M := F.metricSpace
  ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
    (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
include horder

/-- The entire unchanged original seed source has an actual expected compact
target escape bound, with original population loss paid once. -/
theorem exists_original_fixed_seed_allocation_nonproper_tail_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBcompact : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0,
      ∀ (j n : ℕ)
        (Aalloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        Aalloc z.1 z.2 j)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (Aalloc z)) →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set
        (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      volume rootDomain = ENNReal.ofReal N → MeasurableSet U → volume U ≠ ⊤ →
      ∀ (R W : ℝ), 0 < R → (∀ x ∈ U, ‖x‖ ≤ W) → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict (H ×ˢ univ)) coord u N z
        ((U ×ˢ univ) ×ˢ (physicalSceneSpatialClockCutoff W R (u '' B))ᶜ) ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (D.haar.continuous.count : ℝ≥0∞) *
        ((volume U * (C / ENNReal.ofReal q)) / ENNReal.ofReal (R ^ 2)) +
      volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_fixed_seed_both_full_longTail_bounds
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro j n Aalloc halloc hfeas spatialScale N hsp hN
    rootDomain U hD hU hUf R W hR hUW C henergy
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
  have hcoord : Measurable coord := measurable_physicalSceneOriginalSeedScaledPosition
    hF hcomplete hu ha hinj j spatialScale
  have hYB : ∀ᵐ w ∂Penv, ∀ j, w.1 j ∈ B := by
    apply ae_all_iff.mpr
    intro j
    have hm : Measurable (fun w : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) ↦ w.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    apply ae_of_ae_map (p := fun y : M ↦ y ∈ B) hm.aemeasurable
    rw [show Penv.map (fun w ↦ w.1 j) = ν from
      physicalSceneOriginalDirichlet_target_law ν n j]
    exact hνB
  have hcarried := ae_physicalSceneGlobalAllocationFamily_carried Penv μ Aalloc
    (fun z ↦ z.1) (fun z ↦ z.2) hfeas hA hB hμA hYB
  have hpoint : ∀ᵐ w ∂Penv, ∀ z,
      physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
        ((U ×ˢ univ) ×ˢ (physicalSceneSpatialClockCutoff W R (u '' B))ᶜ) ≤
      physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
        (physicalSceneLongEdgeWindow U (ENNReal.ofReal (R ^ 2))) := by
    filter_upwards [hcarried] with w hw z
    exact physicalSceneRootedPlan_escape_compact_le_full_longTail (Γ w) coord hcoord
      u hu.continuous.measurable (hBcompact.image hu.continuous).measurableSet
      (hw.mono fun p hp ↦ mem_image_of_mem u hp.2) H N z hUW hR.le
  exact (lintegral_mono_ae (hpoint.mono fun w hw ↦ lintegral_mono hw)).trans
    (hb j n Aalloc halloc hfeas spatialScale N hsp hN rootDomain U hD hU hUf
      (ENNReal.ofReal (R ^ 2)) (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hR))
      ENNReal.ofReal_ne_top C henergy).1

end PopulationLocalPressureCore
end OTSelector.Reconstruction
