import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonproperCutoff

/-!
# Actual original plans produce nonproper projection tail bounds

The same original target-times-Dirichlet global allocation is restricted only
in its actual physical source core. Its true global energy and the two explicit
original population losses control escape from compact target cutoffs. The
actual compact target clock image is included in each cutoff.
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

/-- A full original physical source-core restriction has an actual rooted long
edge tail bounded by inverse squared-displacement threshold, the two original
population losses, and a vanishing true energy/slack-gap term. -/
theorem exists_original_allocation_piece_nonproper_tail_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBcompact : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0,
      ∀ (i : Fin D.haar.continuous.count) (n : ℕ)
        (Aalloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        Aalloc z.1 z.2 j)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (Aalloc z)) →
      ∀ (H : Set M), MeasurableSet H → H ⊆ D.physicalCoreDomain i →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set
        (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)),
      volume rootDomain = ENNReal.ofReal N → MeasurableSet U → volume U ≠ ⊤ →
      ∀ (R W : ℝ), 0 < R → (∀ x ∈ U, ‖x‖ ≤ W) → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let coord := D.scaledPhysicalBasisPosition i spatialScale
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict (H ×ˢ univ)) coord u N z
        ((U ×ˢ univ) ×ˢ (physicalSceneSpatialClockCutoff W R (u '' B))ᶜ) ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (volume U * (C / ENNReal.ofReal q)) / ENNReal.ofReal (R ^ 2) +
      volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_allocation_piece_longTail_bound
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro i n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN
    rootDomain U hD hU hUf R W hR hUW C henergy
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
  let coord := D.scaledPhysicalBasisPosition i spatialScale
  have hcoord := D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale
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
    (hb i n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN rootDomain U hD hU hUf
      (ENNReal.ofReal (R ^ 2)) (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hR))
      ENNReal.ofReal_ne_top C henergy)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
