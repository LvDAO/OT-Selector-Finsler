import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonproperExhaustion
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetNonproper

/-!
# Actual target-test escape errors for canonical compact cutoffs

The original compact source clock image and each compact target test produce
one genuine source compact exhaustion. The same global physical energy controls
the actual target-window escape rectangles, retaining both original population
losses and every realized restricted target column.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section TargetGeometry
variable {ι : Type*} [Fintype ι]

/-- Target compact-test escape from the genuine source exhaustion forces an
actual target-window long edge, using the unchanged source clock carrier. -/
theorem physicalScene_target_test_escape_exhaustion_le_longTail
    (π : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (W C : ℝ) {J : Set ℝ}
    (hf : ∀ x ∈ tsupport f, ‖x.1‖ ≤ |W|)
    (hJ : ∀ t ∈ J, ‖t‖ ≤ |C| + 1)
    (hclock : ∀ᵐ e ∂π, e.1.2 ∈ J) (n : ℕ) :
    π ((physicalSceneSpatialClockExhaustion W C n)ᶜ ×ˢ tsupport f) ≤
      π (physicalSceneTargetLongEdgeWindow (physicalSceneTestSpatialWindow f)
        (ENNReal.ofReal (((n : ℝ) + 1) ^ 2))) := by
  have hsub : (physicalSceneSpatialClockExhaustion (ι := ι) W C n)ᶜ ×ˢ tsupport f ⊆
      (physicalSceneSpatialClockCutoff (ι := ι) |W| (n + 1) J)ᶜ ×ˢ
        (physicalSceneTestSpatialWindow f ×ˢ (univ : Set ℝ)) := by
    intro e he
    exact ⟨fun h ↦ he.1 (physicalSceneSpatialClockCutoff_subset_exhaustion W C hJ n h),
      mem_image_of_mem Prod.fst he.2, mem_univ _⟩
  exact (measure_mono hsub).trans
    (physicalScene_target_escape_compact_le_longTail π (by
      rintro x ⟨p, hp, rfl⟩
      exact hf p hp) (by positivity) hclock)

end TargetGeometry

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

/-- Original true energy produces the actual nonproper escape errors of
canonical target compact tests, with the exhaustion and its constants constructed from
the compact target test and the unchanged original source clock carrier. -/
theorem exists_original_allocation_target_test_escape_bounds
    {A B : Set M} (hA : IsCompact A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0, ∀ (i : Fin D.haar.continuous.count)
      (f : C_c((Fin (finrank ℝ
        (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ, ℝ)),
    ∃ W clockBound : ℝ,
      ∀ (n : ℕ)
        (Aalloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        Aalloc z.1 z.2 j)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (Aalloc z)) →
      ∀ (H : Set M), MeasurableSet H → H ⊆ D.physicalCoreDomain i →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain : Set
        (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)),
      volume rootDomain = ENNReal.ofReal N → ∀ (m : ℕ) (C : ℝ≥0∞),
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let coord := D.scaledPhysicalBasisPosition i spatialScale
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict (H ×ˢ univ))
        coord u N z ((physicalSceneSpatialClockExhaustion W clockBound m)ᶜ ×ˢ tsupport f)
        ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (volume (physicalSceneTestSpatialWindow f) * (C / ENNReal.ofReal q)) /
        ENNReal.ofReal (((m : ℝ) + 1) ^ 2) +
      volume (physicalSceneTestSpatialWindow f) *
        (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
          C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_allocation_piece_targetLongTail_bound
    hF hcomplete hu ha hinj horder hA.measurableSet hB hμA hνB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro i f
  obtain ⟨W, clockBound, hf, hJ⟩ := exists_physicalScene_compact_test_clock_bounds f
    (hA.image hu.continuous)
  refine ⟨W, clockBound, ?_⟩
  intro n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN rootDomain hD m C henergy
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
    (fun z ↦ z.1) (fun z ↦ z.2) hfeas hA.measurableSet hB hμA hYB
  have hpoint : ∀ᵐ w ∂Penv, ∀ z,
      physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
        ((physicalSceneSpatialClockExhaustion W clockBound m)ᶜ ×ˢ tsupport f) ≤
      physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
        (physicalSceneTargetLongEdgeWindow (physicalSceneTestSpatialWindow f)
          (ENNReal.ofReal (((m : ℝ) + 1) ^ 2))) := by
    filter_upwards [hcarried] with w hw z
    exact physicalScene_target_test_escape_exhaustion_le_longTail _ f W clockBound hf hJ
      (ae_physicalSceneRootedPlan_source_clock (Γ w) coord hcoord u hu.continuous.measurable
        (hA.image hu.continuous).measurableSet
        (hw.mono fun p hp ↦ mem_image_of_mem u hp.1) H N z) m
  have hU := isCompact_physicalSceneTestSpatialWindow f
  exact (lintegral_mono_ae (hpoint.mono fun _ hw ↦ lintegral_mono hw)).trans
    (hb i n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN rootDomain _ hD
      hU.measurableSet hU.measure_ne_top (ENNReal.ofReal (((m : ℝ) + 1) ^ 2))
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top C henergy)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
