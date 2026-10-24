import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetDisplacement
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonproperCutoff

/-!
# Full actual target-window tails and compact source cutoffs

The same physical source-core restriction is covered by its original near
piece and the full global non-near complement.  Its original global energy and
population losses control target-window long edges.  The unchanged original
compact source clock carrier then gives genuine compact source escape bounds.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section ClockCarrier
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

omit [Fintype ι] in
/-- The unchanged source clock carrier survives the same original source
restriction and the actual rooted observation. -/
theorem ae_physicalSceneRootedPlan_source_clock
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {J : Set ℝ} (hJ : MeasurableSet J)
    (hclock : ∀ᵐ p ∂Γ, u p.1 ∈ J) (H : Set M) (N : ℝ) (z : ι → ℝ) :
    ∀ᵐ e ∂physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z, e.1.2 ∈ J := by
  unfold physicalSceneRootedPlan
  apply Measure.ae_smul_measure
  apply (ae_map_iff
    (measurable_physicalSceneRootedObservation coord hcoord u hu z).aemeasurable
    (hJ.preimage measurable_fst.snd)).mpr
  exact ae_restrict_of_ae hclock

/-- For the actual same physical source-restricted plan, escape of its source
from a compact cutoff over a bounded target window forces a long spatial edge. -/
theorem physicalSceneRootedPlan_target_escape_compact_le_full_longTail
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {J : Set ℝ} (hJ : MeasurableSet J)
    (hclock : ∀ᵐ p ∂Γ, u p.1 ∈ J) (H : Set M) (N : ℝ) (z : ι → ℝ)
    {U : Set (ι → ℝ)} {B R : ℝ} (hU : ∀ x ∈ U, ‖x‖ ≤ B) (hR : 0 ≤ R) :
    physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      ((physicalSceneSpatialClockCutoff B R J)ᶜ ×ˢ (U ×ˢ univ)) ≤
    physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      (physicalSceneTargetLongEdgeWindow U (ENNReal.ofReal (R ^ 2))) :=
  physicalScene_target_escape_compact_le_longTail _ hU hR
    (ae_physicalSceneRootedPlan_source_clock Γ coord hcoord u hu hJ hclock H N z)

end ClockCarrier

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
include hF hcomplete hu ha hinj

/-- The original physical cover charges a target-window long edge either to
its genuine forward near event or to the full original non-near complement. -/
theorem rooted_piece_targetLongTail_le_near_add_global_nonNear
    (i : Fin D.haar.continuous.count) (Γ : Measure (M × M))
    {H : Set M} (hH : H ⊆ D.physicalCoreDomain i) (A B : Set M)
    (radius spatialScale N : ℝ)
    (z : Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)
    (U : Set (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ))
    (hU : MeasurableSet U) (threshold : ℝ≥0∞) :
    let coord := D.scaledPhysicalBasisPosition i spatialScale
    physicalSceneRootedPlan (Γ.restrict ((A ×ˢ B) ∩ (H ×ˢ univ))) coord u N z
      (physicalSceneTargetLongEdgeWindow U threshold) ≤
    physicalSceneRootedPlan (Γ.restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)))
      coord u N z (physicalSceneTargetLongEdgeWindow U threshold) +
    physicalSceneRootedPlan
      (Γ.restrict (((A ×ˢ B) \ ⋃ j, D.nearDisplacementEvent j radius) ∩ (H ×ˢ univ)))
      coord u N z {e | e.2.1 ∈ U} := by
  let _inst : MetricSpace M := F.metricSpace
  exact physicalSceneRootedPlan_event_cover_le Γ _
    (D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale)
    u hu.continuous.measurable N z (D.piece_source_subset_near_union_global_nonNear i hH A B radius)
    (measurableSet_physicalSceneTargetLongEdgeWindow hU threshold)
    (hU.preimage measurable_snd.fst) (fun _ hp ↦ hp.1)

variable (horder : let _inst : MetricSpace M := F.metricSpace
  ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
    (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
include horder

/-- The original global energy and the original population losses bound every
full target-window long-edge tail of the same physical source-core restriction. -/
theorem exists_original_piece_full_targetLongTail_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
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
      ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let coord := D.scaledPhysicalBasisPosition i spatialScale
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict
          ((A ×ˢ B) ∩ (H ×ˢ univ))) coord u N z
        (physicalSceneTargetLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (volume U * (C / ENNReal.ofReal q)) / threshold +
      volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, radius, hradius, hnear⟩ :=
    D.exists_uniform_rooted_nearDisplacement_both_expected_tails hF hcomplete hu ha hinj
  obtain ⟨c, hc, hbad⟩ := D.exists_original_nonNear_mass_bound hF hcomplete hu ha hinj horder
    hA hB hgap hdist hradius hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro i n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN
    rootDomain U hD hU hUf threshold ht0 htt C henergy
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
  let coord := D.scaledPhysicalBasisPosition i spatialScale
  have hcoord := D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale
  have hΓ : Measurable Γ := measurable_physicalSceneGlobalAllocationFamily μ Aalloc halloc
    (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  have hcover := lintegral_physicalSceneRootedPlan_event_cover_le Penv Γ hΓ coord hcoord
    u hu.continuous.measurable N hN rootDomain hD
    (D.piece_source_subset_near_union_global_nonNear i hHsub A B radius)
    ((D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius).inter
      (hH.prod MeasurableSet.univ))
    (measurableSet_physicalSceneTargetLongEdgeWindow hU threshold)
    (hU.preimage measurable_snd.fst) (fun _ hp ↦ hp.1)
  have hnonNear := lintegral_event_restricted_rooted_targetWindow_expected_le_of_mass
    Penv Γ coord hcoord u hu.continuous.measurable N hN rootDomain U hU hUf
    ((A ×ˢ B) \ ⋃ j, D.nearDisplacementEvent j radius) H _
    (hbad n Aalloc halloc hfeas (spatialScale ^ 2) (sq_pos_of_pos hsp) C henergy)
  exact hcover.trans (add_le_add
    (hnear i _ Penv Γ H hH spatialScale N hN rootDomain U hU hUf threshold ht0 htt C henergy).2
    hnonNear)

/-- A full original physical source-core restriction has an actual rooted long
edge tail bounded by inverse squared-displacement threshold, the two original
population losses, and a vanishing true energy/slack-gap term. -/
theorem exists_original_allocation_piece_targetLongTail_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
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
      ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      let coord := D.scaledPhysicalBasisPosition i spatialScale
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict (H ×ˢ univ)) coord u N z
        (physicalSceneTargetLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (volume U * (C / ENNReal.ofReal q)) / threshold +
      volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_piece_full_targetLongTail_bound
    hF hcomplete hu ha hinj horder hA hB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro i n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN
    rootDomain U hD hU hUf threshold ht0 htt C henergy
  have hbound := hb i n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN
    rootDomain U hD hU hUf threshold ht0 htt C henergy
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
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
  have heq : ∀ᵐ w ∂Penv,
      (Γ w).restrict ((A ×ˢ B) ∩ (H ×ˢ univ)) = (Γ w).restrict (H ×ˢ univ) := by
    filter_upwards [hcarried] with w hw
    have hs : (Γ w).restrict (A ×ˢ B) = Γ w :=
      Measure.restrict_eq_self_of_ae_mem (show ∀ᵐ p ∂Γ w, p ∈ A ×ˢ B from hw)
    rw [inter_comm, ← Measure.restrict_restrict (hH.prod MeasurableSet.univ), hs]
  have hint : (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ))
      (D.scaledPhysicalBasisPosition i spatialScale) u N z
      (physicalSceneTargetLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N ∂Penv) =
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict ((A ×ˢ B) ∩ (H ×ˢ univ)))
      (D.scaledPhysicalBasisPosition i spatialScale) u N z
      (physicalSceneTargetLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N ∂Penv) := by
    apply lintegral_congr_ae
    filter_upwards [heq] with w hw
    rw [hw]
  exact hint.trans_le hbound

/-- A full original physical source-core restriction has an actual rooted long
edge tail bounded by inverse squared-displacement threshold, the two original
population losses, and a vanishing true energy/slack-gap term. -/
theorem exists_original_allocation_piece_target_nonproper_tail_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAcompact : IsCompact A)
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
        ((physicalSceneSpatialClockCutoff W R (u '' A))ᶜ ×ˢ (U ×ˢ univ)) ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (volume U * (C / ENNReal.ofReal q)) / ENNReal.ofReal (R ^ 2) +
      volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_allocation_piece_targetLongTail_bound
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
        ((physicalSceneSpatialClockCutoff W R (u '' A))ᶜ ×ˢ (U ×ˢ univ)) ≤
      physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
        (physicalSceneTargetLongEdgeWindow U (ENNReal.ofReal (R ^ 2))) := by
    filter_upwards [hcarried] with w hw z
    exact physicalSceneRootedPlan_target_escape_compact_le_full_longTail (Γ w) coord hcoord
      u hu.continuous.measurable (hAcompact.image hu.continuous).measurableSet
      (hw.mono fun p hp ↦ mem_image_of_mem u hp.1) H N z hUW hR.le
  exact (lintegral_mono_ae (hpoint.mono fun w hw ↦ lintegral_mono hw)).trans
    (hb i n Aalloc halloc hfeas H hH hHsub spatialScale N hsp hN rootDomain U hD hU hUf
      (ENNReal.ofReal (R ^ 2)) (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hR))
      ENNReal.ofReal_ne_top C henergy)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
