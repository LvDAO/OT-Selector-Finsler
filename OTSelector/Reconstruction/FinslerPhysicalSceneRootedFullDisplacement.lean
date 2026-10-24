import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonNearMass
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedDisplacement

/-!
# Full original source-core long-edge tails

The source restriction of the same global physical allocation is covered by its
genuine masked near event and the complete original non-near complement. Actual
global energy controls both terms, leaving only the explicitly bounded original
population losses. The sampled target columns are retained as realized.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section RootedCover
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

/-- Actual physical event covers remain measure covers after the same rooted
observation; the second event can be read on a larger rooted window. -/
theorem physicalSceneRootedPlan_event_cover_le
    (Γ : Measure (X × X)) (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock) (N : ℝ) (z : ι → ℝ)
    {S S₀ S₁ : Set (X × X)} (hcover : S ⊆ S₀ ∪ S₁)
    {T T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hT : MeasurableSet T) (hT₁ : MeasurableSet T₁) (hsub : T ⊆ T₁) :
    physicalSceneRootedPlan (Γ.restrict S) coord clock N z T ≤
      physicalSceneRootedPlan (Γ.restrict S₀) coord clock N z T +
      physicalSceneRootedPlan (Γ.restrict S₁) coord clock N z T₁ := by
  let f := physicalSceneRootedObservation coord clock z
  have hf : Measurable f := measurable_physicalSceneRootedObservation coord hcoord clock hclock z
  have hμ : Γ.restrict S ≤ Γ.restrict S₀ + Γ.restrict S₁ :=
    (Measure.restrict_mono hcover le_rfl).trans (Measure.restrict_union_le S₀ S₁)
  have hm : (Γ.restrict S) (f ⁻¹' T) ≤
      (Γ.restrict S₀) (f ⁻¹' T) + (Γ.restrict S₁) (f ⁻¹' T₁) := by
    exact (hμ (f ⁻¹' T)).trans (add_le_add le_rfl (measure_mono (preimage_mono hsub)))
  change ENNReal.ofReal N * ((Γ.restrict S).map f) T ≤
    ENNReal.ofReal N * ((Γ.restrict S₀).map f) T +
    ENNReal.ofReal N * ((Γ.restrict S₁).map f) T₁
  rw [Measure.map_apply hf hT, Measure.map_apply hf hT, Measure.map_apply hf hT₁]
  simpa only [mul_add] using mul_le_mul_right hm (ENNReal.ofReal N)

/-- The actual event cover passes through both the original environment and
the Haar root integral, retaining both explicit physical event restrictions. -/
theorem lintegral_physicalSceneRootedPlan_event_cover_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Penv : Measure Ω) (Γ : Ω → Measure (X × X)) [∀ w, IsFiniteMeasure (Γ w)]
    (hΓ : Measurable Γ)
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock) (N : ℝ) (hN : 0 < N)
    (rootDomain : Set (ι → ℝ)) (hD : volume rootDomain = ENNReal.ofReal N)
    {S S₀ S₁ : Set (X × X)} (hcover : S ⊆ S₀ ∪ S₁)
    (hS₀ : MeasurableSet S₀)
    {T T₁ : Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))}
    (hT : MeasurableSet T) (hT₁ : MeasurableSet T₁) (hsub : T ⊆ T₁) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict S) coord clock N z T
      ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict S₀) coord clock N z T
      ∂cavityRootMeasure volume rootDomain N ∂Penv) +
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict S₁) coord clock N z T₁
      ∂cavityRootMeasure volume rootDomain N ∂Penv) := by
  have : IsProbabilityMeasure (cavityRootMeasure volume rootDomain N) :=
    isProbabilityMeasure_cavityRootMeasure volume rootDomain N hN hD
  have hΓ₀ : Measurable (fun w ↦ (Γ w).restrict S₀) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simp only [Measure.restrict_apply hV]
    exact (Measure.measurable_coe (hV.inter hS₀)).comp hΓ
  have h₀ := (Measure.measurable_coe hT).comp
    (measurable_joint_physicalSceneRootedPlan _ hΓ₀ coord hcoord clock hclock N)
  calc
    _ ≤ ∫⁻ w, ∫⁻ z,
        physicalSceneRootedPlan ((Γ w).restrict S₀) coord clock N z T +
        physicalSceneRootedPlan ((Γ w).restrict S₁) coord clock N z T₁
        ∂cavityRootMeasure volume rootDomain N ∂Penv :=
      lintegral_mono fun w ↦ lintegral_mono fun z ↦
        physicalSceneRootedPlan_event_cover_le (Γ w) coord hcoord clock hclock N z
          hcover hT hT₁ hsub
    _ = ∫⁻ w,
        (∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict S₀) coord clock N z T
          ∂cavityRootMeasure volume rootDomain N) +
        (∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict S₁) coord clock N z T₁
          ∂cavityRootMeasure volume rootDomain N) ∂Penv := by
      apply lintegral_congr
      intro w
      exact lintegral_add_left
        (h₀.comp (measurable_const.prodMk measurable_id)) _
    _ = _ := lintegral_add_left h₀.lintegral_prod_right' _

end RootedCover

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

/-- A source already in one actual core cannot belong to another core's near
event. Its full physical restriction is covered by its own near event and the
actual global complement of all near events. -/
theorem piece_source_subset_near_union_global_nonNear
    (i : Fin D.haar.continuous.count) {H : Set M} (hH : H ⊆ D.physicalCoreDomain i)
    (A B : Set M) (radius : ℝ) :
    (A ×ˢ B) ∩ (H ×ˢ univ) ⊆
      (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)) ∪
      (((A ×ˢ B) \ ⋃ j, D.nearDisplacementEvent j radius) ∩ (H ×ˢ univ)) := by
  classical
  intro p hp
  by_cases hn : p ∈ ⋃ j, D.nearDisplacementEvent j radius
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    have hij : i = j := by
      by_contra h
      exact Set.disjoint_left.mp (D.haar.continuous.disjoint h) (hH hp.2.1).2.1 hj.1
    subst j
    exact Or.inl ⟨hj, hp.2⟩
  · exact Or.inr ⟨⟨hp.1, hn⟩, hp.2⟩

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- Every actual rooted long edge from a retained physical source core is
charged either to the genuine near-event energy tail or the actual non-near
complement. No carrier or scalar-screen exception is dropped. -/
theorem rooted_piece_longTail_le_near_add_global_nonNear
    (i : Fin D.haar.continuous.count) (Γ : Measure (M × M))
    {H : Set M} (hH : H ⊆ D.physicalCoreDomain i) (A B : Set M)
    (radius spatialScale N : ℝ)
    (z : Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)
    (U : Set (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ))
    (hU : MeasurableSet U) (threshold : ℝ≥0∞) :
    let coord := D.scaledPhysicalBasisPosition i spatialScale
    physicalSceneRootedPlan (Γ.restrict ((A ×ˢ B) ∩ (H ×ˢ univ))) coord u N z
      (physicalSceneLongEdgeWindow U threshold) ≤
    physicalSceneRootedPlan (Γ.restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)))
      coord u N z (physicalSceneLongEdgeWindow U threshold) +
    physicalSceneRootedPlan
      (Γ.restrict (((A ×ˢ B) \ ⋃ j, D.nearDisplacementEvent j radius) ∩ (H ×ˢ univ)))
      coord u N z {e | e.1.1 ∈ U} := by
  let _inst : MetricSpace M := F.metricSpace
  exact physicalSceneRootedPlan_event_cover_le Γ _
    (D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale)
    u hu.continuous.measurable N z (D.piece_source_subset_near_union_global_nonNear i hH A B radius)
    (measurableSet_physicalSceneLongEdgeWindow hU threshold)
    (hU.preimage measurable_fst.fst) (fun _ hp ↦ hp.1)

variable (horder : let _inst : MetricSpace M := F.metricSpace
  ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
    (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
include horder

/-- A full original physical source-core restriction has an actual rooted long
edge tail bounded by inverse squared-displacement threshold, the two original
population losses, and a vanishing true energy/slack-gap term. -/
theorem exists_original_piece_full_longTail_bound
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
        (physicalSceneLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (volume U * (C / ENNReal.ofReal q)) / threshold +
      volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, radius, hradius, hnear⟩ :=
    D.exists_uniform_rooted_nearDisplacement_expected_tail hF hcomplete hu ha hinj
  obtain ⟨c, hc, hbad⟩ := D.exists_original_nonNear_rooted_bound hF hcomplete hu ha hinj horder
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
    (measurableSet_physicalSceneLongEdgeWindow hU threshold)
    (hU.preimage measurable_fst.fst) (fun _ hp ↦ hp.1)
  exact hcover.trans (add_le_add
    (hnear i _ Penv Γ H hH spatialScale N hN rootDomain U hU hUf threshold ht0 htt C henergy)
    (hbad n Aalloc halloc hfeas (spatialScale ^ 2) (sq_pos_of_pos hsp) C henergy
      _ coord hcoord H N hN rootDomain U hU hUf))

/-- A full original physical source-core restriction has an actual rooted long
edge tail bounded by inverse squared-displacement threshold, the two original
population losses, and a vanishing true energy/slack-gap term. -/
theorem exists_original_allocation_piece_longTail_bound
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
        (physicalSceneLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      (volume U * (C / ENNReal.ofReal q)) / threshold +
      volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, c, hc, hb⟩ := D.exists_original_piece_full_longTail_bound
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
      (physicalSceneLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N ∂Penv) =
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict ((A ×ˢ B) ∩ (H ×ˢ univ)))
      (D.scaledPhysicalBasisPosition i spatialScale) u N z
      (physicalSceneLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N ∂Penv) := by
    apply lintegral_congr_ae
    filter_upwards [heq] with w hw
    rw [hw]
  exact hint.trans_le hbound

end PopulationLocalPressureCore
end OTSelector.Reconstruction
