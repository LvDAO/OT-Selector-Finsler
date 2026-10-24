import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNearComplement
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals

/-!
# Original global non-near mass and rooted windows

The same actual target-times-Dirichlet allocation pays for every non-near edge.
Its two original population complements and true global energy give the whole
mass bound, with every actual random restricted target column unchanged.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section SourceSet
variable {M : Type*} [MeasurableSpace M]

/-- Actual global feasibility gives the exact original mass of each source set. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_sourceSet_eq
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (A : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (A z)) {K : Set M} (hK : MeasurableSet K) :
    (∫⁻ z, physicalSceneGlobalAllocationFamily μ A (fun z ↦ z.1) z (K ×ˢ univ)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) = μ K := by
  have h := lintegral_physicalSceneGlobalAllocationFamily_source_eq_population μ ν n A hfeas
    (K.indicator (fun _ ↦ 1)) (measurable_const.indicator hK)
  have hp (Γ : Measure (M × M)) :
      (∫⁻ e, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) e.1 ∂Γ) = Γ (K ×ˢ univ) := by
    calc
      _ = ∫⁻ e, (K ×ˢ univ).indicator (fun _ ↦ (1 : ℝ≥0∞)) e ∂Γ := by
        apply lintegral_congr
        intro e
        by_cases he : e.1 ∈ K <;> simp [he]
      _ = _ := lintegral_indicator_one (hK.prod MeasurableSet.univ)
  calc
    _ = ∫⁻ z, ∫⁻ e, K.indicator (fun _ ↦ (1 : ℝ≥0∞)) e.1
        ∂physicalSceneGlobalAllocationFamily μ A (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) :=
      lintegral_congr fun _ ↦ (hp _).symm
    _ = _ := h
    _ = _ := lintegral_indicator_one hK

end SourceSet

/-- A bound on the expected mass of an actual physical event also bounds its
Haar-rooted mass in every finite-volume source window. -/
theorem lintegral_event_restricted_rooted_sourceWindow_expected_le_of_mass
    {ι X Ω : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Ω]
    (Penv : Measure Ω) (Γ : Ω → Measure (X × X)) [∀ w, IsFiniteMeasure (Γ w)]
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : X → ℝ) (hclock : Measurable clock)
    (N : ℝ) (hN : 0 < N) (rootDomain U : Set (ι → ℝ))
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (Q : Set (X × X)) (H : Set X) (C : ℝ≥0∞)
    (hmass : (∫⁻ w, Γ w Q ∂Penv) ≤ C) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (Q ∩ (H ×ˢ univ)))
      coord clock N z {e | e.1.1 ∈ U}
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤ volume U * C := by
  calc
    _ ≤ ∫⁻ w, volume U * Γ w Q ∂Penv := by
      apply lintegral_mono
      intro w
      apply (lintegral_physicalSceneRootedPlan_sourceWindow_le
        ((Γ w).restrict (Q ∩ (H ×ˢ univ))) coord hcoord clock hclock
        N hN rootDomain U hU).trans
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul_right (measure_mono inter_subset_left) _
    _ = volume U * ∫⁻ w, Γ w Q ∂Penv := lintegral_const_mul' _ _ hUf
    _ ≤ _ := mul_le_mul_right hmass _

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

/-- The same original feasible global allocation pays for every non-near edge:
only the two actual physical population complements and the vanishing true
energy/slack-gap term remain. Its random restricted columns are unchanged. -/
theorem exists_original_nonNear_mass_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (n : ℕ)
      (Aalloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        Aalloc z.1 z.2 j)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (Aalloc z)) →
      ∀ (scale : ℝ), 0 < scale → ∀ C : ℝ≥0∞,
      (∫⁻ z, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      (∫⁻ z, physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) z
        ((A ×ˢ B) \ ⋃ i, D.nearDisplacementEvent i radius)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
        C / ENNReal.ofReal (scale * c) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hb⟩ := D.exists_retainedNearComplement_gap hF hcomplete hu ha hinj horder
    hgap hdist hradius hwindow
  refine ⟨c, hc, ?_⟩
  intro n Aalloc halloc hfeas scale hscale C henergy
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)
  let K := ⋃ i, D.physicalCoreDomain i
  let Q := D.retainedNearComplementEvent A B radius
  have hK : MeasurableSet K := MeasurableSet.iUnion fun i ↦
    D.measurableSet_physicalCoreDomain hF hcomplete hu ha i
  have hQ : MeasurableSet Q :=
    D.measurableSet_retainedNearComplementEvent hF hcomplete hu ha hinj hA hB radius
  have hΓ : Measurable Γ := measurable_physicalSceneGlobalAllocationFamily μ Aalloc halloc
    (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  have hcover : ((A ×ˢ B) \ ⋃ i, D.nearDisplacementEvent i radius) ⊆
      (Kᶜ ×ˢ univ) ∪ (univ ×ˢ Kᶜ) ∪ Q := by
    intro p hp
    by_cases hx : p.1 ∈ K
    · by_cases hy : p.2 ∈ K
      · exact Or.inr ⟨⟨⟨hx, hy⟩, hp.1⟩, hp.2⟩
      · exact Or.inl (Or.inr ⟨mem_univ _, hy⟩)
    · exact Or.inl (Or.inl ⟨hx, mem_univ _⟩)
  have hbound (z) : Γ z ((A ×ˢ B) \ ⋃ i, D.nearDisplacementEvent i radius) ≤
      Γ z (Kᶜ ×ˢ univ) + Γ z (univ ×ˢ Kᶜ) + Γ z Q :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))
  have hsource := lintegral_physicalSceneGlobalAllocationFamily_sourceSet_eq μ ν n Aalloc hfeas hK.compl
  have htarget := lintegral_physicalSceneGlobalAllocationFamily_targetSet_eq μ ν n Aalloc hfeas hK.compl
  have hqenergy : (∫⁻ z, Γ z Q ∂Penv) ≤ C / ENNReal.ofReal (scale * c) := by
    calc
      _ ≤ ∫⁻ z, (∫⁻ p, ENNReal.ofReal (scale *
          ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ z) /
          ENNReal.ofReal (scale * c) ∂Penv :=
        lintegral_mono fun z ↦ measure_event_le_scaled_energy_of_gap (Γ z) hQ _ hc hscale hb
      _ = (∫⁻ z, ∫⁻ p, ENNReal.ofReal (scale *
          ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ z ∂Penv) /
          ENNReal.ofReal (scale * c) := by
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr
          (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hscale hc)))
      _ ≤ _ := ENNReal.div_le_div_right henergy _
  calc
    _ ≤ ∫⁻ z, Γ z (Kᶜ ×ˢ univ) + Γ z (univ ×ˢ Kᶜ) + Γ z Q ∂Penv := lintegral_mono hbound
    _ = (∫⁻ z, Γ z (Kᶜ ×ˢ univ) ∂Penv) + (∫⁻ z, Γ z (univ ×ˢ Kᶜ) ∂Penv) +
        ∫⁻ z, Γ z Q ∂Penv := by
      rw [lintegral_add_left, lintegral_add_left]
      · exact (Measure.measurable_coe (hK.compl.prod MeasurableSet.univ)).comp hΓ
      · exact ((Measure.measurable_coe (hK.compl.prod MeasurableSet.univ)).comp hΓ).add
          ((Measure.measurable_coe (MeasurableSet.univ.prod hK.compl)).comp hΓ)
    _ ≤ _ := by rw [hsource, htarget]; exact add_le_add le_rfl hqenergy

/-- The same original feasible global allocation pays for every non-near edge:
only the two actual physical population complements and the vanishing true
energy/slack-gap term remain. Its random restricted columns are unchanged. -/
theorem exists_original_nonNear_rooted_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (n : ℕ)
      (Aalloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        Aalloc z.1 z.2 j)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (Aalloc z)) →
      ∀ (scale : ℝ), 0 < scale → ∀ C : ℝ≥0∞,
      (∫⁻ z, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) z
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      ∀ (ι : Type*) [Fintype ι] (coord : M → (ι → ℝ)), Measurable coord →
      ∀ (H : Set M) (N : ℝ), 0 < N →
      ∀ (rootDomain U : Set (ι → ℝ)), MeasurableSet U → volume U ≠ ⊤ →
      (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan
        ((physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1) w).restrict
          (((A ×ˢ B) \ ⋃ i, D.nearDisplacementEvent i radius) ∩ (H ×ˢ univ)))
        coord u N z {e | e.1.1 ∈ U} ∂cavityRootMeasure volume rootDomain N
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
        C / ENNReal.ofReal (scale * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hb⟩ := D.exists_original_nonNear_mass_bound hF hcomplete hu ha hinj horder
    hA hB hgap hdist hradius hwindow
  refine ⟨c, hc, ?_⟩
  intro n Aalloc halloc hfeas scale hscale C henergy ι _ coord hcoord H N hN
    rootDomain U hU hUf
  exact lintegral_event_restricted_rooted_sourceWindow_expected_le_of_mass
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    (physicalSceneGlobalAllocationFamily μ Aalloc (fun z ↦ z.1)) coord hcoord u
    hu.continuous.measurable N hN rootDomain U hU hUf _ H _
    (hb n Aalloc halloc hfeas scale hscale C henergy)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
