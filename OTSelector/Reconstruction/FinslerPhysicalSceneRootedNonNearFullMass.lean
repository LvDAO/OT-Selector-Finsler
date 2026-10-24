import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreWitnessPopulation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonNearMass

/-!
# Full actual near-event complements from the original population experiment

The original finite completed allocation is carried by its original source and
mean target populations. A mass estimate within that carrier therefore controls
the complete event complement. No realized target column vector is replaced.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {M : Type*} [MeasurableSpace M]

/-- Original source and mean target support identities remove the outside-carrier
mass when bounding the complete complement of a retained actual edge event. -/
theorem lintegral_physicalSceneGlobalAllocationFamily_event_compl_le_of_supported
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    (alloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (halloc : ∀ j, Measurable (fun z :
      (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦ alloc z.1 z.2 j))
    (hfeas : ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ w.2 (alloc w))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (E : Set (M × M)) (hE : MeasurableSet E) (C : ℝ≥0∞)
    (hb : (∫⁻ w, physicalSceneGlobalAllocationFamily μ alloc (fun w ↦ w.1) w
      ((A ×ˢ B) \ E)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C) :
    (∫⁻ w, physicalSceneGlobalAllocationFamily μ alloc (fun w ↦ w.1) w Eᶜ
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C := by
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let Γ := physicalSceneGlobalAllocationFamily μ alloc (fun w ↦ w.1)
  have hΓ : Measurable Γ := measurable_physicalSceneGlobalAllocationFamily μ alloc halloc
    (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  have houtside : (∫⁻ w, Γ w (A ×ˢ B)ᶜ ∂Penv) = 0 := by
    apply le_antisymm _ bot_le
    change (∫⁻ w, Γ w (A ×ˢ B)ᶜ ∂Penv) ≤ (0 : ℝ≥0∞)
    simpa only [Γ, Penv, hμA, hνB, add_zero] using
      lintegral_physicalSceneGlobalAllocationFamily_outside_product_le
        μ ν n alloc halloc hfeas A B hA hB
  have hcover : Eᶜ ⊆ ((A ×ˢ B) \ E) ∪ (A ×ˢ B)ᶜ := by
    intro e he
    by_cases hab : e ∈ A ×ˢ B
    · exact Or.inl ⟨hab, he⟩
    · exact Or.inr hab
  calc
    _ ≤ ∫⁻ w, Γ w ((A ×ˢ B) \ E) + Γ w (A ×ˢ B)ᶜ ∂Penv :=
      lintegral_mono fun w ↦ (measure_mono hcover).trans (measure_union_le _ _)
    _ = (∫⁻ w, Γ w ((A ×ˢ B) \ E) ∂Penv) + ∫⁻ w, Γ w (A ×ˢ B)ᶜ ∂Penv :=
      lintegral_add_left ((Measure.measurable_coe ((hA.prod hB).diff hE)).comp hΓ) _
    _ ≤ C := by rw [houtside, add_zero]; exact hb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] {μ ν : Measure M}
  [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞} [∀ j, SigmaFinite (κ j)]

/-- The original true-energy and union population losses control the COMPLETE
complement of the retained near event inside its unchanged physical carrier. -/
theorem PopulationLocalPressureCore.exists_original_fullNonNear_mass_bound
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (n : ℕ)
      (alloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ),
      (∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
        alloc z.1 z.2 j)) →
      (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ z.2 (alloc z)) →
      ∀ scale : ℝ, 0 < scale → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ alloc (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C →
      (∫⁻ w, physicalSceneGlobalAllocationFamily μ alloc (fun w ↦ w.1) w
        (((⋃ i, D.nearDisplacementEvent i radius) ∩ (A ×ˢ B))ᶜ)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
        C / ENNReal.ofReal (scale * c) := by
  obtain ⟨c, hc, hb⟩ := D.exists_original_nonNear_mass_bound hF hcomplete hu ha hinj horder
    hA hB hgap hdist hradius hwindow
  refine ⟨c, hc, ?_⟩
  intro n alloc halloc hfeas scale hscale C henergy
  have hnear : MeasurableSet (⋃ i, D.nearDisplacementEvent i radius) :=
    MeasurableSet.iUnion fun i ↦ D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius
  apply lintegral_physicalSceneGlobalAllocationFamily_event_compl_le_of_supported
    μ ν n alloc halloc hfeas A B hA hB hμA hνB _ (hnear.inter (hA.prod hB))
  have heq : (A ×ˢ B) \ ((⋃ i, D.nearDisplacementEvent i radius) ∩ (A ×ˢ B)) =
      (A ×ˢ B) \ ⋃ i, D.nearDisplacementEvent i radius := by
    ext e
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  simpa only [heq] using hb n alloc halloc hfeas scale hscale C henergy

end OTSelector.Reconstruction
