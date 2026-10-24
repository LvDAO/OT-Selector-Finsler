import OTSelector.Geometry.Finsler.DistanceLocalizationSupportBound
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNearComplement
import OTSelector.Reconstruction.OriginalIIDOptimalMeanPlan

/-!
# The original mean coupling pays for all non-near physical edges

The positive gap is the existing actual retained-core gap. Both discarded
masses are read from the same coupling's original population marginals.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

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

/-- Any coupling of the unchanged populations pays for its complete non-near
mass by their two actual core complements and its true scaled slack energy. -/
theorem exists_coupling_fullNonNear_mass_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (π : Measure (M × M)) [IsFiniteMeasure π],
      Vlasov.IsCoupling π μ ν → ∀ scale : ℝ, 0 < scale → ∀ C : ℝ≥0∞,
      (∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂π) ≤ C →
      π (((⋃ i, D.nearDisplacementEvent i radius) ∩ (A ×ˢ B))ᶜ) ≤
        μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
          C / ENNReal.ofReal (scale * c) := by
  obtain ⟨c, hc, hb⟩ := D.exists_retainedNearComplement_gap
    hF hcomplete hu ha hinj horder hgap hdist hradius hwindow
  refine ⟨c, hc, ?_⟩
  intro π _ hπ scale hscale C henergy
  let K := ⋃ i, D.physicalCoreDomain i
  let Near := ⋃ i, D.nearDisplacementEvent i radius
  let Q := D.retainedNearComplementEvent A B radius
  have hK : MeasurableSet K := MeasurableSet.iUnion fun i ↦
    D.measurableSet_physicalCoreDomain hF hcomplete hu ha i
  have hNear : MeasurableSet Near := MeasurableSet.iUnion fun i ↦
    D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius
  have hQ : MeasurableSet Q :=
    D.measurableSet_retainedNearComplementEvent hF hcomplete hu ha hinj hA hB radius
  have hcover : ((A ×ˢ B) \ Near) ⊆
      (Kᶜ ×ˢ univ) ∪ (univ ×ˢ Kᶜ) ∪ Q := by
    intro p hp
    by_cases hx : p.1 ∈ K
    · by_cases hy : p.2 ∈ K
      · exact Or.inr ⟨⟨⟨hx, hy⟩, hp.1⟩, hp.2⟩
      · exact Or.inl (Or.inr ⟨mem_univ _, hy⟩)
    · exact Or.inl (Or.inl ⟨hx, mem_univ _⟩)
  have hsource : π (Kᶜ ×ˢ univ) = μ Kᶜ := by
    have hh := congrArg (fun η : Measure M ↦ η Kᶜ) hπ.1
    rw [Measure.map_apply measurable_fst hK.compl] at hh
    have he : Prod.fst ⁻¹' Kᶜ = Kᶜ ×ˢ (univ : Set M) := by ext p; simp
    simpa only [he] using hh
  have htarget : π (univ ×ˢ Kᶜ) = ν Kᶜ := by
    have hh := congrArg (fun η : Measure M ↦ η Kᶜ) hπ.2
    rw [Measure.map_apply measurable_snd hK.compl] at hh
    have he : Prod.snd ⁻¹' Kᶜ = (univ : Set M) ×ˢ Kᶜ := by ext p; simp
    simpa only [he] using hh
  have hretained : π Q ≤ C / ENNReal.ofReal (scale * c) :=
    (measure_event_le_scaled_energy_of_gap π hQ
      (fun p ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)
      hc hscale hb).trans (ENNReal.div_le_div_right henergy _)
  have hbad : π ((A ×ˢ B) \ Near) ≤ μ Kᶜ + ν Kᶜ +
      C / ENNReal.ofReal (scale * c) := by
    calc
      _ ≤ π (Kᶜ ×ˢ univ) + π (univ ×ˢ Kᶜ) + π Q :=
        (measure_mono hcover).trans ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl))
      _ ≤ _ := by rw [hsource, htarget]; exact add_le_add le_rfl hretained
  have hπA : ∀ᵐ p ∂π, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (hπ.1.symm ▸ hμA)
  have hπB : ∀ᵐ p ∂π, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (hπ.2.symm ▸ hνB)
  have hrestrict : π.restrict (A ×ˢ B) = π :=
    Measure.restrict_eq_self_of_ae_mem (hπA.and hπB)
  have heq : π ((Near ∩ (A ×ˢ B))ᶜ) = π ((A ×ˢ B) \ Near) := by
    conv_lhs => rw [← hrestrict, Measure.restrict_apply (hNear.inter (hA.prod hB)).compl]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  exact heq.trans_le hbad

/-- The actual iid optimal mean plan has the same non-near bound, for any
measurable selected cost and scale, with its own true physical slack energy. -/
theorem exists_originalIID_fullNonNear_mass_bound
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap radius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hradius : 0 < radius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (n : ℕ), 0 < n →
      ∀ (cost : M → M → ℝ), Measurable (Function.uncurry cost) →
      ∀ (selectionScale scale : ℝ), 0 < scale → ∀ C : ℝ≥0∞,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (scale *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan cost selectionScale ξ
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ≤ C →
      (∫⁻ ξ, (originalIIDOptimalPhysicalPlan cost selectionScale ξ)
        (((⋃ i, D.nearDisplacementEvent i radius) ∩ (A ×ˢ B))ᶜ)
        ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ≤
        μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
          C / ENNReal.ofReal (scale * c) := by
  obtain ⟨c, hc, hbound⟩ := D.exists_coupling_fullNonNear_mass_bound
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hradius hwindow
  refine ⟨c, hc, ?_⟩
  intro n hn cost hcost selectionScale scale hscale C henergy
  letI : NeZero n := ⟨hn.ne'⟩
  let π := originalIIDOptimalMeanPlan μ ν cost selectionScale n
  have hs : π.map Prod.fst = μ :=
    originalIIDOptimalMeanPlan_source μ ν cost hcost selectionScale
  have ht : π.map Prod.snd = ν :=
    originalIIDOptimalMeanPlan_target μ ν cost hcost selectionScale
  haveI : IsProbabilityMeasure (π.map Prod.fst) := hs.symm ▸ inferInstance
  haveI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  have hmeasEnergy : Measurable (fun p : M × M ↦ ENNReal.ofReal (scale *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))) := by
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    exact ((F.measurable_distance_slack hu).const_mul scale).ennreal_ofReal
  have hmeanEnergy : (∫⁻ p, ENNReal.ofReal (scale *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂π) ≤ C := by
    rw [lintegral_originalIIDOptimalMeanPlan μ ν cost hcost selectionScale n _ hmeasEnergy]
    exact henergy
  have hnear : MeasurableSet (⋃ i, D.nearDisplacementEvent i radius) :=
    MeasurableSet.iUnion fun i ↦
      D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius
  have hmass := hbound π ⟨hs, ht⟩ scale hscale C hmeanEnergy
  rw [show π = (((Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν))).bind
      (originalIIDOptimalPhysicalPlan cost selectionScale)) from rfl,
    Measure.bind_apply (hnear.inter (hA.prod hB)).compl
      (measurable_originalIIDOptimalPhysicalPlan cost hcost selectionScale).aemeasurable] at hmass
  exact hmass

end PopulationLocalPressureCore
end OTSelector.Reconstruction
