import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedNearEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedFiniteCover
import OTSelector.Reconstruction.OriginalIIDMeanPlanNonNear

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
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
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

/-- Arbitrary measurable physical plans with the unchanged populations as their
actual mean marginals have both full rooted tails in the same original seed frame. -/
theorem exists_mean_coupling_fixed_seed_both_full_longTail_bounds
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0, ∀ (j : ℕ) (Ω : Type*) [MeasurableSpace Ω]
      (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)],
      Measurable Γ → Vlasov.IsCoupling (Penv.bind Γ) μ ν →
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      volume rootDomain = ENNReal.ofReal N → MeasurableSet U → volume U ≠ ⊤ →
      ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ w ∂Penv) ≤ C →
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      let bound := (D.haar.continuous.count : ℝ≥0∞) *
        ((volume U * (C / ENNReal.ofReal q)) / threshold) +
        volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
          C / ENNReal.ofReal (spatialScale ^ 2 * c))
      ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ))
        coord u N z (physicalSceneLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤ bound) ∧
      ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ))
        coord u N z (physicalSceneTargetLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤ bound) := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, radius, hradius, hnear⟩ :=
    D.exists_uniform_fixed_seed_near_expected_tails hF hcomplete hu ha hinj
  obtain ⟨c, hc, hmass⟩ := D.exists_coupling_fullNonNear_mass_bound
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hradius hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro j Ω _ Penv Γ _ hΓ hπ spatialScale N hsp hN rootDomain U hD hU hUf
    threshold ht0 htt C henergy
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
  let Near := ⋃ i, D.nearDisplacementEvent i radius
  let Q := (Near ∩ (A ×ˢ B))ᶜ
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  have hcoord : Measurable coord := measurable_physicalSceneOriginalSeedScaledPosition
    hF hcomplete hu ha hinj j spatialScale
  have hNear : MeasurableSet Near := MeasurableSet.iUnion fun i ↦
    D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius
  have hQ : MeasurableSet Q := (hNear.inter (hA.prod hB)).compl
  have hnmeas (i : Fin D.haar.continuous.count) :
      MeasurableSet (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)) :=
    (D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius).inter
      (hH.prod MeasurableSet.univ)
  have : IsFiniteMeasure ((Penv.bind Γ).map Prod.fst) := hπ.1.symm ▸ inferInstance
  have : IsFiniteMeasure (Penv.bind Γ) :=
    Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable
  have hmeasEnergy : Measurable (fun p : M × M ↦ ENNReal.ofReal (spatialScale ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))) := by
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    exact ((F.measurable_distance_slack hu).const_mul _).ennreal_ofReal
  have hmeanEnergy : (∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Penv.bind Γ) ≤ C := by
    rw [Measure.lintegral_bind hΓ.aemeasurable hmeasEnergy.aemeasurable]
    exact henergy
  have hm := hmass (Penv.bind Γ) hπ (spatialScale ^ 2) (sq_pos_of_pos hsp) C hmeanEnergy
  rw [Measure.bind_apply hQ hΓ.aemeasurable] at hm
  have hcov : H ×ˢ (univ : Set M) ⊆
      (⋃ i, D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)) ∪ (Q ∩ (H ×ˢ univ)) := by
    intro p hp
    by_cases hn : p ∈ Near
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hn
      exact Or.inl (mem_iUnion.mpr ⟨i, hi, hp⟩)
    · exact Or.inr ⟨fun h ↦ hn h.1, hp⟩
  have hcoverS := lintegral_physicalSceneRootedPlan_finite_event_cover_le Penv Γ hΓ
    coord hcoord u hu.continuous.measurable N hN rootDomain hD hcov hnmeas
    (measurableSet_physicalSceneLongEdgeWindow hU threshold)
    (hU.preimage measurable_fst.fst) (fun _ hp ↦ hp.1)
  have hcoverT := lintegral_physicalSceneRootedPlan_finite_event_cover_le Penv Γ hΓ
    coord hcoord u hu.continuous.measurable N hN rootDomain hD hcov hnmeas
    (measurableSet_physicalSceneTargetLongEdgeWindow hU threshold)
    (hU.preimage measurable_snd.fst) (fun _ hp ↦ hp.1)
  have hn (i : Fin D.haar.continuous.count) := hnear j i _ Penv Γ spatialScale N hN
    rootDomain U hU hUf threshold ht0 htt C henergy
  have hbadS := lintegral_event_restricted_rooted_sourceWindow_expected_le_of_mass Penv Γ
    coord hcoord u hu.continuous.measurable N hN rootDomain U hU hUf Q H _ hm
  have hbadT := lintegral_event_restricted_rooted_targetWindow_expected_le_of_mass Penv Γ
    coord hcoord u hu.continuous.measurable N hN rootDomain U hU hUf Q H _ hm
  have hsumS := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (hn i).1)
  have hsumT := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (hn i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumS hsumT
  exact ⟨hcoverS.trans (add_le_add hsumS hbadS), hcoverT.trans (add_le_add hsumT hbadT)⟩

/-- The actual growing two-colour iid optimizer has both full fixed-seed rooted tails
for every measurable cost and selection scale, using only its true scaled slack budget. -/
theorem exists_originalIID_fixed_seed_both_full_longTail_bounds
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ q > 0, ∃ c > 0, ∀ (j n : ℕ)
      (cost : M → M → ℝ) (_hcost : Measurable (Function.uncurry cost)) (selectionScale : ℝ),
      let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
      let Γ := originalIIDOptimalPhysicalPlan (n := n + 1) cost selectionScale
      ∀ (spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      volume rootDomain = ENNReal.ofReal N → MeasurableSet U → volume U ≠ ⊤ →
      ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ → ∀ C : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ w ∂Penv) ≤ C →
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      let bound := (D.haar.continuous.count : ℝ≥0∞) *
        ((volume U * (C / ENNReal.ofReal q)) / threshold) +
        volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
          C / ENNReal.ofReal (spatialScale ^ 2 * c))
      ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ))
        coord u N z (physicalSceneLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤ bound) ∧
      ((∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ))
        coord u N z (physicalSceneTargetLongEdgeWindow U threshold)
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤ bound) := by
  obtain ⟨q, hq, c, hc, hbound⟩ :=
    D.exists_mean_coupling_fixed_seed_both_full_longTail_bounds
      hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hwindow
  refine ⟨q, hq, c, hc, ?_⟩
  intro j n cost hcost selectionScale
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let Γ := originalIIDOptimalPhysicalPlan (n := n + 1) cost selectionScale
  have hΓ : Measurable Γ := measurable_originalIIDOptimalPhysicalPlan cost hcost selectionScale
  have hπ : Vlasov.IsCoupling (Penv.bind Γ) μ ν :=
    ⟨originalIIDOptimalMeanPlan_source (n := n + 1) μ ν cost hcost selectionScale,
      originalIIDOptimalMeanPlan_target (n := n + 1) μ ν cost hcost selectionScale⟩
  exact hbound j _ Penv Γ hΓ hπ

end PopulationLocalPressureCore
end OTSelector.Reconstruction
