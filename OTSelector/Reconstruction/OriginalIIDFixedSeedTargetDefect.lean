import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeedTargetVanishing
import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeed
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCrossingTargetDefect
import OTSelector.Reconstruction.OriginalIIDMeanPlanNonNear

/-!
# The actual iid fixed-seed target defect against its original empirical input

The target reference is the same complete second array restricted to the same
original physical seed source. Only real crossings of this fixed set contribute.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal CompactlySupported BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

section Generic
variable {M ι Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

/-- A single actual source-to-target restriction defect is bounded by its true
expected crossing mass, retaining the same rooted compact target test. -/
theorem lintegral_rooted_source_sub_target_restriction_le_expected_crossing
    (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
    (hΓ : Measurable Γ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (hfU : ∀ y ∈ tsupport f, y.1 ∈ U)
    (Ccross : ℝ≥0∞) (hmass : (∫⁻ w, Γ w (physicalSceneCoreCrossing H) ∂Penv) ≤ Ccross) :
    (∫⁻ w, ∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan ((Γ w).restrict (univ ×ˢ H)) coord u N z|
      ∂cavityRootMeasure volume D N ∂Penv) ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U * Ccross := by
  let G := ENNReal.ofReal ‖f.toBoundedContinuousFunction‖
  have hw (w : Ω) : (∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan ((Γ w).restrict (univ ×ˢ H)) coord u N z|
      ∂cavityRootMeasure volume D N) ≤ G * volume U * Γ w (physicalSceneCoreCrossing H) := by
    calc
      _ ≤ ∫⁻ z, G * physicalSceneRootedPlan ((Γ w).restrict (physicalSceneCoreCrossing H))
          coord u N z {e | e.2.1 ∈ U} ∂cavityRootMeasure volume D N :=
        lintegral_mono fun z ↦ ofReal_abs_rooted_source_restrict_sub_target_restrict_le_crossing
          (Γ w) H hH coord hcoord u hu N hN z f U hU hfU
      _ = G * ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (physicalSceneCoreCrossing H))
          coord u N z {e | e.2.1 ∈ U} ∂cavityRootMeasure volume D N :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ G * (volume U * Γ w (physicalSceneCoreCrossing H)) := by
        apply mul_le_mul_right
        simpa only [Measure.restrict_apply_univ] using
          lintegral_physicalSceneRootedPlan_targetWindow_le
            ((Γ w).restrict (physicalSceneCoreCrossing H)) coord hcoord u hu N hN D U hU
      _ = _ := mul_assoc _ _ _ |>.symm
  have hcross : Measurable (fun w ↦ Γ w (physicalSceneCoreCrossing H)) :=
    (Measure.measurable_coe (measurableSet_physicalSceneCoreCrossing hH)).comp hΓ
  calc
    _ ≤ ∫⁻ w, (G * volume U) * Γ w (physicalSceneCoreCrossing H) ∂Penv := lintegral_mono hw
    _ = (G * volume U) * ∫⁻ w, Γ w (physicalSceneCoreCrossing H) ∂Penv :=
      lintegral_const_mul _ hcross
    _ ≤ _ := mul_le_mul_right hmass _

/-- Physical target restriction reads exactly the unchanged second sample word,
with the original empirical normalization and the literal mask `H`. -/
theorem integral_originalIID_rooted_target_restriction_eq_literal_target
    {n : ℕ} [NeZero n] (cost : M → M → ℝ) (selectionScale : ℝ)
    (ξ : (Fin n → M) × (Fin n → M)) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 ≤ N) (z : ι → ℝ)
    (f : C_c((ι → ℝ) × ℝ, ℝ)) :
    (∫ e, f e.2 ∂physicalSceneRootedPlan
      ((originalIIDOptimalPhysicalPlan cost selectionScale ξ).restrict (univ ×ˢ H))
      coord u N z) =
      (N / n) * ∑ i, H.indicator (fun y ↦ f (coord y - z, u y)) (ξ.2 i) := by
  let Γ := originalIIDOptimalPhysicalPlan cost selectionScale ξ
  let endpoint := fun y : M ↦ (coord y - z, u y)
  have he : Measurable endpoint := (hcoord.sub measurable_const).prodMk hu
  have hm := (physicalSceneRootedPlan_marginals (Γ.restrict (univ ×ˢ H))
    coord hcoord u hu N z).2
  rw [snd_actual_target_restriction Γ H hH,
    show Γ.snd = empiricalMeasure ξ.2 from
      originalIIDOptimalPhysicalPlan_target cost selectionScale ξ] at hm
  have hread := integral_map
    (μ := physicalSceneRootedPlan (Γ.restrict (univ ×ˢ H)) coord u N z)
    (f := fun y ↦ f y) measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
  change (∫ y, f y ∂(physicalSceneRootedPlan (Γ.restrict (univ ×ˢ H)) coord u N z).snd) = _ at hread
  calc
    _ = ∫ y, f y ∂(physicalSceneRootedPlan (Γ.restrict (univ ×ˢ H)) coord u N z).snd := hread.symm
    _ = N * ∫ y, f (endpoint y) ∂(empiricalMeasure ξ.2).restrict H := by
      rw [hm, integral_smul_measure]
      simp only [ENNReal.toReal_ofReal hN, smul_eq_mul]
      exact congrArg (fun x : ℝ ↦ N * x)
        (integral_map he.aemeasurable f.continuous.aestronglyMeasurable)
    _ = (N / n) * ∑ i, H.indicator (fun y ↦ f (endpoint y)) (ξ.2 i) := by
      rw [← integral_indicator hH]
      have hh := integral_empiricalMeasure ξ.2
        ((f.continuous.measurable.comp he).indicator hH).stronglyMeasurable
      calc
        _ = N * ((n : ℝ)⁻¹ * ∑ i, H.indicator (fun y ↦ f (endpoint y)) (ξ.2 i)) :=
          congrArg (fun x : ℝ ↦ N * x) hh
        _ = _ := by ring
end Generic

section Finsler
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
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

/-- The same actual iid plan restricted to the original full seed source has
its compact target-test defect against the literal original target word paid
only by the two actual core complements and true physical slack energy. -/
theorem exists_originalIID_fixed_seed_literal_target_test_defect_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (j n : ℕ) (cost : M → M → ℝ),
      Measurable (Function.uncurry cost) → ∀ (selectionScale spatialScale N : ℝ),
      0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      MeasurableSet U → ∀ (f : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ)),
      (∀ y ∈ tsupport f, y.1 ∈ U) → ∀ C : ℝ≥0∞,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan cost selectionScale ξ
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C →
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      (∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
        |(∫ e, f e.2 ∂physicalSceneRootedPlan
          ((originalIIDOptimalPhysicalPlan cost selectionScale ξ).restrict (H ×ˢ univ))
          coord u N z) - (N / (n + 1 : ℕ)) *
            ∑ i, H.indicator (fun y ↦ f (coord y - z, u y)) (ξ.2 i)|
        ∂cavityRootMeasure volume rootDomain N
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤
        ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U *
          (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
            C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hmass⟩ := D.exists_originalIID_fullNonNear_mass_bound
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist
    (show (0 : ℝ) < 1 by norm_num) hwindow
  refine ⟨c, hc, ?_⟩
  intro j n cost hcost selectionScale spatialScale N hsp hN rootDomain U hU f hfU C henergy
  let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  let Γ := originalIIDOptimalPhysicalPlan (n := n + 1) cost selectionScale
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj j
  have hcoord : Measurable coord := measurable_physicalSceneOriginalSeedScaledPosition
    hF hcomplete hu ha hinj j spatialScale
  have hΓ : Measurable Γ := measurable_originalIIDOptimalPhysicalPlan cost hcost selectionScale
  have hcover : physicalSceneCoreCrossing H ⊆
      (((⋃ i, D.nearDisplacementEvent i 1) ∩ (A ×ˢ B))ᶜ) := by
    intro p hp hn
    have hc := D.fixed_seed_crossing_subset_global_nonNear j A B 1 ⟨hp, hn.2⟩
    exact hc.2 hn.1
  have hm : (∫⁻ ξ, Γ ξ (physicalSceneCoreCrossing H) ∂Penv) ≤
      μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
        C / ENNReal.ofReal (spatialScale ^ 2 * c) :=
    (lintegral_mono (fun ξ ↦ measure_mono hcover)).trans
      (hmass (n + 1) (Nat.succ_pos n) cost hcost selectionScale
        (spatialScale ^ 2) (sq_pos_of_pos hsp) C henergy)
  have hb := lintegral_rooted_source_sub_target_restriction_le_expected_crossing
    Penv Γ hΓ H hH coord hcoord u hu.continuous.measurable N hN rootDomain U hU f hfU _ hm
  calc
    _ = ∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
        |(∫ e, f e.2 ∂physicalSceneRootedPlan ((Γ ξ).restrict (H ×ˢ univ)) coord u N z) -
          ∫ e, f e.2 ∂physicalSceneRootedPlan ((Γ ξ).restrict (univ ×ˢ H)) coord u N z|
        ∂cavityRootMeasure volume rootDomain N ∂Penv := by
      apply lintegral_congr
      intro ξ
      apply lintegral_congr
      intro z
      rw [integral_originalIID_rooted_target_restriction_eq_literal_target
        cost selectionScale ξ H hH coord hcoord u hu.continuous.measurable N hN.le z f]
    _ ≤ _ := hb

/-- Two actual iid optimizers retain the same complete empirical target before
masking by the same original full seed, so only their true crossing masses remain. -/
theorem exists_originalIID_fixed_seed_target_test_defect_bound
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ (j n : ℕ) (costPlus costMinus : M → M → ℝ),
      Measurable (Function.uncurry costPlus) → Measurable (Function.uncurry costMinus) →
      ∀ (selectionPlus selectionMinus spatialScale N : ℝ), 0 < spatialScale → 0 < N →
      ∀ (rootDomain U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
      MeasurableSet U → ∀ (f : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ)),
      (∀ y ∈ tsupport f, y.1 ∈ U) → ∀ C : ℝ≥0∞,
      let Penv := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
      let Γplus := originalIIDOptimalPhysicalPlan (n := n + 1) costPlus selectionPlus
      let Γminus := originalIIDOptimalPhysicalPlan (n := n + 1) costMinus selectionMinus
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γplus ξ ∂Penv) ≤ C →
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γminus ξ ∂Penv) ≤ C →
      let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
      (∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
        |(∫ e, f e.2 ∂physicalSceneRootedPlan ((Γplus ξ).restrict (H ×ˢ univ)) coord u N z) -
          ∫ e, f e.2 ∂physicalSceneRootedPlan ((Γminus ξ).restrict (H ×ˢ univ)) coord u N z|
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
        2 * ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U *
          (μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
            C / ENNReal.ofReal (spatialScale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hmass⟩ := D.exists_originalIID_fullNonNear_mass_bound
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist
    (show (0 : ℝ) < 1 by norm_num) hwindow
  refine ⟨c, hc, ?_⟩
  intro j n costPlus costMinus hp hm selectionPlus selectionMinus spatialScale N hsp hN
    rootDomain U hU f hfU C Penv Γplus Γminus hEp hEm
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj j
  have hcoord : Measurable coord := measurable_physicalSceneOriginalSeedScaledPosition
    hF hcomplete hu ha hinj j spatialScale
  have hplus : Measurable Γplus := measurable_originalIIDOptimalPhysicalPlan costPlus hp selectionPlus
  have hminus : Measurable Γminus := measurable_originalIIDOptimalPhysicalPlan costMinus hm selectionMinus
  have htarget : ∀ᵐ ξ ∂Penv, (Γplus ξ).snd = (Γminus ξ).snd :=
    Eventually.of_forall fun ξ ↦
      (originalIIDOptimalPhysicalPlan_target costPlus selectionPlus ξ).trans
        (originalIIDOptimalPhysicalPlan_target costMinus selectionMinus ξ).symm
  have hcover : physicalSceneCoreCrossing H ⊆
      (((⋃ i, D.nearDisplacementEvent i 1) ∩ (A ×ˢ B))ᶜ) := by
    intro p hp hn
    have hc := D.fixed_seed_crossing_subset_global_nonNear j A B 1 ⟨hp, hn.2⟩
    exact hc.2 hn.1
  let budget := μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ +
    C / ENNReal.ofReal (spatialScale ^ 2 * c)
  have hcp : (∫⁻ ξ, Γplus ξ (physicalSceneCoreCrossing H) ∂Penv) ≤ budget :=
    (lintegral_mono (fun ξ ↦ measure_mono hcover)).trans
      (hmass (n + 1) (Nat.succ_pos n) costPlus hp selectionPlus
        (spatialScale ^ 2) (sq_pos_of_pos hsp) C hEp)
  have hcm : (∫⁻ ξ, Γminus ξ (physicalSceneCoreCrossing H) ∂Penv) ≤ budget :=
    (lintegral_mono (fun ξ ↦ measure_mono hcover)).trans
      (hmass (n + 1) (Nat.succ_pos n) costMinus hm selectionMinus
        (spatialScale ^ 2) (sq_pos_of_pos hsp) C hEm)
  have hcross : (∫⁻ ξ, Γplus ξ (physicalSceneCoreCrossing H) +
      Γminus ξ (physicalSceneCoreCrossing H) ∂Penv) ≤ budget + budget := by
    exact (lintegral_add_left
      ((Measure.measurable_coe (measurableSet_physicalSceneCoreCrossing hH)).comp hplus)
      (fun ξ ↦ Γminus ξ (physicalSceneCoreCrossing H))).trans_le (add_le_add hcp hcm)
  exact (lintegral_rooted_source_restricted_target_tests_le_expected_crossing
    Penv Γplus Γminus hplus hminus htarget H hH coord hcoord u hu.continuous.measurable
    N hN rootDomain U hU f hfU (budget + budget) hcross).trans_eq (by ring)

end PopulationLocalPressureCore
/-- Auxiliary original cores make the actual fixed-seed target marginal agree
with its literal original target-cloud restriction. Only an eventual true energy
budget is needed; the mask, optimizer and coordinate frame stay unchanged. -/
theorem tendsto_originalIID_fixed_seed_literal_target_test_defect_zero
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (j : ℕ)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (selectionScale spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (rootMass : ℕ → ℝ) (hN : ∀ n, 0 < rootMass n)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C)
    (f : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
    Tendsto (fun n ↦ ∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan
        ((originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z) - (rootMass n / (n + 1 : ℕ)) *
          ∑ i, H.indicator (fun y ↦ f (coord n y - z, u y)) (ξ.2 i)|
      ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
      ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) atTop (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let U := physicalSceneTestSpatialWindow f
  have hU := isCompact_physicalSceneTestSpatialWindow f
  let coeff := ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U
  have hcoeff : coeff ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU.measure_ne_top
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
  let defect := fun n ↦ ∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
    |(∫ e, f e.2 ∂physicalSceneRootedPlan
      ((originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ).restrict (H ×ˢ univ))
      (coord n) u (rootMass n) z) - (rootMass n / (n + 1 : ℕ)) *
        ∑ i, H.indicator (fun y ↦ f (coord n y - z, u y)) (ξ.2 i)|
    ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
    ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp henergy
  let mass := fun n ↦ if N₀ ≤ n then defect n else 0
  have hvanish : Tendsto mass atTop (𝓝 0) := by
    apply tendsto_zero_of_auxiliary_small_mass_energy_bounds mass
      (fun n ↦ spatialScale n ^ 2) hscale coeff C hcoeff hC
    intro δ hδ
    let d : ℝ≥0∞ := (δ : ℝ≥0∞) / 4
    have hd : 0 < d := ENNReal.div_pos (by exact_mod_cast hδ.ne') (by norm_num)
    obtain ⟨D, hscreen, hμtail, hνtail⟩ :=
      exists_original_small_clock_screen_population_core_of_face hcore hrecovery
        hF hcomplete hu ha hinj hκ hbalance hA hB hμ hν hreg hμreg hface
        (half_pos hgap) hd.ne' hd.ne'
    have htails : μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤
        (δ : ℝ≥0∞) := by
      apply (add_le_add hμtail hνtail).trans_eq
      calc
        _ = 4 * ((δ : ℝ≥0∞) / 4) := by dsimp only [d]; ring
        _ = _ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
    obtain ⟨c, hc, hb⟩ := D.exists_originalIID_fixed_seed_literal_target_test_defect_bound
      hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμ hν hgap hdist hscreen
    refine ⟨c, hc, ?_⟩
    intro n
    by_cases hn : N₀ ≤ n
    · have hbN := hb j n (cost n) (hcost n) (selectionScale n) (spatialScale n)
        (rootMass n) (hsp n) (hN n) (rootDomain n) U hU.measurableSet f
        (fun y hy ↦ mem_image_of_mem Prod.fst hy) C (hN₀ n hn)
      change (if N₀ ≤ n then defect n else 0) ≤ _
      rw [ite_eq_left hn]
      exact hbN.trans (mul_le_mul_right (add_le_add htails le_rfl) _)
    · simp only [mass, ite_eq_right hn]
      exact zero_le
  have heq : mass =ᶠ[atTop] defect := by
    filter_upwards [eventually_ge_atTop N₀] with n hn
    simp only [mass, ite_eq_left hn]
  exact hvanish.congr' heq

/-- The two actual iid optimizer target tests agree asymptotically in the same
full original seed scene, using auxiliary original cores and one eventual true
slack-energy budget for each optimizer. -/
theorem tendsto_originalIID_fixed_seed_target_test_defect_zero
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (j : ℕ)
    (costPlus costMinus : ℕ → M → M → ℝ)
    (hcostPlus : ∀ n, Measurable (Function.uncurry (costPlus n)))
    (hcostMinus : ∀ n, Measurable (Function.uncurry (costMinus n)))
    (selectionPlus selectionMinus spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (rootMass : ℕ → ℝ) (hN : ∀ n, 0 < rootMass n)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan (costPlus n) (selectionPlus n) ξ
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C) ∧
      ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan (costMinus n) (selectionMinus n) ξ
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C))
    (f : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ, ℝ)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
    Tendsto (fun n ↦ ∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
      |(∫ e, f e.2 ∂physicalSceneRootedPlan
        ((originalIIDOptimalPhysicalPlan (costPlus n) (selectionPlus n) ξ).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z) -
        ∫ e, f e.2 ∂physicalSceneRootedPlan
          ((originalIIDOptimalPhysicalPlan (costMinus n) (selectionMinus n) ξ).restrict (H ×ˢ univ))
          (coord n) u (rootMass n) z|
      ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
      ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) atTop (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let U := physicalSceneTestSpatialWindow f
  have hU := isCompact_physicalSceneTestSpatialWindow f
  let coeff := 2 * ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * volume U
  have hcoeff : coeff ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hU.measure_ne_top
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)
  let defect := fun n ↦ ∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
    |(∫ e, f e.2 ∂physicalSceneRootedPlan
      ((originalIIDOptimalPhysicalPlan (costPlus n) (selectionPlus n) ξ).restrict (H ×ˢ univ))
      (coord n) u (rootMass n) z) -
      ∫ e, f e.2 ∂physicalSceneRootedPlan
        ((originalIIDOptimalPhysicalPlan (costMinus n) (selectionMinus n) ξ).restrict (H ×ˢ univ))
        (coord n) u (rootMass n) z|
    ∂cavityRootMeasure volume (rootDomain n) (rootMass n)
    ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp henergy
  let mass := fun n ↦ if N₀ ≤ n then defect n else 0
  have hvanish : Tendsto mass atTop (𝓝 0) := by
    apply tendsto_zero_of_auxiliary_small_mass_energy_bounds mass
      (fun n ↦ spatialScale n ^ 2) hscale coeff C hcoeff hC
    intro δ hδ
    let d : ℝ≥0∞ := (δ : ℝ≥0∞) / 4
    have hd : 0 < d := ENNReal.div_pos (by exact_mod_cast hδ.ne') (by norm_num)
    obtain ⟨D, hscreen, hμtail, hνtail⟩ :=
      exists_original_small_clock_screen_population_core_of_face hcore hrecovery
        hF hcomplete hu ha hinj hκ hbalance hA hB hμ hν hreg hμreg hface
        (half_pos hgap) hd.ne' hd.ne'
    have htails : μ (⋃ i, D.physicalCoreDomain i)ᶜ + ν (⋃ i, D.physicalCoreDomain i)ᶜ ≤
        (δ : ℝ≥0∞) := by
      apply (add_le_add hμtail hνtail).trans_eq
      calc
        _ = 4 * ((δ : ℝ≥0∞) / 4) := by dsimp only [d]; ring
        _ = _ := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
    obtain ⟨c, hc, hb⟩ := D.exists_originalIID_fixed_seed_target_test_defect_bound
      hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμ hν hgap hdist hscreen
    refine ⟨c, hc, ?_⟩
    intro n
    by_cases hn : N₀ ≤ n
    · have hbN := hb j n (costPlus n) (costMinus n) (hcostPlus n) (hcostMinus n)
        (selectionPlus n) (selectionMinus n) (spatialScale n) (rootMass n) (hsp n) (hN n)
        (rootDomain n) U hU.measurableSet f (fun y hy ↦ mem_image_of_mem Prod.fst hy)
        C (hN₀ n hn).1 (hN₀ n hn).2
      change (if N₀ ≤ n then defect n else 0) ≤ _
      rw [ite_eq_left hn]
      exact hbN.trans (mul_le_mul_right (add_le_add htails le_rfl) _)
    · simp only [mass, ite_eq_right hn]
      exact zero_le
  have heq : mass =ᶠ[atTop] defect := by
    filter_upwards [eventually_ge_atTop N₀] with n hn
    simp only [mass, ite_eq_left hn]
  exact hvanish.congr' heq

end Finsler
end OTSelector.Reconstruction
